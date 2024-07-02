/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arpa/inet.h>
#include <host_spdm_rsp_ifc.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>
#include <utils_def.h>

#define PCI_DOE_VENDOR_ID_PCISIG		0x1

#define PCI_DOE_DATA_OBJ_TYPE_SPDM		0x1
#define PCI_DOE_DATA_OBJ_TYPE_SECURED_SPDM	0x2

/* SPDM max transfer size + DOE header */
#define PCI_DOE_MAX_SIZE_IN_BYTE		(4096 + 8)

/* DOE header*/
typedef struct {
	uint16_t vendor_id;
	uint8_t data_obj_type;
	uint8_t reserved;
	uint32_t length;
} pci_doe_header_t;

/* static int spdm_rsp_fds[SPDM_RSP_EMU_MAX]; */
static int g_sock_fd = -1;

int host_spdm_rsp_init(const char *host_addr, uint32_t port, int *spdm_rsp_id)
{
	int fd, rc;
	struct sockaddr_in serv_addr;

	fd = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
	if (fd == -1) {
		return -1;
	}

	memset(&serv_addr, 0, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	serv_addr.sin_port = htons(port);
	serv_addr.sin_addr.s_addr = inet_addr(host_addr);

	rc = connect(fd, (struct sockaddr *)&serv_addr, sizeof(serv_addr));
	if (rc != 0) {
		return -1;
		close(fd);
	}

	g_sock_fd = fd;
	*spdm_rsp_id = fd;

	return 0;
}

int host_spdm_rsp_deinit(int spdm_rsp_id)
{
	if ((g_sock_fd == -1) || (spdm_rsp_id != g_sock_fd)) {
		return -1;
	}

	/* Send shutdown command and close fd */

	close(g_sock_fd);
	g_sock_fd = -1;

	return 0;
}

static int send_bytes(int sock_fd, const uint8_t *src, size_t len)
{
	int rc;
	size_t sent_bytes;

	sent_bytes = 0;
	while (sent_bytes < len) {
		rc = send(sock_fd, src + sent_bytes, len - sent_bytes, 0);
		if (rc == -1) {
			return -1;
		}
		sent_bytes += rc;
	}

	return 0;
}

static int send_data32(int sock_fd, uint32_t data)
{
	data = htonl(data);
	return send_bytes(sock_fd, (uint8_t *)&data, sizeof(uint32_t));
}

static int recv_bytes(int sock_fd, uint8_t *dst, size_t len)
{
	int rc;
	size_t rcvd_bytes;

	rcvd_bytes = 0;
	while (rcvd_bytes < len) {
		rc = recv(sock_fd, dst + rcvd_bytes, len - rcvd_bytes, 0);
		if (rc == -1) {
			return -1;
		}
		rcvd_bytes += rc;
	}

	return 0;
}

static int recv_data32(int sock_fd, uint32_t *data)
{
	int rc;

	rc = recv_bytes(sock_fd, (uint8_t *)data, sizeof(uint32_t));
	if (rc != 0) {
		return -1;
	}
	*data = ntohl(*data);
	return 0;
}


/* host_doe_header_create */
static int host_doe_header_create(pci_doe_header_t *doe_hdr, size_t req_sz,
				  bool is_sspdm)
{
	size_t payload_size;

	payload_size = req_sz + sizeof(pci_doe_header_t);

	/* todo: Check min transfer size */
	if (payload_size > PCI_DOE_MAX_SIZE_IN_BYTE) {
		return -1;
	}

	doe_hdr->vendor_id = PCI_DOE_VENDOR_ID_PCISIG;
	if (!is_sspdm) {
		doe_hdr->data_obj_type = PCI_DOE_DATA_OBJ_TYPE_SPDM;
	} else {
		doe_hdr->data_obj_type = PCI_DOE_DATA_OBJ_TYPE_SECURED_SPDM;
	}
	doe_hdr->reserved = 0;
	doe_hdr->length = payload_size / sizeof(uint32_t);

	return 0;
}

/* host_doe_header_validate */
static int host_doe_header_validate(pci_doe_header_t *doe_hdr,
				    size_t expected_payload_sz, bool is_sspdm)
{
	size_t rcvd_payload_sz;

	if (doe_hdr->vendor_id != PCI_DOE_VENDOR_ID_PCISIG) {
		return -1;
	}

	if ((!is_sspdm && doe_hdr->data_obj_type !=
	     PCI_DOE_DATA_OBJ_TYPE_SPDM) ||
	    (is_sspdm && doe_hdr->data_obj_type !=
	     PCI_DOE_DATA_OBJ_TYPE_SECURED_SPDM)) {
		return -1;
	}

	rcvd_payload_sz = doe_hdr->length * sizeof(uint32_t);
	if (rcvd_payload_sz != expected_payload_sz ||
	    rcvd_payload_sz > PCI_DOE_MAX_SIZE_IN_BYTE) {
		return -1;
	}

	return 0;
}

/* host_send_doe_spdm */
static int host_send_doe_spdm_req(int spdm_rsp_id, const void *req_buf,
				  size_t req_sz, bool is_sspdm)
{
	int rc;
	pci_doe_header_t doe_hdr = { 0 };

	/* This shouldn't overflow the request buffer */
	req_sz = round_up(req_sz, 4);
	if (req_sz > 4096U) {
		return -1;
	}

	/* Create DOE header */
	rc = host_doe_header_create(&doe_hdr, req_sz, is_sspdm);
	if (rc == -1) {
		return -1;
	}

	/* Send command SOCKET_SPDM_COMMAND_NORMAL */
	rc = send_data32(spdm_rsp_id, SOCKET_SPDM_COMMAND_NORMAL);
	if (rc != 0) {
		return -1;
	}

	/* Send transport as SOCKET_TRANSPORT_TYPE_PCI_DOE */
	rc = send_data32(spdm_rsp_id, SOCKET_TRANSPORT_TYPE_PCI_DOE);
	if (rc != 0) {
		return -1;
	}

	/* Send payload size */
	rc = send_data32(spdm_rsp_id, (uint32_t)(doe_hdr.length *
						 sizeof(uint32_t)));
	if (rc != 0) {
		return -1;
	}

	/* Send payload header (DOE header) */
	rc = send_bytes(spdm_rsp_id, (const uint8_t *)&doe_hdr,
			sizeof(pci_doe_header_t));
	if (rc != 0) {
		return -1;
	}

	/* Send payload */
	rc = send_bytes(spdm_rsp_id, req_buf, req_sz);

	return rc;
}

/* host_recv_doe_spdm */
static int host_recv_doe_spdm_rsp(int spdm_rsp_id, void *rsp_buf,
				  size_t *rsp_sz, bool is_sspdm)
{
	int rc;
	uint32_t command;
	uint32_t transport;
	uint32_t payload_sz;
	pci_doe_header_t doe_hdr = { 0 };

	/* Read command and check if its COMMAND_NORMAL */
	rc = recv_data32(spdm_rsp_id, &command);
	if ((rc != 0) || (command != SOCKET_SPDM_COMMAND_NORMAL)) {
		return -1;
	}

	/* Read transport and check its SOCKET_TRANSPORT_TYPE_PCI_DOE */
	rc = recv_data32(spdm_rsp_id, &transport);
	if ((rc != 0) || (transport != SOCKET_TRANSPORT_TYPE_PCI_DOE)) {
		return -1;
	}

	/* Read total payload size */
	rc = recv_data32(spdm_rsp_id, &payload_sz);
	if (rc != 0) {
		return -1;
	}

	/* Read payload header (DOE header) */
	rc = recv_bytes(spdm_rsp_id, (uint8_t *)&doe_hdr,
			sizeof(pci_doe_header_t));
	if (rc != 0) {
		return -1;
	}

	/* Validate DOE header */
	rc = host_doe_header_validate(&doe_hdr, payload_sz, is_sspdm);
	if (rc != 0) {
		return -1;
	}

	/* Read payload */
	*rsp_sz = payload_sz - sizeof(pci_doe_header_t);
	rc = recv_bytes(spdm_rsp_id, (uint8_t *)rsp_buf, *rsp_sz);

	return rc;
}

/* Send SPDM request and receive response */
int host_spdm_rsp_communicate(int spdm_rsp_id, void *req_buf, size_t req_sz,
			      void *rsp_buf, size_t *rsp_sz, bool is_sspdm)
{
	int rc;

	if ((g_sock_fd == -1) || (spdm_rsp_id != g_sock_fd)) {
		return -1;
	}

	rc = host_send_doe_spdm_req(spdm_rsp_id, req_buf, req_sz, is_sspdm);
	if (rc != 0) {
		return -1;
	}

	rc = host_recv_doe_spdm_rsp(spdm_rsp_id, rsp_buf, rsp_sz, is_sspdm);

	return rc;
}
