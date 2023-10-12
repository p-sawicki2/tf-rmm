/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_TESTS_BASE
#define S2TT_TESTS_BASE

void s2tte_create_unassigned_empty_tc1(void);

void s2tte_create_unassigned_ram_tc1(void);

void s2tte_create_unassigned_ns_tc1(void);

void s2tte_create_unassigned_destroyed_tc1(void);

void s2tte_create_assigned_empty_tc1(void);
void s2tte_create_assigned_empty_tc2(void);
void s2tte_create_assigned_empty_tc3(void);
void s2tte_create_assigned_empty_tc4(void);

void s2tte_create_assigned_ram_tc1(void);
void s2tte_create_assigned_ram_tc2(void);
void s2tte_create_assigned_ram_tc3(void);
void s2tte_create_assigned_ram_tc4(void);

void s2tte_create_assigned_ns_tc1(void);
void s2tte_create_assigned_ns_tc2(void);
void s2tte_create_assigned_ns_tc3(void);
void s2tte_create_assigned_ns_tc4(void);

void s2tte_create_assigned_destroyed_tc1(void);
void s2tte_create_assigned_destroyed_tc2(void);
void s2tte_create_assigned_destroyed_tc3(void);
void s2tte_create_assigned_destroyed_tc4(void);

void s2tte_create_assigned_unchanged_tc1(void);
void s2tte_create_assigned_unchanged_tc2(void);
void s2tte_create_assigned_unchanged_tc3(void);
void s2tte_create_assigned_unchanged_tc4(void);
void s2tte_create_assigned_unchanged_tc5(void);

void s2tte_create_table_tc1(void);
void s2tte_create_table_tc2(void);
void s2tte_create_table_tc3(void);
void s2tte_create_table_tc4(void);

void host_ns_s2tte_is_valid_tc1(void);
void host_ns_s2tte_is_valid_tc2(void);
void host_ns_s2tte_is_valid_tc3(void);
void host_ns_s2tte_is_valid_tc4(void);

void host_ns_s2tte_tc1(void);

void host_ns_s2tte_tc2(void);

void host_ns_s2tte_tc3(void);

void s2tte_has_ripas_tc1(void);
void s2tte_has_ripas_tc2(void);
void s2tte_has_ripas_tc3(void);
void s2tte_has_ripas_tc4(void);

void s2tte_is_unassigned_tc1(void);

void s2tte_is_unassigned_empty_tc1(void);

void s2tte_is_unassigned_ram_tc1(void);

void s2tte_is_unassigned_ns_tc1(void);

void s2tte_is_unassigned_destroyed_tc1(void);

void s2tte_is_assigned_empty_tc1(void);

void s2tte_is_assigned_ns_tc1(void);
void s2tte_is_assigned_ns_tc2(void);

void s2tte_is_assigned_ram_tc1(void);
void s2tte_is_assigned_ram_tc2(void);

void s2tte_is_assigned_destroyed_tc1(void);

void s2tte_is_table_tc1(void);

void s2tte_get_ripas_tc1(void);
void s2tte_get_ripas_tc2(void);
void s2tte_get_ripas_tc3(void);
void s2tte_get_ripas_tc4(void);

void s2tt_init_unassigned_empty_tc1(void);
void s2tt_init_unassigned_empty_tc2(void);

void s2tt_init_unassigned_ram_tc1(void);
void s2tt_init_unassigned_ram_tc2(void);

void s2tt_init_unassigned_ns_tc1(void);
void s2tt_init_unassigned_ns_tc2(void);

void s2tt_init_unassigned_destroyed_tc1(void);
void s2tt_init_unassigned_destroyed_tc2(void);

void s2tt_init_assigned_empty_tc1(void);
void s2tt_init_assigned_empty_tc2(void);
void s2tt_init_assigned_empty_tc3(void);
void s2tt_init_assigned_empty_tc4(void);
void s2tt_init_assigned_empty_tc5(void);

void s2tt_init_assigned_ram_tc1(void);
void s2tt_init_assigned_ram_tc2(void);
void s2tt_init_assigned_ram_tc3(void);
void s2tt_init_assigned_ram_tc4(void);
void s2tt_init_assigned_ram_tc5(void);

void s2tt_init_assigned_ns_tc1(void);
void s2tt_init_assigned_ns_tc2(void);
void s2tt_init_assigned_ns_tc3(void);
void s2tt_init_assigned_ns_tc4(void);
void s2tt_init_assigned_ns_tc5(void);

void s2tt_init_assigned_destroyed_tc1(void);
void s2tt_init_assigned_destroyed_tc2(void);
void s2tt_init_assigned_destroyed_tc3(void);
void s2tt_init_assigned_destroyed_tc4(void);
void s2tt_init_assigned_destroyed_tc5(void);

void s2tte_pa_tc1(void);
void s2tte_pa_tc2(void);
void s2tte_pa_tc3(void);
void s2tte_pa_tc4(void);

void s2tte_is_addr_lvl_aligned_tc1(void);
void s2tte_is_addr_lvl_aligned_tc2(void);
void s2tte_is_addr_lvl_aligned_tc3(void);
void s2tte_is_addr_lvl_aligned_tc4(void);

void s2tte_map_size_tc1(void);
void s2tte_map_size_tc2(void);
void s2tte_map_size_tc3(void);

void s2tt_invalidate_page_tc1(void);

void s2tt_invalidate_block_tc1(void);

void s2tt_invalidate_pages_in_block_tc1(void);

void s2tt_is_unassigned_empty_block_tc1(void);
void s2tt_is_unassigned_empty_block_tc2(void);
void s2tt_is_unassigned_empty_block_tc3(void);

void s2tt_is_unassigned_ram_block_tc1(void);
void s2tt_is_unassigned_ram_block_tc2(void);
void s2tt_is_unassigned_ram_block_tc3(void);

void s2tt_is_unassigned_ns_block_tc1(void);
void s2tt_is_unassigned_ns_block_tc2(void);
void s2tt_is_unassigned_ns_block_tc3(void);

void s2tt_is_unassigned_destroyed_block_tc1(void);
void s2tt_is_unassigned_destroyed_block_tc2(void);
void s2tt_is_unassigned_destroyed_block_tc3(void);

void s2tt_maps_assigned_empty_block_tc1(void);
void s2tt_maps_assigned_empty_block_tc2(void);
void s2tt_maps_assigned_empty_block_tc3(void);
void s2tt_maps_assigned_empty_block_tc4(void);
void s2tt_maps_assigned_empty_block_tc5(void);
void s2tt_maps_assigned_empty_block_tc6(void);

void s2tt_maps_assigned_ram_block_tc1(void);
void s2tt_maps_assigned_ram_block_tc2(void);
void s2tt_maps_assigned_ram_block_tc3(void);
void s2tt_maps_assigned_ram_block_tc4(void);
void s2tt_maps_assigned_ram_block_tc5(void);
void s2tt_maps_assigned_ram_block_tc6(void);

void s2tt_maps_assigned_ns_block_tc1(void);
void s2tt_maps_assigned_ns_block_tc2(void);
void s2tt_maps_assigned_ns_block_tc3(void);
void s2tt_maps_assigned_ns_block_tc4(void);
void s2tt_maps_assigned_ns_block_tc5(void);
void s2tt_maps_assigned_ns_block_tc6(void);

void s2tt_maps_assigned_destroyed_block_tc1(void);
void s2tt_maps_assigned_destroyed_block_tc2(void);
void s2tt_maps_assigned_destroyed_block_tc3(void);
void s2tt_maps_assigned_destroyed_block_tc4(void);
void s2tt_maps_assigned_destroyed_block_tc5(void);
void s2tt_maps_assigned_destroyed_block_tc6(void);

void s2tt_skip_non_live_entries_tc1(void);
void s2tt_skip_non_live_entries_tc2(void);
void s2tt_skip_non_live_entries_tc3(void);
void s2tt_skip_non_live_entries_tc4(void);
void s2tt_skip_non_live_entries_tc5(void);
void s2tt_skip_non_live_entries_tc6(void);

void s2tt_walk_lock_unlock_tc1(void);
void s2tt_walk_lock_unlock_tc2(void);
void s2tt_walk_lock_unlock_tc3(void);
void s2tt_walk_lock_unlock_tc4(void);
void s2tt_walk_lock_unlock_tc5(void);
void s2tt_walk_lock_unlock_tc6(void);
void s2tt_walk_lock_unlock_tc7(void);
void s2tt_walk_lock_unlock_tc8(void);
void s2tt_walk_lock_unlock_tc9(void);
void s2tt_walk_lock_unlock_tc10(void);
void s2tt_walk_lock_unlock_tc11(void);
void s2tt_walk_lock_unlock_tc12(void);

#endif /* S2TT_TESTS_BASE */
