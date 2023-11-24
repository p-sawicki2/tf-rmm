/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>
#include <s2tt_tests_base.h>

extern "C" {
#include <test_helpers.h>
#include <s2tt_tests_base.h>
#include <s2tt_test_helpers.h>
}

TEST_GROUP(s2tt_lpa2) {
	TEST_SETUP()
	{
		s2tt_test_helpers_setup(LPA2_ENABLED);
	}

	TEST_TEARDOWN()
	{}
};

TEST(s2tt_lpa2, s2tte_create_unassigned_empty_tc1)
{
	s2tte_create_unassigned_empty_tc1();
}

TEST(s2tt_lpa2, s2tte_create_unassigned_ram_tc1)
{
	s2tte_create_unassigned_ram_tc1();
}

TEST(s2tt_lpa2, s2tte_create_unassigned_ns_tc1)
{
	s2tte_create_unassigned_ns_tc1();
}

TEST(s2tt_lpa2, s2tte_create_unassigned_destroyed_tc1)
{
	s2tte_create_unassigned_destroyed_tc1();
}

TEST(s2tt_lpa2, s2tte_create_assigned_empty_tc1)
{
	s2tte_create_assigned_empty_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_create_assigned_emtpy_tc2)
{
	s2tte_create_assigned_empty_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tt_create_assigned_emtpy_tc3)
{
	s2tte_create_assigned_empty_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tt_create_assigned_emtpy_tc4)
{
	s2tte_create_assigned_empty_tc4();
}

TEST(s2tt_lpa2, s2tte_create_assigned_ram_tc1)
{
	s2tte_create_assigned_ram_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_ram_tc2)
{
	s2tte_create_assigned_ram_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_ram_tc3)
{
	s2tte_create_assigned_ram_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_ram_tc4)
{
	s2tte_create_assigned_ram_tc4();
}

TEST(s2tt_lpa2, s2tte_create_assigned_ns_tc1)
{
	s2tte_create_assigned_ns_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_ns_tc2)
{
	s2tte_create_assigned_ns_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_ns_tc3)
{
	s2tte_create_assigned_ns_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_ns_tc4)
{
	s2tte_create_assigned_ns_tc4();
}

TEST(s2tt_lpa2, s2tte_create_assigned_destroyed_tc1)
{
	s2tte_create_assigned_destroyed_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_destroyed_tc2)
{
	s2tte_create_assigned_destroyed_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_destroyed_tc3)
{
	s2tte_create_assigned_destroyed_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_destroyed_tc4)
{
	s2tte_create_assigned_destroyed_tc4();
}

TEST(s2tt_lpa2, s2tte_create_assigned_unchanged_tc1)
{
	s2tte_create_assigned_unchanged_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_unchanged_tc2)
{
	s2tte_create_assigned_unchanged_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_unchanged_tc3)
{
	s2tte_create_assigned_unchanged_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_unchanged_tc4)
{
	s2tte_create_assigned_unchanged_tc4();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_assigned_unchanged_tc5)
{
	s2tte_create_assigned_unchanged_tc5();
}

TEST(s2tt_lpa2, s2tte_create_table_tc1)
{
	s2tte_create_table_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_table_tc2)
{
	s2tte_create_table_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_table_tc3)
{
	s2tte_create_table_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_create_table_tc4)
{
	s2tte_create_table_tc4();
}

TEST(s2tt_lpa2, host_ns_s2tte_is_valid_tc1)
{
	host_ns_s2tte_is_valid_tc1();
}

TEST(s2tt_lpa2, host_ns_s2tte_is_valid_tc2)
{
	host_ns_s2tte_is_valid_tc2();
}

ASSERT_TEST(s2tt_lpa2, host_ns_s2tte_is_valid_tc3)
{
	host_ns_s2tte_is_valid_tc3();
}

ASSERT_TEST(s2tt_lpa2, host_ns_s2tte_is_valid_tc4)
{
	host_ns_s2tte_is_valid_tc4();
}

TEST(s2tt_lpa2, host_ns_s2tte_tc1)
{
	host_ns_s2tte_tc1();
}

ASSERT_TEST(s2tt_lpa2, host_ns_s2tte_tc2)
{
	host_ns_s2tte_tc2();
}

ASSERT_TEST(s2tt_lpa2, host_ns_s2tte_tc3)
{
	host_ns_s2tte_tc3();
}

TEST(s2tt_lpa2, s2tte_has_ripas_tc1)
{
	s2tte_has_ripas_tc1();
}

TEST(s2tt_lpa2, s2tte_has_ripas_tc2)
{
	s2tte_has_ripas_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_has_ripas_tc3)
{
	s2tte_has_ripas_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_has_ripas_tc4)
{
	s2tte_has_ripas_tc4();
}

TEST(s2tt_lpa2, s2tte_is_unassigned_tc1)
{
	s2tte_is_unassigned_tc1();
}

TEST(s2tt_lpa2, s2tte_is_unassigned_empty_tc1)
{
	s2tte_is_unassigned_empty_tc1();
}

TEST(s2tt_lpa2, s2tte_is_unassigned_ram_tc1)
{
	s2tte_is_unassigned_ram_tc1();
}

TEST(s2tt_lpa2, s2tte_is_unassigned_ns_tc1)
{
	s2tte_is_unassigned_ns_tc1();
}

TEST(s2tt_lpa2, s2tte_is_unassigned_destroyed_tc1)
{
	s2tte_is_unassigned_destroyed_tc1();
}

TEST(s2tt_lpa2, s2tte_is_assigned_empty_tc1)
{
	s2tte_is_assigned_empty_tc1();
}

TEST(s2tt_lpa2, s2tte_is_assigned_ns_tc1)
{
	s2tte_is_assigned_ns_tc1();
}

TEST(s2tt_lpa2, s2tte_is_assigned_ns_tc2)
{
	s2tte_is_assigned_ns_tc2();
}

TEST(s2tt_lpa2, s2tte_is_assigned_ram_tc1)
{
	s2tte_is_assigned_ram_tc1();
}

TEST(s2tt_lpa2, s2tte_is_assigned_ram_tc2)
{
	s2tte_is_assigned_ram_tc2();
}

TEST(s2tt_lpa2, s2tte_is_assigned_destroyed_tc1)
{
	s2tte_is_assigned_destroyed_tc1();
}

TEST(s2tt_lpa2, s2tte_is_table_tc1)
{
	s2tte_is_table_tc1();
}

TEST(s2tt_lpa2, s2tte_get_ripas_tc1)
{
	s2tte_get_ripas_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_get_ripas_tc2)
{
	s2tte_get_ripas_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_get_ripas_tc3)
{
	s2tte_get_ripas_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_get_ripas_tc4)
{
	s2tte_get_ripas_tc4();
}

TEST(s2tt_lpa2, s2tt_init_unassigned_empty_tc1)
{
	s2tt_init_unassigned_empty_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_unassigned_empty_tc2)
{
	s2tt_init_unassigned_empty_tc2();
}

TEST(s2tt_lpa2, s2tt_init_unassigned_ram_tc1)
{
	s2tt_init_unassigned_ram_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_unassigned_ram_tc2)
{
	s2tt_init_unassigned_ram_tc2();
}

TEST(s2tt_lpa2, s2tt_init_unassigned_ns_tc1)
{
	s2tt_init_unassigned_ns_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_unassigned_ns_tc2)
{
	s2tt_init_unassigned_ns_tc2();
}

TEST(s2tt_lpa2, s2tt_init_unassigned_destroyed_tc1)
{
	s2tt_init_unassigned_destroyed_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_unassigned_destroyed_tc2)
{
	s2tt_init_unassigned_destroyed_tc2();
}

TEST(s2tt_lpa2, s2tt_init_assigned_empty_tc1)
{
	s2tt_init_assigned_empty_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_empty_tc2)
{
	s2tt_init_assigned_empty_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_empty_tc3)
{
	s2tt_init_assigned_empty_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_empty_tc4)
{
	s2tt_init_assigned_empty_tc4();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_empty_tc5)
{
	s2tt_init_assigned_empty_tc5();
}

TEST(s2tt_lpa2, s2tt_init_assigned_ram_tc1)
{
	s2tt_init_assigned_ram_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ram_tc2)
{
	s2tt_init_assigned_ram_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ram_tc3)
{
	s2tt_init_assigned_ram_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ram_tc4)
{
	s2tt_init_assigned_ram_tc4();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ram_tc5)
{
	s2tt_init_assigned_ram_tc5();
}

TEST(s2tt_lpa2, s2tt_init_assigned_ns_tc1)
{
	s2tt_init_assigned_ns_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ns_tc2)
{
	s2tt_init_assigned_ns_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ns_tc3)
{
	s2tt_init_assigned_ns_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ns_tc4)
{
	s2tt_init_assigned_ns_tc4();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_ns_tc5)
{
	s2tt_init_assigned_ns_tc5();
}

TEST(s2tt_lpa2, s2tt_init_assigned_destroyed_tc1)
{
	s2tt_init_assigned_destroyed_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_destroyed_tc2)
{
	s2tt_init_assigned_destroyed_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_destroyed_tc3)
{
	s2tt_init_assigned_destroyed_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_destroyed_tc4)
{
	s2tt_init_assigned_destroyed_tc4();
}

ASSERT_TEST(s2tt_lpa2, s2tt_init_assigned_destroyed_tc5)
{
	s2tt_init_assigned_destroyed_tc5();
}

TEST(s2tt_lpa2, s2tte_pa_tc1)
{
	s2tte_pa_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_tc2)
{
	s2tte_pa_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_tc3)
{
	s2tte_pa_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_tc4)
{
	s2tte_pa_tc4();
}

TEST(s2tt_lpa2, s2tte_pa_table_tc1)
{
	s2tte_pa_table_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_table_tc2)
{
	s2tte_pa_table_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_table_tc3)
{
	s2tte_pa_table_tc3();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_table_tc4)
{
	s2tte_pa_table_tc4();
}

ASSERT_TEST(s2tt_lpa2, s2tte_pa_table_tc5)
{
	s2tte_pa_table_tc5();
}

TEST(s2tt_lpa2, addr_is_level_aligned_tc1)
{
	addr_is_level_aligned_tc1();
}

TEST(s2tt_lpa2, addr_is_level_aligned_tc2)
{
	addr_is_level_aligned_tc2();
}

ASSERT_TEST(s2tt_lpa2, addr_is_level_aligned_tc3)
{
	addr_is_level_aligned_tc3();
}

ASSERT_TEST(s2tt_lpa2, addr_is_level_aligned_tc4)
{
	addr_is_level_aligned_tc4();
}

TEST(s2tt_lpa2, s2tte_map_size_tc1)
{
	s2tte_map_size_tc1();
}

ASSERT_TEST(s2tt_lpa2, s2tte_map_size_tc2)
{
	s2tte_map_size_tc2();
}

ASSERT_TEST(s2tt_lpa2, s2tte_map_size_tc3)
{
	s2tte_map_size_tc3();
}

ASSERT_TEST(s2tt_lpa2, invalidate_page_tc1)
{
	invalidate_page_tc1();
}

ASSERT_TEST(s2tt_lpa2, invalidate_block_tc1)
{
	invalidate_block_tc1();
}

ASSERT_TEST(s2tt_lpa2, invalidate_pages_in_block_tc1)
{
	invalidate_pages_in_block_tc1();
}

TEST(s2tt_lpa2, table_is_unassigned_empty_block_tc1)
{
	table_is_unassigned_empty_block_tc1();
}

TEST(s2tt_lpa2, table_is_unassigned_empty_block_tc2)
{
	table_is_unassigned_empty_block_tc2();
}

ASSERT_TEST(s2tt_lpa2, table_is_unassigned_empty_block_tc3)
{
	table_is_unassigned_empty_block_tc3();
}

TEST(s2tt_lpa2, table_is_unassigned_ram_block_tc1)
{
	table_is_unassigned_ram_block_tc1();
}

TEST(s2tt_lpa2, table_is_unassigned_ram_block_tc2)
{
	table_is_unassigned_ram_block_tc2();
}

ASSERT_TEST(s2tt_lpa2, table_is_unassigned_ram_block_tc3)
{
	table_is_unassigned_ram_block_tc3();
}

TEST(s2tt_lpa2, table_is_unassigned_ns_block_tc1)
{
	table_is_unassigned_ns_block_tc1();
}

TEST(s2tt_lpa2, table_is_unassigned_ns_block_tc2)
{
	table_is_unassigned_ns_block_tc2();
}

ASSERT_TEST(s2tt_lpa2, table_is_unassigned_ns_block_tc3)
{
	table_is_unassigned_ns_block_tc3();
}

TEST(s2tt_lpa2, table_is_unassigned_destroyed_block_tc1)
{
	table_is_unassigned_destroyed_block_tc1();
}

TEST(s2tt_lpa2, table_is_unassigned_destroyed_block_tc2)
{
	table_is_unassigned_destroyed_block_tc2();
}

ASSERT_TEST(s2tt_lpa2, table_is_unassigned_destroyed_block_tc3)
{
	table_is_unassigned_destroyed_block_tc3();
}

TEST(s2tt_lpa2, table_maps_assigned_empty_block_tc1)
{
	table_maps_assigned_empty_block_tc1();
}

TEST(s2tt_lpa2, table_maps_assigned_empty_block_tc2)
{
	table_maps_assigned_empty_block_tc2();
}

TEST(s2tt_lpa2, table_maps_assigned_empty_block_tc3)
{
	table_maps_assigned_empty_block_tc3();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_empty_block_tc4)
{
	table_maps_assigned_empty_block_tc4();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_empty_block_tc5)
{
	table_maps_assigned_empty_block_tc5();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_empty_block_tc6)
{
	table_maps_assigned_empty_block_tc6();
}

TEST(s2tt_lpa2, table_maps_assigned_ram_block_tc1)
{
	table_maps_assigned_ram_block_tc1();
}

TEST(s2tt_lpa2, table_maps_assigned_ram_block_tc2)
{
	table_maps_assigned_ram_block_tc2();
}

TEST(s2tt_lpa2, table_maps_assigned_ram_block_tc3)
{
	table_maps_assigned_ram_block_tc3();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_ram_block_tc4)
{
	table_maps_assigned_ram_block_tc4();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_ram_block_tc5)
{
	table_maps_assigned_ram_block_tc5();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_ram_block_tc6)
{
	table_maps_assigned_ram_block_tc6();
}

TEST(s2tt_lpa2, table_maps_assigned_ns_block_tc1)
{
	table_maps_assigned_ns_block_tc1();
}

TEST(s2tt_lpa2, table_maps_assigned_ns_block_tc2)
{
	table_maps_assigned_ns_block_tc2();
}

TEST(s2tt_lpa2, table_maps_assigned_ns_block_tc3)
{
	table_maps_assigned_ns_block_tc3();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_ns_block_tc4)
{
	table_maps_assigned_ns_block_tc4();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_ns_block_tc5)
{
	table_maps_assigned_ns_block_tc5();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_ns_block_tc6)
{
	table_maps_assigned_ns_block_tc6();
}

TEST(s2tt_lpa2, table_maps_assigned_destroyed_block_tc1)
{
	table_maps_assigned_destroyed_block_tc1();
}

TEST(s2tt_lpa2, table_maps_assigned_destroyed_block_tc2)
{
	table_maps_assigned_destroyed_block_tc2();
}

TEST(s2tt_lpa2, table_maps_assigned_destroyed_block_tc3)
{
	table_maps_assigned_destroyed_block_tc3();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_destroyed_block_tc4)
{
	table_maps_assigned_destroyed_block_tc4();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_destroyed_block_tc5)
{
	table_maps_assigned_destroyed_block_tc5();
}

ASSERT_TEST(s2tt_lpa2, table_maps_assigned_destroyed_block_tc6)
{
	table_maps_assigned_destroyed_block_tc6();
}

TEST(s2tt_lpa2, skip_non_live_entries_tc1)
{
	skip_non_live_entries_tc1();
}

ASSERT_TEST(s2tt_lpa2, skip_non_live_entries_tc2)
{
	skip_non_live_entries_tc2();
}

ASSERT_TEST(s2tt_lpa2, skip_non_live_entries_tc3)
{
	skip_non_live_entries_tc3();
}

ASSERT_TEST(s2tt_lpa2, skip_non_live_entries_tc4)
{
	skip_non_live_entries_tc4();
}

ASSERT_TEST(s2tt_lpa2, skip_non_live_entries_tc5)
{
	skip_non_live_entries_tc5();
}

ASSERT_TEST(s2tt_lpa2, skip_non_live_entries_tc6)
{
	skip_non_live_entries_tc6();
}

TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc1)
{
	rtt_walk_lock_unlock_tc1();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc2)
{
	rtt_walk_lock_unlock_tc2();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc3)
{
	rtt_walk_lock_unlock_tc3();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc4)
{
	rtt_walk_lock_unlock_tc4();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc5)
{
	rtt_walk_lock_unlock_tc5();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc6)
{
	rtt_walk_lock_unlock_tc6();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc7)
{
	rtt_walk_lock_unlock_tc7();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc8)
{
	rtt_walk_lock_unlock_tc8();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc9)
{
	rtt_walk_lock_unlock_tc9();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc10)
{
	rtt_walk_lock_unlock_tc10();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc11)
{
	rtt_walk_lock_unlock_tc11();
}

ASSERT_TEST(s2tt_lpa2, rtt_walk_lock_unlock_tc12)
{
	rtt_walk_lock_unlock_tc12();
}
