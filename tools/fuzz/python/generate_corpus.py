#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

"""Generate fuzzing corpus or inputs"""

from data_type import GRANULE_PAGE_COUNT, PAGE_SIZE \
		, SIZE_OF_GRANULE, COMMAND_COUNT, REGISTER_COUNT \
		, REGISTER_SIZE, FID_BEGIN, FID_END
import sys
import random
from data_type import RMMFuzzingInput
import os

				  # granule delegate #1
delegate_and_undelegate=[(0, 0, 0xC4000151), (0, 1, 0) \
				  # granule delegate #2
				  , (1, 0, 0xC4000151), (1, 1, PAGE_SIZE) \
				  # granule delegate #3
				  , (2, 0, 0xC4000151), (2, 1, 2 * PAGE_SIZE) \
				  # granule delegate #4
				  , (3, 0, 0xC4000151), (3, 1, 3 * PAGE_SIZE) \
				  # This delegate will fail
				  , (4, 0, 0xC4000151), (4, 1, 3 * PAGE_SIZE) \
				  # granule undelegate #1
				  , (5, 0, 0xC4000152), (5, 1, 0) \
				  # granule undelegate #2
				  , (6, 0, 0xC4000152), (6, 1, PAGE_SIZE) \
				  # granule undelegate #3
				  , (7, 0, 0xC4000152), (7, 1, 2 * PAGE_SIZE) \
				  # granule undelegate #4
				  , (8, 0, 0xC4000152), (8, 1, 3 * PAGE_SIZE) \
				  # This undelegate will fail
				  , (9, 0, 0xC4000152), (9, 1, 3 * PAGE_SIZE) ]

ipa = random.randint(0, 2 ** REGISTER_SIZE - 1)
			  # granule delegate #1
realm_create_activate = [(0, 0, 0xC4000151), (0, 1, 0) \
			  # realm create #1 with param #2
			  , (1, 0, 0xC4000158), (1, 1, 0), (1, 2, PAGE_SIZE) \
			  # granule delegate #3
			  , (2, 0, 0xC4000151), (2, 1, 2 * PAGE_SIZE) \
			  # rtt create on realm #1 with rtt #3
			  , (3, 0, 0xC400015D), (3, 1, 0), (3, 2, 2 * PAGE_SIZE) \
			  , (3, 3, ipa), (3, 4, 1) \
			  # granule delegate #4
			  , (4, 0, 0xC4000151), (4, 1, 3 * PAGE_SIZE) \
			  # rtt create on realm #1 with rtt #4
			  , (5, 0, 0xC400015D), (5, 1, 0), (5, 2, 3 * PAGE_SIZE) \
			  , (5, 3, ipa), (5, 4, 2) \
			  # granule delegate #5
			  , (6, 0, 0xC4000151), (6, 1, 4 * PAGE_SIZE) \
			  # rtt create on realm #1 with rtt #5
			  , (7, 0, 0xC400015D), (7, 1, 0), (7, 2, 4 * PAGE_SIZE) \
			  , (7, 3, ipa), (7, 4, 3) \
			  # set ripas realm #1
			  , (8, 0, 0xC4000169), (8, 1, 0) \
			  # granule delegate #6
			  , (9, 0, 0xC4000151), (9, 1, 5 * PAGE_SIZE) \
			  # data create on realm #1 with data #6 and param #7
			  , (10, 0, 0xC4000153), (10, 1, 0), (10, 2, 5 * PAGE_SIZE) \
			  , (10, 3, ipa), (10, 4, 6 * PAGE_SIZE) \
			  # activate realm #1
			  , (11, 0, 0xC4000157), (11, 1, 0) ]

			  # granule delegate #1
rec_create = [(0, 0, 0xC4000151), (0, 1, 0) \
			  # realm create #1 with param #2
			  , (1, 0, 0xC4000158), (1, 1, 0), (1, 2, PAGE_SIZE) \
			  # rec aux count on realm #1
			  , (2, 0, 0xC4000167), (2, 1, 0) \
			  # granule delegate #3
			  , (3, 0, 0xC4000151), (3, 1, 2 * PAGE_SIZE) \
			  # rec create #3 on realm #1 with param #4
			  , (4, 0, 0xC4000167), (4, 1, 0), (4, 2, 2 * PAGE_SIZE) \
			  , (4, 3, 3 * PAGE_SIZE) ]

realm_destroy = [(0, 0, 0xC4000151), (0, 1, 0) \
			  # realm create #1 with param #2
			  , (1, 0, 0xC4000158), (1, 1, 0), (1, 2, PAGE_SIZE) \
			  # granule delegate #3
			  , (2, 0, 0xC4000151), (2, 1, 2 * PAGE_SIZE) \
			  # rtt create on realm #1 with rtt #3
			  , (3, 0, 0xC400015D), (3, 1, 0), (3, 2, 2 * PAGE_SIZE) \
			  , (3, 3, ipa), (3, 4, 1) \
			  # granule delegate #4
			  , (4, 0, 0xC4000151), (4, 1, 3 * PAGE_SIZE) \
			  # rtt create on realm #1 with rtt #4
			  , (5, 0, 0xC400015D), (5, 1, 0), (5, 2, 3 * PAGE_SIZE) \
			  , (5, 3, ipa), (5, 4, 2) \
			  # granule delegate #5
			  , (6, 0, 0xC4000151), (6, 1, 4 * PAGE_SIZE) \
			  # rtt create on realm #1 with rtt #5
			  , (7, 0, 0xC400015D), (7, 1, 0), (7, 2, 4 * PAGE_SIZE) \
			  , (7, 3, ipa), (7, 4, 3) \
			  # set ripas realm #1
			  , (8, 0, 0xC4000169), (8, 1, 0) \
			  # granule delegate #6
			  , (9, 0, 0xC4000151), (9, 1, 5 * PAGE_SIZE) \
			  # data create #6 on realm #1 with data #6 and param #7
			  , (10, 0, 0xC4000153), (10, 1, 0), (10, 2, 5 * PAGE_SIZE) \
			  , (10, 3, ipa), (10, 4, 6 * PAGE_SIZE) \
			  # granule delegate #8
			  , (11, 0, 0xC4000151), (11, 1, 8 * PAGE_SIZE) \
			  # rec create #8 on realm #1 with param #9
			  , (12, 0, 0xC4000167), (12, 1, 0), (12, 2, 7 * PAGE_SIZE) \
			  , (12, 3, 8 * PAGE_SIZE) \
			  # rec destroy #8
			  , (13, 0, 0xC400015B), (13, 1, 7 * PAGE_SIZE) \
			  # data destroy #6
			  , (14, 0, 0xC4000155), (14, 1, 0), (14, 2, ipa) \
			  # rtt destroy #5
			  , (15, 0, 0xC400015E), (15, 1, 0), (15, 2, ipa), (15, 3, 3) \
			  # rtt destroy #4
			  , (16, 0, 0xC400015E), (16, 1, 0), (16, 2, ipa), (16, 3, 2) \
			  # rtt destroy #3
			  , (17, 0, 0xC400015E), (17, 1, 0), (17, 2, ipa), (17, 3, 1) \
			  # realm destroy #2
			  , (18, 0, 0xC4000159), (18, 1, 0) ]

if __name__ == "__main__":

	if len(sys.argv) < 2:
		raise Exception("No output path/prefix.")

	if os.path.dirname(sys.argv[1]) != '':
		os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)

	for (file_name, command) in \
			[ ("delegate_and_undelegate", delegate_and_undelegate) \
			, ("realm_create_activate", realm_create_activate) \
			, ("rec_create", rec_create) \
			, ("realm_destroy", realm_destroy) ]:
		with open(sys.argv[1] + "corpus" + file_name + ".bin", "wb") as file:
			file.write(RMMFuzzingInput.random_with_commands(command).to_bytes())
			file.close()
