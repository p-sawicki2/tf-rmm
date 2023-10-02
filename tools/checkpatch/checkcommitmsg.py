#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

from argparse import ArgumentParser
import sys
import re
import os
import pathlib

VALID_TYPES = [
    "feat",
    "fix",
    "build",
    "docs",
    "perf",
    "refactor",
    "revert",
    "style",
    "test",
    "chore"
]

#
# Maximum depth that scope directory can be. Indexed from 0.
#
SCOPE_MAX_DEPTH = 1

def print_valid_types():
    for type in VALID_TYPES:
        print("- " + type)

    print()

#
# Print total number of errors and exit with error code
#
def print_error_and_exit(total_errors):
    if total_errors:
        print("total: " + str(total_errors) + " errors")
        sys.exit(1)
    else:
        sys.exit(0)

#
# Return a list of directories up to a specified depth. These directories are
# valid scopes.
#
def get_valid_dirs():
    current_file_directory = pathlib.Path(__file__).parent.resolve()
    project_root = current_file_directory.parent.parent

    valid_directories = []

    #
    # Iterate through all subdirectories, include only the ones which are at or
    # below the maximum depth.
    #
    for dir,_,_ in os.walk(project_root):
        relative_dir = os.path.relpath(dir, project_root)
        if str(relative_dir).count(os.path.sep) <= SCOPE_MAX_DEPTH:
            valid_directories.append(str(relative_dir))

    return valid_directories

def check_title(title):
    errors = 0

    if not title:
        print("ERROR: Title cannot be empty")
        errors += 1
        return errors

    if len(title) > 50:
        print("ERROR: Title must be 50 characters or less")
        errors += 1

    title_parts = title.split(":", 1)

    if len(title_parts) < 2:
        print("ERROR: Title must be of the form:\n\ttype(scope): description\n")
        errors += 1
        return errors

    subject = title_parts[0]

    if not subject.islower():
        print("ERROR: Title subject must be lowercase")
        errors += 1

    #
    # Extract the type and scope from the subject
    #
    scope_match = re.search("\(.*\)", subject)

    if scope_match is None:
        scope = ""
        type = subject
    else:
        scope = scope_match.group().strip("()")
        scope_begin_index = scope_match.span()[0]
        type = subject[:scope_begin_index]

    if not type in VALID_TYPES:
        print("ERROR: Type must be one of the following:")
        print_valid_types()
        errors += 1

    if scope:
        valid_scopes = get_valid_dirs()
        if not scope in valid_scopes:
            print("WARNING: Scope should match the directory where the patch applies")
    else:
        print("ERROR: Subject must contain a scope")
        errors += 1

    description = title_parts[1].lstrip()
    if not description:
        print("ERROR: Title description cannot be empty")
        errors += 1

    return errors

def check_body(lines):
    errors = 0

    if not lines:
        print("ERROR: Body of commit message cannot be empty")
        errors += 1
        return errors

    for line in lines:
        if len(line) > 72:
            print("ERROR: Width of commit message body must be 72 characters or less")
            errors += 1
            return errors

    return errors

#
# Check that the trailer contains both a Signed-off-by and Change-Id.
#
def check_trailer(trailer_lines):
    has_signed_off_by = False
    has_change_id = False

    errors = 0

    for line in trailer_lines:
        signed_off_by_match = re.search("^Signed-off-by: .* <.*>$", line)
        if (signed_off_by_match is not None):
            has_signed_off_by = True

        change_id_match = re.search("^Change-Id: I.*", line)
        if (change_id_match is not None):
            has_change_id = True

    if not has_signed_off_by:
        print("ERROR: Trailer must contain Signed-off-by")
        errors += 1

    if not has_change_id:
        print("ERROR: Trailer must contain Change-Id")
        errors += 1

    return errors

#
# Return the index at which the trailer begins. If the commit message only
# consists of the trailer, return 0.
#
def find_trailer(message_lines):
    #
    # Iterate backwards over the message, starting at the last line. Stop when
    # a non-trailer line is encountered.
    #
    for idx, line in reversed(list(enumerate(message_lines))):
        signed_off_by_match = re.search("^Signed-off-by: .* <.*>$", line)
        change_id_match = re.search("^Change-Id: I.*", line)

        if (signed_off_by_match is None and change_id_match is None):
            return idx + 1

    return 0

def check_commit_msg(message):
    #
    # Convert message into a list of its lines, and remove all empty lines
    #
    message_lines = message.splitlines()
    message_lines = [line for line in message_lines if line != ""]

    trailer_start_idx = find_trailer(message_lines)

    if trailer_start_idx == 0:
        print("ERROR: Commit message requires a title and body")
        title = ""
        body = ""
    else:
        title = message_lines[0]
        body = message_lines[1:trailer_start_idx]

    trailer = message_lines[trailer_start_idx:]

    total_errors = 0

    total_errors += check_title(title)
    total_errors += check_body(body)
    total_errors += check_trailer(trailer)

    return total_errors

if __name__ == '__main__':
    parser = ArgumentParser(description='Check commit messages')
    parser.add_argument('message')

    args = parser.parse_args()

    total_errors = check_commit_msg(args.message)
    print_error_and_exit(total_errors)
