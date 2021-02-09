#!/usr/bin/env bash
#**************************************************************************
#*                                                                        *
#*                                 OCaml                                  *
#*                                                                        *
#*                 David Allsopp, OCaml Labs, Cambridge.                  *
#*                                                                        *
#*   Copyright 2021 David Allsopp Ltd.                                    *
#*                                                                        *
#*   All rights reserved.  This file is distributed under the terms of    *
#*   the GNU Lesser General Public License version 2.1, with the          *
#*   special exception on linking described in the file LICENSE.          *
#*                                                                        *
#**************************************************************************

#------------------------------------------------------------------------
#This test checks that the Changes file has been modified by the pull
#request. Most contributions should come with a message in the Changes
#file, as described in our contributor documentation:
#
#  https://github.com/ocaml/ocaml/blob/trunk/CONTRIBUTING.md#changelog
#
#Some very minor changes (typo fixes for example) may not need
#a Changes entry. In this case, you may explicitly disable this test by
#adding the code word "No change entry needed" (on a single line) to
#a commit message of the PR, or using the "no-change-entry-needed" label
#on the github pull request.
#------------------------------------------------------------------------

set -e

UPSTREAM_BRANCH="$1"
UPSTREAM_HEAD="$2"
PR_BRANCH="$3"
PR_HEAD="$4"

# Ensure that we have all the commits
echo "Determining merge-base of $UPSTREAM_HEAD..$PR_HEAD for $PR_BRANCH"

DEEPEN=50
MSG='Deepening'
while ! git merge-base "$UPSTREAM_HEAD" "$PR_HEAD" &> /dev/null
do
  echo " - $MSG by $DEEPEN commits"
  git fetch origin --deepen=$DEEPEN "$PR_BRANCH" &> /dev/null
  MSG='Further deepening'
  ((DEEPEN*=2))
done
MERGE_BASE=$(git merge-base "$UPSTREAM_HEAD" "$PR_HEAD")

echo "$PR_BRANCH branched from $UPSTREAM_BRANCH at: $MERGE_BASE"

MSG='Check Changes has been updated'
COMMIT_RANGE="$MERGE_BASE..$PR_HEAD"

# Check if Changes has been updated in the PR
if git diff "$COMMIT_RANGE" --name-only --exit-code Changes > /dev/null; then
  # Check if any commit messages include something like No Changes entry needed
  REGEX='[Nn]o [Cc]hange.* needed'
  if [[ -n $(git log --grep="$REGEX" --max-count=1 "$COMMIT_RANGE") ]]; then
    echo -e "$MSG: \e[33mSKIPPED\e[0m (owing to commit message)"
  else
    echo -e "$MSG: \e[31mNO\e[0m"
    exit 1
  fi
else
  echo -e "$MSG: \e[32mYES\e[0m"
fi
