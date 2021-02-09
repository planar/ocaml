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
#This test checks that if configure.ac has been modified by the pull
#request, then configure has been correctly regenerated.
#------------------------------------------------------------------------

set -e

. tools/ci/actions/deepen-fetch.sh

# XXX The configure test _should_ test commit by commit for bisect-safety

# Test to see if any part of the directory name has been marked prune
not_pruned () {
  DIR=$(dirname "$1")
  if [[ $DIR = '.' ]] ; then
    return 0
  else
    case ",$(git check-attr typo.prune "$DIR" | sed -e 's/.*: //')," in
      ,set,)
      return 1
      ;;
      *)

      not_pruned "$DIR"
      return $?
    esac
  fi
}

CheckTypoTree () {
  export OCAML_CT_HEAD=$1
  export OCAML_CT_LS_FILES="git diff-tree --no-commit-id --name-only -r $2 --"
  export OCAML_CT_CAT='git cat-file --textconv'
  export OCAML_CT_PREFIX="$1:"
  GIT_INDEX_FILE=tmp-index git read-tree --reset -i "$1"
  git diff-tree --diff-filter=d --no-commit-id --name-only -r "$2" \
    | (while IFS= read -r path
  do
    if not_pruned "$path" ; then
      echo "Checking $1: $path"
      if ! tools/check-typo "./$path" ; then
        touch failed
      fi
    else
      echo "NOT checking $1: $path (typo.prune)"
    fi
    case "$path" in
      configure|configure.ac|VERSION|tools/ci/travis/travis-ci.sh)
        touch CHECK_CONFIGURE;;
    esac
  done)
  rm -f tmp-index
  if [[ -e CHECK_CONFIGURE ]] ; then
    rm -f CHECK_CONFIGURE
    echo "configure generation altered in $1"
    echo 'Verifying that configure.ac generates configure'
    git checkout "$1"
    mv configure configure.ref
    make configure
    if ! diff -q configure configure.ref >/dev/null ; then
      echo "configure.ac no longer generates configure in $1, \
please run rm configure ; make configure and commit"
      exit 1
    fi
  fi
}

# XXX Get these are parameters higher up the script

# XXX Temporarily 1, while we sort out configure
CHECK_ALL_COMMITS=1

export OCAML_CT_GIT_INDEX='tmp-index'
export OCAML_CT_CA_FLAG='--cached'
# Work around an apparent bug in Ubuntu 12.4.5
# See https://bugs.launchpad.net/ubuntu/+source/gawk/+bug/1647879
rm -f failed
# XXX Tidy this up with a better decision on the call
#if [[ -z $TRAVIS_COMMIT_RANGE ]]
#then CheckTypoTree "$TRAVIS_COMMIT" "$TRAVIS_COMMIT"
#else
  COMMIT_RANGE="$MERGE_BASE..$PR_HEAD"
  echo "Debug: will scan $COMMIT_RANGE"
#  if [[ $TRAVIS_EVENT_TYPE = 'pull_request' ]]
#  then TRAVIS_COMMIT_RANGE=$TRAVIS_MERGE_BASE..$TRAVIS_PULL_REQUEST_SHA
#  fi
  if [[ $CHECK_ALL_COMMITS -eq 1 ]]
  then
    for commit in $(git rev-list "$COMMIT_RANGE" --reverse)
    do
      CheckTypoTree "$commit" "$commit"
    done
  else
#    if [[ -z $TRAVIS_PULL_REQUEST_SHA ]]; then
#    CheckTypoTree "$TRAVIS_COMMIT" "$TRAVIS_COMMIT"
#    else
      CheckTypoTree "$PR_HEAD" "$TRAVIS_COMMIT_RANGE"
#    fi
  fi
#fi
echo complete
test -e failed && exit 1

# XXX This is the old script

exit 0

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
