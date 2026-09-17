#!/usr/bin/env bash
# ec2-lane.sh -- build an app-pipe lane's worktree on the EC2 mirror.
#
#   ec2-lane.sh <lane> sync                 push this worktree's changed files to the lane's remote clone
#   ec2-lane.sh <lane> check File.v [...]   sync, then FAST statement check (make File.vos) -- catches a broken
#                                           statement, NOT a broken proof (opaque proofs are skipped)
#   ec2-lane.sh <lane> build [make targets] sync, regen CoqMakefile if _CoqProject changed, make -j6 targets
#                                           (default: the whole iris tree); prints "RC=<n>" last -- trust ONLY that
#   ec2-lane.sh <lane> run '<shell>'        run a command in the remote clone's iris/ with the opam env set
#
# <lane> names the local worktree /shared/xv6iris-pipe-<lane> and the remote clone of the same name.
# The remote clone is FULLY BUILT at the base SHA, so dependencies never need building -- never run
# rocq/coqc/make LOCALLY.  Host and key: EC2_HOST / EC2_KEY (defaults below; the hostname changes
# on every restart of the box -- the coordinator updates it).
set -euo pipefail
LANE="${1:?lane}"; CMD="${2:?sync|check|build|run}"; shift 2
HOST="${EC2_HOST:-ec2-44-202-245-129.compute-1.amazonaws.com}"
KEY="${EC2_KEY:-/shared/xv6iris/aws/ags-fk.pem}"
LOCAL="/shared/xv6iris-pipe-$LANE"; REMOTE="/shared/xv6iris-pipe-$LANE"
SSH=(ssh -i "$KEY" -o BatchMode=yes -o ServerAliveInterval=30 "ubuntu@$HOST")
ENV='eval $(opam env --switch=/shared/xv6rocq --set-switch) && export OCAMLRUNPARAM="l=4000000000"'
[ -d "$LOCAL/.git" ] || [ -f "$LOCAL/.git" ] || { echo "no worktree $LOCAL" >&2; exit 2; }

sync() {
  # modified + untracked (not ignored) files, and deletions; mtimes NOT preserved so make rebuilds them
  local list; list="$(cd "$LOCAL" && git ls-files -m -o --exclude-standard)"
  local dels; dels="$(cd "$LOCAL" && git ls-files -d)"
  # tracked files that differ from the remote clone's base are committed on the lane branch: ship the
  # whole diff vs the merge-base too, so a fresh remote clone sees committed lane work
  local base; base="$(cd "$LOCAL" && git merge-base HEAD main)"
  local comm; comm="$(cd "$LOCAL" && git diff --name-only --diff-filter=AMR "$base" HEAD)"
  local all; all="$(printf '%s\n%s\n' "$list" "$comm" | sort -u | sed '/^$/d')"
  if [ -n "$all" ]; then
    printf '%s\n' "$all" | rsync -rlpgoD --files-from=- -e "ssh -i $KEY -o BatchMode=yes" "$LOCAL/" "ubuntu@$HOST:$REMOTE/" >/dev/null
    printf '%s\n' "$all" | "${SSH[@]}" "cd $REMOTE && xargs -r touch" || true
    echo "synced: $(printf '%s\n' "$all" | wc -l) file(s)" >&2
  fi
  if [ -n "$dels" ]; then
    printf '%s\n' "$dels" | "${SSH[@]}" "cd $REMOTE && xargs -r rm -f" || true
    echo "deleted remotely: $(printf '%s\n' "$dels" | wc -l)" >&2
  fi
}

remote() {  # run in remote iris/, pipefail, RC printed last
  "${SSH[@]}" "set -o pipefail; cd $REMOTE/iris && $ENV && ( $1 ) 2>&1 | grep -Ev '^(COQC|ROCQ|COQDEP|ROCQDEP|make\[)' || true; echo RC=\${PIPESTATUS[0]}"
}

case "$CMD" in
  sync)  sync ;;
  check) sync
         tgts=""; for f in "$@"; do tgts="$tgts ${f%.v}.vos"; done
         remote "make -f CoqMakefile -j6 $tgts" ;;
  build) sync
         remote "if [ ! CoqMakefile -nt _CoqProject ]; then rocq makefile -f _CoqProject -o CoqMakefile >/dev/null; fi; make -f CoqMakefile -j6 $* 2>&1 | grep -E 'Error|Segmentation fault|Anomaly|^File|^make' -A3 || true" ;;
  run)   remote "$*" ;;
  *) echo "unknown command $CMD" >&2; exit 2 ;;
esac
