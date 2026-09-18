#!/usr/bin/env bash
# ec2-gate.sh -- the coordinator's GATE: sync local main to the EC2 mirror's main checkout and build the
# whole tree there, in dependency order, with every false-green trap from claude-notes/durable-notes.md
# and the ec2-build-mirror memory guarded.  Run from the coordinator's checkout (/shared/xv6iris) on main.
#
#   ec2-gate.sh            sync + full build (model-xv6iris, kernel-rocq, user-rocq, iris) + the three audits
#   ec2-gate.sh --no-audit sync + full build only
#   ec2-gate.sh --status   print the detached build's log (BUILD_RC=<n> marks the end)
#   ec2-gate.sh --audits   print the detached audits' log (AUDITS_DONE marks the end)
#   ec2-gate.sh --audit-now start the detached audits without building (after --status shows BUILD_RC=0)
#
# Prints "GATE GREEN at <sha>" or "GATE RED (...)" LAST; the exit status is the gate's.
set -euo pipefail
HOST="${EC2_HOST:-ec2-44-202-245-129.compute-1.amazonaws.com}"
KEY="${EC2_KEY:-/shared/xv6iris/aws/ags-fk.pem}"
LOCAL=/shared/xv6iris; REMOTE=/shared/xv6iris
SSH=(ssh -i "$KEY" -o BatchMode=yes -o ServerAliveInterval=30 "ubuntu@$HOST")
AUDIT=1; [ "${1:-}" = "--no-audit" ] && AUDIT=0; ONLYAUDIT=0; [ "${1:-}" = "--audit-now" ] && ONLYAUDIT=1
if [ "${1:-}" = "--status" ]; then "${SSH[@]}" 'cat /tmp/gate-build.log 2>/dev/null || echo "(no build log)"; tail -3 /tmp/gate-build-full.log 2>/dev/null | cut -c1-160'; exit 0; fi
if [ "${1:-}" = "--audits" ]; then "${SSH[@]}" 'cat /tmp/gate-audit.log 2>/dev/null || echo "(no audit log)"'; exit 0; fi

br="$(git -C $LOCAL branch --show-current)"
[ "$br" = main ] || { echo "GATE RED (local checkout is on '$br', not main)"; exit 1; }
[ -z "$(git -C $LOCAL status --short)" ] || { echo "GATE RED (local main is dirty)"; git -C $LOCAL status --short | head; exit 1; }
sha="$(git -C $LOCAL rev-parse HEAD)"

if [ $ONLYAUDIT = 0 ]; then
# 1. ship main by bundle, fast-forward the mirror's main (never reset --hard in the same script as a build)
tmp="$(mktemp -d)"; git -C $LOCAL bundle create "$tmp/main.bundle" main >/dev/null 2>&1
scp -q -i "$KEY" "$tmp/main.bundle" "ubuntu@$HOST:/tmp/gate-main.bundle"; rm -rf "$tmp"
"${SSH[@]}" "set -e; cd $REMOTE; [ -z \"\$(git status --short)\" ] || { echo 'GATE RED (mirror dirty)'; git status --short | head; exit 1; }; \
  git fetch -q /tmp/gate-main.bundle main:refs/heads/synced; [ \"\$(git branch --show-current)\" = main ] || git checkout -q main; \
  git merge -q --ff-only synced; [ \"\$(git rev-parse HEAD)\" = $sha ] || { echo 'GATE RED (mirror HEAD != local after ff)'; exit 1; }; \
  echo \"mirror at \$(git rev-parse --short HEAD)\""

# 2. build, DETACHED (a Spec change can rebuild a large cone, longer than an ssh session should hold):
#    subtree by subtree, each with its CoqMakefile regenerated (iris/CoqMakefile is untracked); the log ends
#    in BUILD_RC=<n>.  Poll with `ec2-gate.sh --status`.
"${SSH[@]}" "nohup bash -c 'set -o pipefail; cd $REMOTE && eval \$(opam env --switch=/shared/xv6rocq --set-switch) && export OCAMLRUNPARAM=l=4000000000; \
  echo BUILD at \$(git rev-parse --short HEAD); rc=0; for d in model-xv6iris kernel-rocq user-rocq iris; do \
    ( cd \$d && rocq makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1 && make -f CoqMakefile -j30 ) >> /tmp/gate-build-full.log 2>&1 || { rc=\$?; echo build FAILED in \$d rc=\$rc; break; }; \
    echo built \$d; done; \
  if grep -Eq "Error|Segmentation fault|Anomaly" /tmp/gate-build-full.log; then echo ---- errors:; grep -E "Error|Segmentation fault|Anomaly" -B3 -A8 /tmp/gate-build-full.log | tail -80; [ \$rc -eq 0 ] && rc=1; fi; \
  small=\$(find iris -name "*.vo" -size -1k | head); [ -z "\$small" ] || { echo suspiciously small .vo: \$small; rc=1; }; \
  echo BUILD_RC=\$rc' > /tmp/gate-build.log 2>&1 < /dev/null &"
echo "build started detached on the mirror at ${sha:0:10} -> ec2-gate.sh --status"
fi
# 3. audits, DETACHED (each takes ~7.5 min: Print Assumptions loads the whole cone); read them later with
#    `ec2-gate.sh --audits` (prints the log; the three counts must be system 13, echo 14, tree 13)
if [ $ONLYAUDIT = 1 ]; then
  "${SSH[@]}" "nohup bash -c 'cd $REMOTE && eval \$(opam env --switch=/shared/xv6rocq --set-switch) && echo AUDITS at \$(git rev-parse --short HEAD) && for t in audit-only audit-echo-only audit-tree-only; do echo == \$t; /usr/bin/time -f %es make -s \$t 2>&1 | grep -Ev \"^(Warning|make)\" | tail -30; done; echo AUDITS_DONE' > /tmp/gate-audit.log 2>&1 < /dev/null &" 
  echo "audits started detached on the mirror -> ec2-gate.sh --audits"
fi
echo "GATE: build detached at ${sha:0:10}; --status for BUILD_RC, then --audit-now, then --audits"
