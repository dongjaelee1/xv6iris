# CHECKPOINT — the echo application theorem, 2026-09-16

Handoff document for the next coordinator. Written by the outgoing coordinator
after the owner's instruction to stop spawning workers and checkpoint on
quiescence. ALL LANES HAVE STOPPED; nothing is running; every lane's work is
either on `origin/main` or recorded in a handover file named below. Everything
here is stated in ordinary concurrent-separation-logic and xv6 terms; every
term of art is defined on first use.

State of `origin/main`: `e8b61dc6a` (IO-LEAF M6a(2)b) — the notes commit for
it follows this checkpoint. Read `claude-notes/projects/app-echo.md` first:
its lane list (section "Lanes, in execution order") and every LANDED note
dated 2026-09-16 are the authoritative record; this document is the map.

## 1. The theorem and what it still assumes

`iris/UInitBootAdequacy.v`, `echo_adequacy_modulo_phi`. Conclusion: for every
finite run of the machine from the real disk image, IF the console input keeps
the typing discipline (`EchoDisc.disc`), THEN in every power cycle everything
on the console UART's wire is a prefix of the transcript the input calls for
(`Forall good_out (cycles_of h)`). The conclusion is pure (about the trace).
The trace predicates admit init's failure transcripts and the shell's own fork
panic as "prologue rounds" (lane PROLOGUE-ALTS); the good run is unchanged.

Open hypotheses beyond the machine model and the disk image: `Hsh_owed`, TWO
Coq-level entailments about the shell's program:

```
(⊢ UkSh.sh_deps (PS := uprogSG_free))          (* the FREE CONSOLE-WRITE LAW *)
/\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)      (* the shell's REST-OF-LINE obligation *)
```

- `sh_deps := udepw_law 16`: a placeholder that lets a program's write(16)
  syscall count as paid without the era's credential. It is spent at exactly
  FOUR leaves (the endgame audit): `UkSh.ksh_w_of_law`, `ksh_w_of_prompt_in`'s
  right arm, `UkShDiag.ksh_w1_of_law`, `UkInit.kinit_w1_of_law`. Everything
  else is a pass-through (`UkSh.wp_ksh_read`'s is dead, deletable). It
  disappears when the shell's diagnostics, init's restart rounds and init's
  failure-message sites pay through the era's link.
- `sh_pay_rest sh_Rsh`: "the shell's command loop body holds the line fact",
  closed by a lemma `sh_rest_holds` once the child's payload and the
  diagnostics' obligations exist inside the body. BLOCKER (endgame audit):
  `sh_pay_rest` quantifies the taint `T` internally over every `Persistent T`
  but its discharger needs `UkSh.ush_gen_slot N T`, false for arbitrary `T`.
  RULED: restate it at the application's taint (`echo_taint c`), a trusted
  change; report OLD/NEW to the owner.

The third conjunct (the shell's console read leaf) was CLOSED by IO-LEAF M5b.
`Hphi` was closed by ECHO-OUT part 5. The audit is the same thirteen ambient
assumptions throughout (md5 `57f7327206c4b276d05035342fea8ecf`).

## 2. What is landed (one line each; details in the notes)

Application side: the console I/O claim (`EchoOut.v`: output/input claims,
window token, per-boot credential "the turn", the line/prologue choice lists
`cs`/`ps` with their bookkeeping laws `cs_len_ok`/`ps_len_ok`), wired into the
record (`AppEcho.v`); the link law `EchoLinks.echo_links` (six persistent
links: write, block-first, prologue-choice, taint, read, read-taint); the
credential at an arbitrary line boundary and an arbitrary round's banner
(`wr_pro`/`wr_blk`/`wr_open`/`wr_ban` with their steps, M6a).

Kernel rows (all facts about the C, all landed): the short console write says
which byte was unreadable (T1); the read's -1 says "negative count or killed"
and a process that resumes knows it was not killed, so a read at an open
readable console fd never returns -1 (T2); at a killing-cause trap the
process offers deposit AND resume additively, and a deliberate fault pays
from a linear resource (T3 + the engine statements); a null-pointer wait's -1
says "no children or killed" (T4), the pid registration carries the range
(T4(c)), wait's reaping arm names the caller's own child (T4(b)), a process
can name its own pid (B1a), init's pid is the literal 1 (B1b); fork's failure
returns the parent's lend (FORK-REFUND); dup's reasons on both arms (DUP-ROW);
the write leaves tie the process's view to the caller's buffer, writable and
text halves (M1(d), TXT-ROW). THE KERNEL ROWS ARE COMPLETE; nothing kernel-side
is scheduled.

Program side (IO-LEAF): init's banner paid from the credential at EVERY round
through a persistent conversion, fds 1-2 pinned (M1, M6a(2)); echo's four
writes through the link (M2); the shell on the real fork/wait leaves, its
child forked at a chosen payload, the child's death paying with a resource
(M3a, M3b(1), M3c); the shell's prompt through the link at every boundary
(M4a, M6a(1)); the diagnostics tower carrying a per-call obligation, no
payment yet (M4b(1)); the shell's read on the era's link with the credential
riding the console lease, the third conjunct closed (M5a/b); the shell's
`gets` reading the era's line and the body handed the line fact (M5(3)).

Last trusted diff (M6a(2)b): `UInitKernel.init_boot_pay T Cns cn stc Rt Bn Rd
:= init_cons_dance_all T Cns stc ∗ ucons_reader cn 0 ∗ Rd 0 ∗ Bn ∗ □ (∀ N', Bn
-∗ UkInitMain.kinit_banner0 N' stc Rt)` (was without `Bn` and the conversion);
`kinit_round0 Bn := Bn ∨ True`; `Rt` stays (the prompt pair). `echo_Hinit_boot`
and `Hsh_owed` untouched.

## 3. The two findings that decide the next lane's shape (IO-LEAF handover)

(a) `die_dw` ("init: wait returned an error") CANNOT be deleted, contrary to
the audit's hope: the -1 reason is `⌜nullst = false⌝ ∨ ⌜cs = ∅⌝ ∨ kill_shot gn`;
the first two arms die (init's set is non-empty; `nullst` is exposed by
`uwait_ans_at`), but a KILLED init is real — a killed process runs on to its
next trap and does print. Deleting the arm needs a kernel row relating the
shot to the taint (candidate: `SpecSetkilled` returns `□ (kill_shot gn -∗
riscv_kill_cred)` since the killer presented Q(-1) = init's payload at -1
whose only arm is the taint — a design question for the next kernel lane; K1's
taint route then pays the arm). All three die arms stay for M6b.

(b) A SHAPE MISMATCH ACROSS THE FORK: what init LENDS is the credential at the
round's prompt (`wr_pro`), what a child HANDS BACK is the credential at the
next round's banner (`wr_ban`) — different propositions at the same count,
and `Rd` is one family used in both directions. So the placeholder-free shape
is `Rc ≠ Q (-1)` (D8(iii)'s ruling): `Rc` = the pieces plus the prompt
credential; `Q` = `ucons_pay cn γ T Rd` with `Rd` carrying the banner
credential; `uinit_lend` minting the pair across the two shapes (UserConsole);
D3's unbundling of `ush_at` following (the loop keeps the pieces; the payload
is assembled only where sh exits or forks). The handover's FOUR-STEP order:
(1) `ush_mid` + `E_lb`; (2) the `Wc`/`Wc'` routing (`ush_prompt_law` is
ALREADY PROVED = `ksh_w_of_link_prompt` at the boundary index; only routing);
(3) `Rc ≠ Q (-1)` + the two diagnostics through the link, after which every
`∨ True` arm is dead and dropped; (4) M3b core and the wait redemption on
TRAP-ROWS-5's `_pid` rows (`wp_kshr_wait`'s `_pid` twin owed in UkShRun.v).

## 4. What remains, in order

1. IO-LEAF next milestone = the four steps above (the handover
   `io-leaf-handover.md` is exact; the brief `brief-io-leaf.md` v9 + a new
   scope block on the same mould). Serialise with M4b(2): they collide on
   UkShDiag/Run/Fork/Main/Echo.  STEPS 1-2 LANDED 2026-09-14 (`a43341d28`,
   `b39fd4d48`; app-echo.md's M6a(3) note); steps 3-4 remain.  SH-LINE R3
   (item 5) is NOT a side task: see app-echo.md's "SH-LINE R3 SURVEYED".
2. M6b: init's restart loop — round k > 0's banner is already payable at the
   landed law and waits only for a credential at the restart head (a child's
   exit payload carrying `wr_ban`, step 3 above); `die_df`/`die_de` through
   `echo_link_pro` at a = 2 / 1; `die_dw` per finding (a).
3. M4b(2): the diagnostics' payment — `UkShRun.ush_diag_leaf`'s shape carries
   the obligation; the parser pins the `%s` token (`echo_key_args_holds` is
   the mould); "open %s failed" and "cannot cd %s" are REFUTED, not paid;
   `ksh_w_of_closed` from the write leaf's closed-fd arm (RULED).
4. Delete `sh_deps` from `Hsh_owed` once the four leaves are off the law.
5. SH-LINE R3: `sh_pay_rest` restated at the application's taint (RULED),
   `sh_rest_holds` closes it (collides with init-side work only in UInitSh.v).
6. The closed theorem; a final trusted-surface document (successor to
   `trusted-surface-2026-09-16b.md`, same structure); then the post-Qed
   redesign per `post-qed-redesign.md` (its three owner questions first).

## 5. Rulings of record (owner's, verbatim where possible)

- "the ring doesn't matter, it's internal to the kernel. what matters ... at
  the syscall boundary, is ownership of the UART input/output resources (and
  fupd's to update them)."
- The kill credential is the target's exit payload at -1; "require that taint
  implies Q, persistently"; the fork-child wand `□ (riscv_kill_cred -∗ Q (-1))`.
- "there's no per-cycle form. once we get taint in one era, it's tainted
  forever." (`echo_phi := fun _ h => disc h -> Forall good_out (cycles_of h)`)
- Era index by generation number.
- "q1: yes, allow these errors in the top-level trace theorem" (init's
  failure messages as prologue rounds). "q2: yeah, let's fix the specs for
  short writes" (T1). "on page fault, the process should provide these two
  facts ... separated by separation-logic AND" (T3). "agreed with fixing the
  console read spec to never return -1 to userspace" (T2).
- "if some process kills sh, sh's getcmd is not going to run. it's killed."
- The window token and the per-boot credential on the record are accepted
  "for the time being"; POST-QED REDESIGN: what an application is; a single
  IO invariant (design page written; the redesign itself after Qed).
- Explanations to the owner in plain CSL/xv6 terms, every term defined; every
  trusted-statement change reported OLD/NEW.
- 2026-09-16: no more workers/subagents; checkpoint on quiescence.
  SUPERSEDED 2026-09-14 (later session): "use subagents to run tasks in
  parallel, to the extent that you have multiple independent things".
- 2026-09-14: THE BANNER IS OPTIONAL in the transcript ("it's not
  important ... a trace without a banner in a given era has to be possible
  anyway") -- a banner-less prologue round is admitted (PROLOGUE-ALTS-3);
  no kernel row for init's console open.

Coordinator's rulings of record (2026-09-16): route B for the read leaf
(owed, then closed); the credential crosses as "an opaque resource plus a
persistent conversion" built once at the top (`echo_Hinit_boot`) — the
programs name nothing of the era; the credential rides the console lease's
`Rd` slot; no affine `∨ True` placeholders in the lease (ruling A for M6a);
init's pid pinned to the literal 1 via the one-shot mirror on the counted
regime; `sh_pay_rest` at the application's taint; `ksh_w_of_closed` from the
closed-fd arm; `Rc ≠ Q (-1)` across the fork (finding (b)).

## 6. Procedure (never skip)

Checkouts: `/shared/xv6iris-2` (main; IO-LEAF's lane `lane/io-leaf` = main),
`-disc`, `-sup`, `-tlw` (all free), `-notes` (the ONLY place notes are
committed; landings that need a cherry-pick are pushed from here). VM trees
`/mnt/rocq/trees/_shared_xv6iris-2*` via `./gcp-rocq/run-on-gcp`; build with
`./gcp-rocq/vmbuild.sh <tree> <log>` FROM THE REPO ROOT, one build per tree at
a time; a run-on-gcp sync IS a build (it drops every dirty .vo; rebuild a
touched dependency with `make -f CoqMakefile -j8 A.vo` on the VM before
`rocq-warm check B.v`); never start a build before the previous log has its
`EXIT=` line; never pattern-kill; never push from a lane checkout except
`git push origin <lane>:main` after the gate.

The gate before landing: (1) the lane sits on the current origin/main, or
behind it by notes-only commits (then cherry-pick from `-notes` and check
`git diff <lane> HEAD -- iris` is empty); (2) local md5 of every changed
iris/*.v equals the VM tree's; (3) the confirming build's log has `EXIT=0`
and zero `^Error`; (4) VM `make -f CoqMakefile -n` prints no `ROCQ compile`;
(5) `make audit-only 2>&1 | grep -v '^make\|^cd ' | md5sum` =
`57f7327206c4b276d05035342fea8ecf`; (6) `python3 tools/lemma_diff.py --ref
origin/main` with every GONE/CHANGED justified; (7) no `Admitted`; (8)
`./gcp-rocq/run-on-gcp --check-dumps` clean. Commit author `Nickolai Zeldovich
<nickolai.zeldovich@gmail.com>` (the checkouts' config; never `-c user.email`).
After landing: the as-landed note in `claude-notes/projects/app-echo.md`
(from `-notes`), the lane list updated, memory updated.

Rebase recipe when main moves under a lane: `git diff HEAD -- iris/ > p.patch`
(`git apply --3way` STAGES its result, so plain `git diff` afterwards shows
only later edits), `git checkout HEAD -- <paths>`, `git merge --ff-only
origin/main`, `git apply --3way p.patch`; never stash or reset.

Agent hygiene (when spawning resumes): briefs name the checkout, the reading
list (handover first), the allow/deny file lists, the milestone order, the
gate; agents stop green and report with the trusted diff verbatim; a Fable
reviewer before ruling on a lane that reports problems; a bare `{!ctokG Σ}`
beside `xv6G Σ` is a second camera (copy UInitBanner's/UShOut's context list);
`read_ret T k v n ws` has no γ; `echo_write_link_taint T γ`.

## 7. Documents (copies in `claude-notes/projects/handoff-2026-09-16/` (the session scratchpad `/tmp/claude-0/-shared-xv6iris-2/67f6490d-c29c-49bf-8c51-e37c71ee39df/scratchpad/` may not survive))

- Owner's review documents: `trusted-surface-2026-09-14.md`,
  `trusted-surface-2026-09-16.md`, `trusted-surface-2026-09-16b.md` (all sent).
- Design pages: `e5-design-page.md` (the application claim), `brief-self-kill-2.md`
  (the kill design), `post-qed-redesign.md` (the redesign study, sent).
- Surveys/reviews: `io-leaf-survey.md`, `tasks-review-io-leaf.md`,
  `tasks-review-road-to-qed.md`, `endgame-audit.md`.
- Handovers (current): `io-leaf-handover.md` (THE one to read first for the
  next milestone), `io-leaf-diag-handover.md`, `io-leaf-fd-handover.md`,
  `trap-rows-5-handover.md` (and -3, -4, -4-B), `dup-row-handover.md`,
  `txt-row-handover.md`, `fork-refund-handover.md`, `prologue-alts-2-handover.md`,
  `echo-out-handover-6.md`.
- Briefs: `brief-io-leaf.md` (v9 + every milestone's scope block), the others
  by lane name.
- Memory: `/root/.claude-kmit/projects/-shared-xv6iris-2/memory/app-project-lane-workflow.md`
  (the state paragraph) and `no-more-subagents-checkpoint.md`.
