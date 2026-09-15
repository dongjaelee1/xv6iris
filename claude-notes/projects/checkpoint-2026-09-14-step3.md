# CHECKPOINT 2026-09-14 (THIRD session limit) -- step 3, INIT-DIAG, PROLOGUE-ALTS-3, M6b, step 4, RESIDUALS (A) landed; lane EXEC-SEAM was in flight

Supersedes `checkpoint-2026-09-16.md` §4/§5 for the state of play; that file's
rules (§1-§3: build procedure, gate, commit rules, how to talk to the owner)
still stand.  Read `durable-notes.md` first, then this, then
`handoff-2026-09-16/io-leaf-handover.md` ("STEP 3 -- THE DESIGN OF RECORD")
and `handoff-2026-09-16/step3-interface.md` (THE BINDING CONTRACT between the
two halves of step 3).

## 1. Owner rulings this session (all in force)

* Subagents are allowed again: "use subagents to run tasks in parallel, to the
  extent that you have multiple independent things that can be done at the same
  time without conflicts".  One checkout per lane (`/shared/xv6iris-2` = the
  coordinator, `-disc`, `-sup`, `-tlw`; VM trees `_shared_xv6iris-2*`), one
  build per tree, never pattern-kill on the VM.
* THE BANNER IS OPTIONAL in the transcript predicate (a prologue round may be
  "$ " alone; PROLOGUE-ALTS-3 implements it).  No kernel row for init's console
  open; OPEN-ROW withdrawn.  Shortest honest path to Qed is the value.
* `iris/_CoqProject`: header, bare file rows and the six descoped `# Foo.v`
  rows ONLY; no prose comments ("ditch all that useless commentary").
* Landings: `git push origin lane/io-leaf:main` after the full gate; notes only
  from `/shared/xv6iris-2-notes` (branch `notes`, `git push origin HEAD:main`).
* 2026-09-14 (later): THE WEAKER TRACE PREDICATE IS ACCEPTED FOR NOW --
  "the weaker trace predicate seems alright for now; let's land it first and
  then we'll go back and clean things up and possibly strengthen it".  So
  PROLOGUE-ALTS-3's widening (app-echo.md, "PROLOGUE-ALTS-3 LANDED") is NOT
  an open question; tightening belongs to the post-Qed cleanup.

## 2. What is on main (origin/main = d1cc70d8b code)

FOURTH SESSION (2026-09-14, later): EXEC-SEAM (B)/(C)/(D) LANDED (`75e353efc`,
`10b399a6c`, `d1cc70d8b`; app-echo.md "EXEC-SEAM LANDED").  `Hsh_owed` is ONE
conjunct now (`⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh`); no `∨ True` in the
U tier.  Lane R3 (checkout `-sup`, branch `lane/r3`, brief
`handoff-2026-09-16/brief-r3.md`) deletes it per `r3-survey-2.md` §5/§6.
Owner ruling 2026-09-14: finish the work; no surveys, reports or owner pages
before Qed.

## 2-third. What was on main at the third checkpoint (146e7cac1)

THIRD SESSION (2026-09-14, later): M6b LANDED (`a7d47ccef`+`290f05cf0`),
IO-LEAF STEP 4 LANDED (`2426ca438`+`7da574e81`), RESIDUALS (A) LANDED
(`146e7cac1`) -- app-echo.md's notes of those names are the record; the
R3 RE-SURVEY (ruling: delete `sh_pay_rest`, discharge at the era's families
through a new `UShRest.sh_rest_holds`; report `handoff-2026-09-16/
r3-survey-2.md`); the refreshed TRUSTED-SURFACE document
`handoff-2026-09-16/trusted-surface-2026-09-14b.md` (as of 7da574e81; not yet
sent to the owner as a page -- do so).  The remaining hypothesis is still
`Hsh_owed`'s two conjuncts.

## 2-old. What was on main at the second checkpoint (b65275c81)

* M6a(3) steps 1-2, WRITE-CLOSED, SH-LINE-CRED, the `_CoqProject` strip,
  INIT-DIAG (`bdd9faf7f`), IO-LEAF STEP 3 (`a583457a6`, `a860c399d`,
  `eab906990`) and PROLOGUE-ALTS-3 (`…b65275c81`, three commits) -- the
  "LANDED" notes of 2026-09-14 in app-echo.md are the record; three trusted
  changes (`init_boot_pay`, `sh_pay_rest`, EchoDisc's `pro_alts`/`pro_of`),
  OLD/NEW in the notes and the commit messages.  Audit md5 unchanged
  (57f7327206c4b276d05035342fea8ecf); `Hsh_owed`'s text unchanged.

## 3. In flight -- STEP 4 (launched 2026-09-14, third session)

Two lanes, spawned from the coordinator's main checkout (`lane/io-leaf-3`):
* STEP4-SH -- LANDED (`2426ca438`+`7da574e81`, app-echo.md "IO-LEAF STEP 4
  LANDED"); `-disc` is free again.
* M6B-INIT -- LANDED (`a7d47ccef`+`290f05cf0`, app-echo.md "M6b LANDED");
  `-sup` is free again.
* RESIDUALS -- (A) LANDED (`146e7cac1`), (B) BLOCKED at the exec seam
  (app-echo.md "RESIDUALS (A) LANDED; (B) BLOCKED").
* EXEC-SEAM in `-disc`, branch `lane/exec-seam` (WAS RUNNING at the third
  session limit -- DIED with the session; its checkout may hold uncommitted
  edits: `git status`/`git diff` in -disc first, then re-spawn with the saved
  brief plus "continue from the previous attempt's edits"): (B) the exec seam
  carries `uvis_ch`/`uvis_pid` (kernel contract text changes: pure rows,
  reflexive at the discharge), (C) the kills, (D) the free law
  taint-conditional + `Hsh_owed`'s first conjunct deleted; brief
  `brief-exec-seam.md`, report `exec-seam-report.md`.  R3 follows it.
* R3-SURVEY -- DONE (app-echo.md "SH-LINE R3 RE-SURVEYED"): RULED to delete
  `sh_pay_rest` and the second conjunct and discharge at the era's families
  through a new `UShRest.sh_rest_holds`; lane R3 follows RESIDUALS.
* TRUSTED-SURFACE in `-tlw` (READ-ONLY): the refreshed trusted-surface
  document as of 7da574e81; brief `brief-trusted-surface.md`, report
  `trusted-surface-2026-09-14b.md`.
Both step-4 lanes could touch UInitSh.v/UInitBoot.v minimally; the coordinator merges those
two files by hand, then the one-line kill of `UkInit.init_rd_cred`'s `∨ True`
once the shell's exits all hand back `Wb n`.  If this session dies: the lanes
die with it; their checkouts keep the uncommitted edits; re-spawn with the
saved briefs plus "inspect git status/diff first and continue".

## 3-old. (before the launch) In flight -- nothing

All lanes have landed; every checkout is free (`-disc` on `lane/step3-sh`,
`-tlw` on `lane/prologue-alts-3`, `-sup` on `lane/init-diag`, all merged;
the main checkout on `lane/io-leaf-3` = main).  NO OPEN OWNER QUESTION.
The predicate widening is RULED (§1).  `die_dw` is NOT a question but an
M6b work item (owner, 2026-09-14: "how can a killed init print anything?"
-- it cannot): see app-echo.md "DIE-DW CORRECTED".

## 3b. Where the next agent starts

Read `durable-notes.md`, this file, then app-echo.md's four 2026-09-14
"LANDED" notes (INIT-DIAG, IO-LEAF STEP 3, PROLOGUE-ALTS-3, and M6a(3) STEPS
1-2) and `handoff-2026-09-16/io-leaf-handover.md` ("THE REST OF THE LANE").
The one remaining hypothesis of the top theorem is `Hsh_owed`
(`UInitBootAdequacy.v`): `⊢ sh_deps` (the free console-write law, spent at
four leaf families: the prompt's affine arm in `UkSh.ksh_w_of_wcp`, the
shell's diagnostics `UkShDiag.ksh_w1_of_law`, init's die arms
`UkInit.kinit_w1_of_law`, the echo child's generic entry in `UShEcho`) and
`⊢ sh_pay_rest sh_Rsh` (the rest-of-line obligation; R3's three
prerequisites, app-echo.md "SH-LINE R3 SURVEYED").  Order of work is §4
below; step 4 first.  Spawn lanes on the four free checkouts with briefs on
`handoff-2026-09-16/brief-*.md`'s mould (checkout, reading list, allow/deny
files, build procedure, gate, report shape); a lane that starts a detached VM
build and ends its turn does not wake on completion -- poll its `<log>.out`
for `EXIT=` and message it.  Rebase recipe and gate: `checkpoint-2026-09-16.md`
§6.  Landings from `-notes` by cherry-pick when the lane is behind main by
notes-only commits (`git diff <lane> HEAD -- iris` must be empty).

## 3c. Where the FOURTH session starts

1. `cd /shared/xv6iris-2-disc && git status --short` -- if lane EXEC-SEAM
   left uncommitted edits, re-spawn it (brief `brief-exec-seam.md`) telling
   it to inspect and continue; if it committed (B)/(C)/(D) on
   `lane/exec-seam`, land by cherry-pick onto main (recipe: `git fetch
   /shared/xv6iris-2-disc lane/exec-seam:refs/remotes/disc/exec-seam` in the
   main checkout, cherry-pick, `git diff <lane> HEAD -- iris` empty, push
   `lane/io-leaf-3:main`; the lane's gate ran on the identical tree).
2. Then lane R3 (brief on the mould of the others; the plan is
   `r3-survey-2.md` §6: `ush_gen_slot` and the wb-assembler into
   `ush_rest_l`'s box, the fork's taint arm to the generic slot through
   `ush_gen_run`, new `UShRest.v` (`sh_rest_holds`), `sh_pay_rest` DELETED and
   `Hsh_owed`'s second conjunct with it -- TRUSTED, OLD/NEW).
3. Then the closed theorem: `Hsh_owed` gone; consider a second audit target
   for the echo theorem (trusted-surface §4 recommends one) and the
   corollary at the literal image (§2.2); refresh the trusted-surface
   document once more; send it to the owner.
4. Post-Qed: the predicate tightening; init's closed-ledger arms off the
   free law.

## 4. Then (unchanged plan)

Step 4 = M3b core + the wait redemption + PROLOGUE-ALTS-3's two lemmas
consumed -> every `∨ True` named in `step3-interface.md` dies
(`UkInit.init_rd_cred`, `init_lend_cred`'s third arm, `UkSh.ush_wcp`'s third
arm); M6b (init's diagnostics through the link, INIT-DIAG's files);
M4b(2); delete `sh_deps`; SH-LINE R3 (three prerequisites, serialised after
M3b core); the closed theorem; the trusted-surface document; the post-Qed
redesign.  M6b includes DELETING `die_dw`: init's wait moves to the `_pid`
twin (`UkRunSys.wp_uk_ecall_wait_null_pid`, whose -1 row is `Sc' = ∅`) and
the arm is refuted against init's live child token (app-echo.md "DIE-DW
CORRECTED"); the same twin is what the shell's wait redemption takes.
