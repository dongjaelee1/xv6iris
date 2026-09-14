# CHECKPOINT 2026-09-14 (second session limit) -- step 3, INIT-DIAG, PROLOGUE-ALTS-3 landed; nothing in flight

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

## 2. What is on main (origin/main = b65275c81 code)

* M6a(3) steps 1-2, WRITE-CLOSED, SH-LINE-CRED, the `_CoqProject` strip,
  INIT-DIAG (`bdd9faf7f`), IO-LEAF STEP 3 (`a583457a6`, `a860c399d`,
  `eab906990`) and PROLOGUE-ALTS-3 (`…b65275c81`, three commits) -- the
  "LANDED" notes of 2026-09-14 in app-echo.md are the record; three trusted
  changes (`init_boot_pay`, `sh_pay_rest`, EchoDisc's `pro_alts`/`pro_of`),
  OLD/NEW in the notes and the commit messages.  Audit md5 unchanged
  (57f7327206c4b276d05035342fea8ecf); `Hsh_owed`'s text unchanged.

## 3. In flight -- nothing

All lanes have landed; every checkout is free (`-disc` on `lane/step3-sh`,
`-tlw` on `lane/prologue-alts-3`, `-sup` on `lane/init-diag`, all merged;
the main checkout on `lane/io-leaf-3` = main).  ONE OPEN OWNER QUESTION:
`die_dw` (a killed init prints "init: wait returned an error", which no
transcript admits) -- narrow the free law to that one arm, or a kernel row
relating the kill shot to the taint (`open-row-survey.md` is the map if
kernel rows reopen).  The predicate widening is RULED (§1), not open.

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

## 4. Then (unchanged plan)

Step 4 = M3b core + the wait redemption + PROLOGUE-ALTS-3's two lemmas
consumed -> every `∨ True` named in `step3-interface.md` dies
(`UkInit.init_rd_cred`, `init_lend_cred`'s third arm, `UkSh.ush_wcp`'s third
arm); M6b (init's diagnostics through the link, INIT-DIAG's files);
M4b(2); delete `sh_deps`; SH-LINE R3 (three prerequisites, serialised after
M3b core); the closed theorem; the trusted-surface document; the post-Qed
redesign.  Owner question still open: `die_dw` (a killed init) -- narrow the
free law to that one arm or reopen kernel rows (`open-row-survey.md` is the
map if reopened).
