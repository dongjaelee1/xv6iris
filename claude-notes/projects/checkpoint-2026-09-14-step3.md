# CHECKPOINT 2026-09-14 (session limit) -- IO-LEAF step 3 in flight

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
the main checkout on `lane/io-leaf-3` = main).  OPEN OWNER QUESTIONS: (i)
the trace predicate's WIDENING by PROLOGUE-ALTS-3 (app-echo.md's
"PROLOGUE-ALTS-3 LANDED": leave or tighten); (ii) `die_dw` (a killed init),
unchanged.

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
