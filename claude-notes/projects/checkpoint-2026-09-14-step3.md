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

## 2. What is on main (origin/main = eab906990 code)

* M6a(3) steps 1-2, WRITE-CLOSED, SH-LINE-CRED, the `_CoqProject` strip,
  INIT-DIAG (`bdd9faf7f`: `EchoLinksPro.v`, `UInitDiag.v`), and IO-LEAF STEP 3
  (`a583457a6` init side, `a860c399d` shell side, `eab906990` the glue) --
  app-echo.md's "INIT-DIAG LANDED" and "IO-LEAF STEP 3 LANDED" notes are the
  record (two trusted changes, OLD/NEW there and in the commit messages).
  Audit md5 unchanged (57f7327206c4b276d05035342fea8ecf); `Hsh_owed`'s text
  unchanged.

## 3. In flight -- one lane

### PROLOGUE-ALTS-3 -- checkout `/shared/xv6iris-2-tlw`, branch `lane/prologue-alts-3`
Brief: `brief-prologue-alts-3.md`; reports `prologue-alts-3-report.md` and
`-report-2.md` (in the coordinator's scratchpad until landed, then in
`handoff-2026-09-16/`).  DONE AND GREEN on `9a1d2e638` (commits `da61f6275`,
`fcd6e6c08` = new `EchoLinksBan.v`, `5612d819d` = the EchoLinksPro fix); the
lane is rebasing onto `eab906990` (re-applying its three one-line fixes in
UShLine.v/UShOut.v/EchoLinksLine.v), full build pa3-5, gate, report-3.
Then the coordinator cherry-picks it from `-notes` and lands.

TRUSTED DIFF IT CARRIES (EchoDisc): the banner becomes a fourth prologue
LETTER (`pro_alts := [u_prompt; u_execfail; u_forkfail; u_banner]`,
`pro_cont a := a = 1 \/ a = 3`, `pro_of [] = []`, `pro_of (a :: ps') =
pro_alts !!! a ++ pro_more a (pro_of ps')`, `pro_done ps := Exists (fun a =>
~ pro_cont a) ps`); `expected_rel`/`disc_pt` textually unchanged.  Good run
`[3;0]`, banner-less `[0]`, exec failure + restart `[3;1;3;0]`, fork failure
`[3;2]`.  OWNER QUESTION (report it): the predicate is WIDER than the ruling's
literal shape -- it admits every word in {1,3}*{0,2} per round, e.g. `[3;3;0]`
(two banners) and `[1;0]` (exec diagnostic without a banner), which the
machine never produces.  Sound (weaker theorem, not vacuous: anti-vacuity
witnesses `demo_*` for all five machine transcripts), and the lane's reason
for the shape is that a writer's knowledge of `ps` is a persistent LOWER
BOUND, so `pro_of` must be monotone -- a default banner at `pro_of []` breaks
every link stated at a bound.  Tightening = a well-formedness conjunct on
`ps` through `pro_ok` plus a premise on `echo_link_pro`; the owner decides
whether it is worth doing.  What step 4 receives: `EchoLinks.echo_prompt_
dollar_ban` / `EchoLinksBan.echo_prompt_dollar_ban` (pay '$' from the
banner-owed shape), `EchoLinks.ewc_owed_read_taint` / `EchoLinksBan.ewc_line_
read_taint` / `ewc_ban_read_taint` (an untainted read at an unwritten prompt
is refuted), `ewc_ban_owed`/`ewc_ban_line` (collapse the top's disjunction).

## 4. Then (unchanged plan; PROLOGUE-ALTS-3 lands first)

Step 4 = M3b core + the wait redemption + PROLOGUE-ALTS-3's two lemmas
consumed -> every `∨ True` named in `step3-interface.md` dies
(`UkInit.init_rd_cred`, `init_lend_cred`'s third arm, `UkSh.ush_wcp`'s third
arm); M6b (init's diagnostics through the link, INIT-DIAG's files);
M4b(2); delete `sh_deps`; SH-LINE R3 (three prerequisites, serialised after
M3b core); the closed theorem; the trusted-surface document; the post-Qed
redesign.  Owner question still open: `die_dw` (a killed init) -- narrow the
free law to that one arm or reopen kernel rows (`open-row-survey.md` is the
map if reopened).
