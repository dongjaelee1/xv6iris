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

## 2. What is on main (origin/main = b7c49dea2 code, 17c05c746 notes)

* M6a(3) steps 1-2 (`E_lb` on the lease pieces; the `Wc` routing), WRITE-CLOSED
  (`UkWriteClosed.v`), SH-LINE-CRED (`EchoLinksLine.v`, `UShPanic.v`: the tight
  shapes `wr_tail`/`ewc_line`/`ewc_lcred`, `ewc_panic_done`,
  `sh_prompt_law_holds_line`), the `_CoqProject` strip.  Audit md5 unchanged
  (57f7327206c4b276d05035342fea8ecf); `Hsh_owed`'s text unchanged.

## 3. In flight -- three lanes and the coordinator's half

The lanes were subagents of the dead session; THEY ARE GONE with it.  Their
checkouts hold whatever they had written.  Their briefs are saved verbatim in
`handoff-2026-09-16/brief-*.md`; re-spawn each with its brief plus "your
checkout already contains a previous attempt's uncommitted edits -- inspect
`git status`/`git diff` first and continue from them".

### (a) STEP3-SH -- checkout `/shared/xv6iris-2-disc`, branch `lane/step3-sh`
Brief: `brief-step3-sh.md`; contract: `step3-interface.md`.  At the
checkpoint: uncommitted edits in UkSh.v, UShKernel.v, UShLine.v, UShOut.v,
UShPanic.v (no build yet, no report).  Deliverable: `Wb` beside `Wc` in UkSh
(`ush_wcp` with the both-console / closed / True arms, `ush_posb` over `Pm`,
`ush_at_of_pm_wb`, `ush_gets_done_0/_line` re-cut), the consumers, the entry
law `UShLine.ush_posb_of_lend`, `sh_uexec_slot`/`sh_slot_of_kexec` taking the
lend `Ql (-1)` + `ush_wcp`, `sh_prompt_at`/`sh_prompt_pay`/`ush_prompt_in`
deleted, UInitSh/UInitBoot compiling with PLACEHOLDER instantiations
(`Wb := fun _ => True`).  Report to scratchpad `step3-sh-report.md`.

### (b) The init side -- DONE, committed LOCALLY as c74734d65 on `lane/io-leaf`
in `/shared/xv6iris-2` (NOT pushed; the tree does not build until the glue).
UInitFd (`ufd_row`, `ufd_head_open_row`, `ufd_head_of_row`), UserConsole
(`uinit_lend_c`), UkInit (`init_rd_cred`, `init_rd`, `init_pay_of_lend`,
`init_lend_cred`, `init_exec_sup_pos cn T st Wc Wb Rdl γ n` at
`∀ N' m pc l, … ustd (ukn_fd N') l -∗ ufd_row T st l -∗ init_lend_cred st Wc
Wb l n -∗ upos γ n -∗ ucons_pay cn γ T Rdl (-1) -∗ udepw_at_ref …`),
UkInitMain (`kinit_ban_law stc Wc Wb`, `kinit_lent`, `wp_kinit_banner` opens
the token and returns `kinit_lent`, `wp_kinit_fork … cn l γ np …` lends
`init_lend_cred`, `wp_kinit_main_child … Wc Wb Rdl γ np l …`, every walk
lemma's binders `(Wc) (Wb Rdl) `{HRdl} `{HWb} (cn)` -- NAMED instance binders,
an anonymous second one is `H0` and clashes with the proofs' asserts),
UInitKernel (`init_boot_pay T Cns cn stc Wc Wb Rdl` -- TRUSTED, OLD/NEW in the
commit message), UInitBanner (`kinit_own_is_cred`, `kinit_ban_law_holds` at
`Wc := EchoLinks.ewc_cred T γ (S gen_id)`; `kinit_ban_any`,
`sh_prompt_pay_of_kinit_own`, `kinit_prompt_law_holds` deleted).  All six
warm-checked OK on the VM.

### (c) THE GLUE (nobody's yet) -- after (a) lands
Cherry-pick (a) onto `lane/io-leaf` (or rebase c74734d65 on it), then in
UInitSh `init_exec_sup_of_sh_slot`: take `Wb`, `Rdl` (drop the placeholder
`Rd -∗ Rdl` premise and `Rt`), conclusion `init_exec_sup_lend cn T st Wc Wb
Rdl` with `Rd := UkInit.init_rd Rdl Wb`; inside, destruct
`init_lend_cred st Wc Wb l n` per row into sh's `UkSh.ush_wcp Wc Wb (take
NSTD fdv) n 0` (l3 arm: `ush_fd0c ∧ ush_fd2p` from `st = console rw`; l0 arm:
`l !! 2 = Some FdClosed`; True); the refund arm needs `ukn_pay N' (-1)` from
the lend: `UkInit.init_pay_of_lend`.  `sh_pay_rest` quantifies `Wb` (TRUSTED:
report OLD/NEW of `Hsh_owed`'s second conjunct).  UInitBoot
`init_cons_sup_of_sh_slot` + `echo_Hinit_boot`: `Wb := UInitBanner.kinit_ban
(echo_taint γ) γ`, `Rdl := UShLine.ush_rd_pin γ`, `Wc := EchoLinks.ewc_cred
(echo_taint γ) γ (S gen_id)`, the boot payment from `kinit_ban0_of_eturn`
(`kinit_dl0` = `Rdl 0`, `kinit_ban 0` = `Wb 0`), the law from
`UInitBanner.kinit_ban_law_holds`.  Then full build, gate, land, note.

### (d) PROLOGUE-ALTS-3 -- checkout `/shared/xv6iris-2-tlw`, branch `lane/prologue-alts-3`
Brief: `brief-prologue-alts-3.md`.  Uncommitted edits in EchoDisc.v,
EchoLinks.v, EchoOut.v, EchoOutPure.v; its first full build pa3-1 was green
(EXIT=0), later warm checks pa3-c1..c3 in progress.  Deliverables: the 4th
prologue alternative ("$ " without banner), `echo_prompt_dollar_ban` (pay '$'
from the banner-owed shape), the DISCIPLINE LEMMA (an untainted read at an
unwritten prompt is refuted), `ewc_pr`'s p = 0 arm possibly widened to
`ewc_owed ∨ ewc_ban`.  Report to scratchpad `prologue-alts-3-report.md`.
Consumers in step 4: `ush_wcp_cons` at k = 2 (closed arm -> credential arm via
`Wb n -∗ Wc n 0`), `ush_gets_done_line`'s closed arm (the discipline lemma),
the top's `Wc n 0` widening.

### (e) INIT-DIAG (M6b prep) -- checkout `/shared/xv6iris-2-sup`, branch `lane/init-diag`
Brief: `brief-init-diag.md`.  New files `iris/EchoLinksPro.v`, `iris/UInitDiag.v`
(untracked) + `_CoqProject` rows; its rebased build id-4 was running at the
checkpoint (log `/tmp/id-4.log` on the VM).  It was one commit from done: gate,
commit, report.

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
