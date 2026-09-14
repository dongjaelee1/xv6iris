# lane TRAP-ROWS-4 -- handover (in progress)

Checkout `/shared/xv6iris-2-tlw`, branch `lane/trap-rows-4`, rebased onto
`origin/main = 212d0aec7` (IO-LEAF M4b(1)).
Build logs `tr104`..`tr109` used; **next free `tr110`**.

MILESTONE A IS COMMITTED AND GREEN: `5f04889b0`, 29 files, +1115/-174.
Gate (tr108 full / tr109 confirming, both `EXIT=0`, zero `Error`):
`make -f CoqMakefile -n` prints 0 `ROCQ compile`; audit md5
`57f7327206c4b276d05035342fea8ecf`; `lemma_diff --ref origin/main` CLEAN
(nothing dropped, nothing admitted, no new assumption); no
Admitted/admit/Abort and no Axiom/Hypothesis in the diff;
`run-on-gcp --check-dumps` clean.  NOT a statements-only pass -- every
proof is closed.

## WHAT IS WRITTEN (milestone A, commit `40dafc428`)

### (e) THE BOOT END -- the part the previous lane never wrote
* `WaitInv.children_boot` SPLIT: `children_boot := init_pid_tok 0 ∗
  children_boot_rows` (+ `children_boot_split`).  `ProofMain` splits at its
  TOP level (`wp_main_boot_sconf`), hands `mn_grp_kvm` only
  `children_boot_rows` and routes `init_pid_tok` to `mn_grp_fs` (the group
  that calls userinit at main+0x9e).  `SpecMain`'s premise does not move.
* `SpecUserinit` gains the premise `SlotGen.init_pid_tok 0` beside the
  <initproc> cell; its post's `∃ v, initproc ↦₈□ v` becomes
  `∃ v, initproc ↦₈□ v ∗ ∃ p0, WaitInv.init_gen v p0` (main drops it -- the
  continuation's arity does not move).
* `ProofUserinit` DISCARDS instead of dropping: `slot_gen_persist` on
  init's 3/4 and `pid_reg_persist` on its 3/4, then
  `init_pid_set`/`init_pid_seal` at the pid allocproc returned, then
  `WaitInv.init_gen (proc_addr j) pid`.  NOTE FOR THE LANDING NOTE:
  `slot_gen ip (DfracOwn 1)` is now forever unobtainable at <init>'s slot
  (allocproc can never re-key it, freeproc can never deregister its pid).
  True -- init never exits, kexit panics on it -- nothing needs the converse.
* `UsertrapRes.ut_names` gains the PURE field `un_ipid : mword 32`;
  `ut_caps` and `ut_park_caps` gain `WaitInv.init_gen (un_ip N) (un_ipid N)`
  (CONTEXT-FREE -- the cell half is not in the record, the resumer gets its
  own from `park_globals`), and `ut_caps` also gains
  `⌜un_dqi N = DfracDiscarded⌝` (new `ut_caps_init` projects both).
  `SyscParkEnv.park_world`'s initproc row becomes the PAIR
  `∃ ip p0, initproc ↦₈□ ip ∗ init_gen ip p0` so a forked child's record can
  inherit both (`ProofKforkB5`); `ut_caps_of_park` re-pairs at the resumer's
  context through `ctx_word_pointsto_agree`.

### (a) THE KERNEL ROW AT NUMBERS
* `UserChildren` is now THREE sections: `GenIsInit` (`wchG`, the ghost
  reading `gen_is_init`), `WaitAns` (`ctokG` ONLY -- `wait_ans` mentions no
  ghost, so NO U-tier file needs `wchG`), and `WaitAnsGen` (both).
* `wait_ans rv xs cs cs' gn nullst pidv ip` -- two PURE `mword 32`
  parameters; the reaping arm's new conjunct is `⌜γ' ∈ cs \/ pidv = ip⌝`.
* `wait_ans_gen` is the SAME answer at the GHOST (`⌜γ' ∈ cs⌝ ∨ gen_is_init
  gn`); kwait's eleven internal block lemmas are stated at it and
  `wait_ans_of_gen` takes the step across ONCE, at `wp_kwait_sconf`'s own
  exit, out of `ChildTok.gen_pid` (off the block, new
  `ProcInv.proc_priv_slot_gen` third component) and `SlotGen.init_pid_is`
  (kwait's new contract premise).  So NOTHING inside ProofKwait threads a
  pid.
* `SpecKwait` / `SpecSysWait` gain `(ipid : mword 32)` + the persistent
  premise `SlotGen.init_pid_is ipid`.
* `SpecSyscall.sysc_init_id dqi ip := initproc ↦₈{dqi} ip ∗
  WaitInv.init_ident ip` REPLACES the bare cell row at the syscall layer
  (one row, so the 20 arms that only frame it do not move); the wait arm
  reads `init_pid_is` out of it, the exit arm reads the DISCARDED cell and
  `init_ident` out of it for kexit's reparent.
* `sysc_wait_out U r cs cs' pidv` and `ut_wait_out … gn pidv` close `ip`
  existentially (the U tier cannot name it until milestone B); `pidv` is
  the caller's own pid, real all the way to the usertrap boundary.

### (b) `uwait_ans` KEEPS ITS ARITY
`UexecRet.uwait_ans_at r cs cs' gn b pidv ip`, new
`uwait_ans_pid r cs cs' pidv ip := ∃ gn b, …`, and
`uwait_ans r cs cs' := ∃ pidv ip, uwait_ans_pid …`.  `UkInit.wp_kinit_wait`,
`UkShRun.wp_kshr_wait`, `UkRunSys.wp_uk_ecall_wait_null{,_live}` DO NOT MOVE.
`UkInitMain.v`: exactly THREE intro-pattern lines (`(gnw bnw rv xs)` ->
`(pidw ipw gnw bnw rv xs)`, and two reaping-arm patterns gain one `_`).

### (d) NOT WRITTEN -- AND THERE IS AN OPEN QUESTION IN THE RULING
See "MILESTONE B'S OPEN QUESTION" below.

## MILESTONE B'S OPEN QUESTION (for the coordinator)

The fork half of (d) IS well-defined: `wp_uk_ecall_fork` CHOOSES the child's
record (the program's obligation is `∀ N' h', …`), so UkFork can set
`ukn_ipid N' := ipK` for whatever number the KERNEL's fork answer carries,
and `⌜pidc <> ukn_ipid N'⌝` follows.  That needs SpecKfork/SpecSysFork/
SpecSyscall's fork row to report `⌜pidc <> un_ipid N⌝`, refuted at
allocproc's registration INSERT against `WaitInv.init_gen`'s
`pid_reg p0 DfracDiscarded g` (already in the record, and
`WaitInv.init_gen_reg_ne` is written and ready).

The WAIT half is NOT: `wp_uk_ecall_wait_null_live` gets its answer from
`uslot W`'s wait row (`UexecRet.uexec_wait_F`), which is indexed by `W :
uvis` ALONE.  For the leaf to hand the program `⌜p = ukn_ipid N⌝` the number
has to be in `uslot`'s own index -- i.e. a `uvis` FIELD or an extra
parameter of `uslot` -- because the constructor receives that row in a
NEGATIVE position and cannot pin an existential the kernel chose.  A
parameter of `uslot_of_urun*` does not reach it.  So ruling (c)'s "NOT a
`uvis` field" and "the leaf hands the program the disjunct" cannot both
hold; one of them has to give.

## THE EXACT B LINES (entry constructors), once the ruling lands

Each of these is ONE `iApply (uslot_of_urun* W … )` that would gain the
`ip` argument, and ONE `iIntros (N h) "…"` in the same proof that would
gain the `upid (ukn_pid N) p` fragment:

  * `UShKernel.v:584`  (inside `sh_slot_of_kexec`, `uslot_of_urun_all`) --
    plus `UInitSh.v:1108`'s `pose proof (sh_slot_of_kexec …)` if the
    bridge's arity moves.
  * `UInitKernel.v:360` (`uslot_of_urun_all`)
  * `UEchoKernel.v:456` (`uslot_of_urun_ro`)
  * `UEchoOut.v:794`    (`uslot_of_urun_ro`)
  * `USyncKernel.v:182` (`uslot_of_urun`)

NONE of these is in the new IO-LEAF agent's allow-list (UkSh, UShLine,
UkShLoop, UkShFork, UkShRun, UkShEcho, UkShMain, UShEcho), so B can take
them; `UInitSh.sh_slot_of_kexec` is the one file IO-LEAF may touch "if
forced", so whoever lands second rebases.

A CHEAPER ROUTE THAT TOUCHES NONE OF THEM: give `uslot_of_urun*` a `_ip`
TWIN that takes the number (T4(c)'s corollary trick) and leave the five
old names in place; the constructors switch over one at a time.

## RULES IN FORCE
Build only `./gcp-rocq/vmbuild.sh xv6iris-2-tlw <log>` from
/shared/xv6iris-2-tlw; one at a time; a sync IS a build; never pattern-kill;
never push; commit by explicit path; author
`Nickolai Zeldovich <nickolai.zeldovich@gmail.com>` (the checkout's config).
