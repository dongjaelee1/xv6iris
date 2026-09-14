# lane TRAP-ROWS-5 -- B1b LANDED

Checkout `/shared/xv6iris-2-tlw`, branch `lane/trap-rows-5`, commit
`1a7682370` on `origin/main = a72323b79` (IO-LEAF M6a(1)).  43 files
+1035/-296.  Builds `tr115`..`tr121` in `-tlw`; next free `tr122`.
STOPPED GREEN, working tree clean, no build owed.  NOT PUSHED.

## GATE (tr120 full, tr121 confirming after the rebase; both EXIT=0, zero Error)
* `make -f CoqMakefile -n` prints 0 `ROCQ compile`
* audit md5 `57f7327206c4b276d05035342fea8ecf` (the thirteen, unchanged)
* `lemma_diff --ref origin/main` CLEAN (nothing dropped/admitted, no new
  assumption) -- so NOTHING to justify
* no `Admitted`/`admit`/`Abort`, no new `Axiom`/`Hypothesis` in the diff
* `run-on-gcp --check-dumps` clean

## THE TWO CHECKS, ANSWERED
1. userinit's park does NOT hold <pid_lock> when it seals the ledger
   (`ProofUserinit` ~line 819, long after allocproc released it).  It does
   not have to: the encoding below re-establishes the payload INSIDE
   allocproc, at its own store, so the seal is lock-free.
2. A failing allocproc: the C scans for a free slot FIRST and calls the
   inlined allocpid only at `found`, so the NO-SLOT arm never touches
   <nextpid> -- its ledger comes back UNMOVED, index and all
   (`procs_avail_at op tk`).  The two freeproc TAILS run after allocpid,
   so theirs comes back with the boot token spent (`pav_spent op`).

## THE ENCODING (it resolves the hole the B handover flagged)
The mirror is a ONE-SHOT, not an exact value.  An exact-value mirror has
to be updated by every party that bumps the counter and updating a
two-half ghost needs BOTH halves, so a caller WITHOUT the tracked half
could not move the payload off the tracked side at all.  A one-shot
inverts it: the UNTRACKED side is the persistent one, hence free.
* `SlotGen.nextpid_pend` / `nextpid_shot` at a second `wchG` gname
  (`Xv6Cameras.npid_name`, reusing `ipidUR` -- NO new functor), with
  `nextpid_shoot` / `nextpid_pend_shot`; `SlotGen.init_reg :=
  ∃ g, pid_reg 1 DfracDiscarded g` and `init_reg_ne`.
* `PidLock.nextpid_res_at` gains TWO marks, each `<boot fact> ∨ shot`:
  `⌜bv_unsigned v = 1⌝` beside the counter and
  `⌜Forall (fun q => bv_unsigned q <> 1) pids⌝` beside the 64 values.
  The second is what KILLS allocpid's RETRY branch in the boot era.
  freeproc's `p->pid = 0` preserves it (0 <> 1) and every other lock user
  hands back the disjunct it received -- no other contract moves.
* `ProcAvail`: `pav_core` (the old authority), `npid_done := shot ∗
  init_reg`, `procs_avail_at on t`, `procs_avail on := ∃ t, ...` (ARITY
  UNMOVED, `None` still persistent), `pav_boot`, `pav_spent on := core ∗
  shot`, `pav_of_spent`, `procs_avail_seal_spent`, `procs_avail_at_None`,
  `pslot_mint_core`, `pav_spent_mint`.  `procs_avail_alloc` now yields
  `pav_core` only; the boot pairs it with the token
  `WaitInv.children_res_alloc` mints (BootShared ~2120).

## THE LINES OUTSIDE THIS LANE'S OWN FILES (one each)
  `UShKernel.v:606`, `UInitKernel.v:368`, `UEchoKernel.v:455`,
  `UEchoOut.v:793`, `USyncKernel.v:181` -- the
  `(mword_of_int 0 : mword 32)` argument of `uslot_of_urun*` DELETED
  (`ukn_ipid` is gone).
  `UkInitMain.v:1539` -- `(pidw ipw gnw bnw rv xs)` -> `(pidw gnw bnw rv xs)`.
  `UkShRun.v` NOT TOUCHED.

## WHAT IO-LEAF RECEIVES (sh's redemption)
At its fork, sh's record comes out of `UkFork.wp_uk_ecall_fork`'s child
arm with `∃ p : Z, ⌜p <> 1⌝ ∗ UserChildren.upid (ukn_pid N') p`.  Carry
BOTH through sh's state.  At the wait ecall take
`UkRunSys.wp_uk_ecall_wait_null_pid N h m pc avail Sc p` (same premises as
`_null_live` plus `upid (ukn_pid N) p`); the continuation hands back
`⌜bv_unsigned pidv = p⌝`, the fragment, the `⌜r = -1 -> Sc' = ∅⌝` row and
`UexecRet.uwait_ans_pid r Sc Sc' pidv`.  Then
`UexecRet.uwait_ans_pid_mine r Sc Sc' pidv` (premises `pidv <> 1`, from
the equation and `p <> 1`, and `r <> -1`, from the row and a non-empty
`Sc`) yields
  `∃ γ' rv xs, ⌜r = sext rv /\ Sc' = Sc ∖ {[γ']} /\ γ' ∈ Sc /\
   1 <= bv_unsigned rv <= PIDMAX⌝ ∗ exit_tok γ' rv xs ∗ gen_uniq Sc rv γ'`.
With `Sc = {[γ]}` the `γ' ∈ Sc` pins `γ' = γ` with no pid comparison, and
`ChildTok.gen_uniq_tok` then `gen_pay` cash the child token.
`wp_kshr_wait` needs a `_pid` twin in `UkShRun.v` (IO-LEAF's file).
