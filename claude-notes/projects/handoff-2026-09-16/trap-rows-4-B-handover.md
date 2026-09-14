# lane TRAP-ROWS-4 -- MILESTONE B handover

Checkout `/shared/xv6iris-2-tlw`, branch `lane/trap-rows-4` on
`origin/main = b992befc3`.  Build logs `tr110`..`tr114`;
**next free `tr115`**.

## B1a -- THE IDENTITY PLUMBING: COMMITTED AND GREEN (`31aff80ee`)

11 files, +289/-32.  Gate (`tr113` full, `tr114` confirming after the
rebase, both `EXIT=0`, zero `Error`): `make -f CoqMakefile -n` prints 0
`ROCQ compile`; audit md5 `57f7327206c4b276d05035342fea8ecf` (unchanged);
`lemma_diff --ref origin/main` CLEAN; NO `Admitted`/`admit`/`Abort` and no
new `Axiom`/`Hypothesis`; `--check-dumps` clean.  Every proof is closed --
this is NOT a statements-only pass.

* `UserChildren.v` gains `Section UserPid`: `upid_auth`/`upid` over **Z**
  (`ghost_varG Σ Z`, the class the tier already has -- a
  `ghost_varG Σ (mword 32)` would be the new-class mistake T4(b) ruled
  against), `upid_agree`, `upid_alloc`, `upid_any`.  NO update law: a
  process's pid never moves.
* `UkRun.uk_names` gains `ukn_pid : gname` and the pure `ukn_ipid : mword
  32`, BOTH AFTER `ukn_pay`, so every positional `MkUkNames` only gained
  trailing arguments.
* `UkRun.urun_ids N cs pidv := uch_auth (ukn_ch N) cs ∗ upid_auth (ukn_pid
  N) (bv_unsigned pidv)` REPLACES `urun`'s `uch_auth` conjunct, and
  `urun_close`/`urun_close_upd` take it in `uch_auth`'s POSITION.  That is
  the whole trick: ~200 leaves destructure `urun` positionally and hand
  the hypothesis straight back, and none of them reads either half, so
  the pid authority costs them NOTHING.  The four that do read a half take
  `urun_ids_ch` / `urun_ids_pid` (both LENDING accessors) or
  `urun_ids_intro` / `urun_ids_quiet`.
* `uslot_of_urun{,_all,_ro}` gain an `(ipid : mword 32)` parameter after
  `Q`, mint `upid_alloc (bv_unsigned (uvis_pid W))`, key the record at
  `γpid`/`ipid`, and hand the program
  `upid (ukn_pid N) (bv_unsigned (uvis_pid W))` right after `uch`.
* `UkFork`: the parent arm lends the children half through `urun_ids_ch`;
  the child arm mints the child's own pid pair at `pidc`, keys the child's
  record at it and at the parent's `ukn_ipid N` (INHERITED), and hands the
  child `∃ p, upid (ukn_pid N') p`.

### The lines outside this lane's own files
  * `UShKernel.v:584`   `uslot_of_urun_all` + `:589` intro pattern
  * `UInitKernel.v:369` `uslot_of_urun_all` + `:374` intro pattern
  * `UEchoKernel.v:456` `uslot_of_urun_ro`  + `:462` intro pattern
  * `UEchoOut.v:794`    `uslot_of_urun_ro`  + `:797` intro pattern
  * `USyncKernel.v:182` `uslot_of_urun`     + `:187` intro pattern
  * `UkInitMain.v:946`  child-arm intro gains one `_`
  * `UkShRun.v:1093`    child-arm intro gains one `_`  <-- IO-LEAF's file
  Each is ONE argument or ONE `_`.  The `ipid` argument is
  `(mword_of_int 0)` at all five for B1a -- NOTHING READS `ukn_ipid` yet --
  and B1b turns it into the entry's own parameter.

## B1b -- THE FAMILY FIELD AND THE ROWS (designed, not written)

The re-keying combinator is the mechanism, on `sfam_at`'s exact mould:

  * `UexecSG.uexecSG` gains `sinit_pid : sfam -> mword 32`, the
    constructor `sfam_ip : mword 32 -> sfam -> sfam`, and the laws
    `sinit_pid_ip` (`= ip`), `sinit_pid_at` / `sinit_pid_pay` /
    `sinit_pid_pt` (pass-through / junk at the point), `sexit_pay_ip`,
    `sfork_pay_ip`, `sfork_lend_ip`, `sbundle_at_ip` (at `n <> read`,
    `n <> exec` -- wait and fork are both) and `spost_at_ip`.
  * `UexecExecInst.xfam` gains `kf_ipid : mword 32`, `xfam_ip` beside
    `xfam_at`, and the instance rows; every existing builder sets it at
    `mword_of_int 0`.
  * `UexecRet.uexec_wait_F`'s row becomes
    `uwait_ans_pid r (uvis_ch W) cs' (uvis_pid W) (sinit_pid f)`, and
    `uexec_fork_child_F` gains an `ip` parameter and the wand
    `⌜pidc <> ip⌝`, instantiated at `sinit_pid f` in `uexec_fork_F`.
  * The two leaves RE-KEY their deposited family with
    `sfam_ip (ukn_ipid N)` (free at wait and fork by `sbundle_at_ip`), so
    `wp_uk_ecall_wait_null_live` -- a `_pid` twin, `wp_uk_ecall_wait_null`
    unchanged -- hands the program `⌜γ' ∈ Sc⌝ ∨ ⌜p = ukn_ipid N⌝` against
    its `upid (ukn_pid N) p`, and `wp_uk_ecall_fork`'s child arm hands it
    `⌜pidc <> ukn_ipid N'⌝`.
  * NEITHER `uvis` NOR `uslot`'s index moves, and every relay keeps its
    arity.

### THE ONE OBLIGATION THAT DOES NOT DISCHARGE ITSELF
The kernel OWES the arm at the family the PROCESS deposited, so it must
prove `pidv = sinit_pid f` from kwait's `pidv = un_ipid N`, i.e. it needs
`⌜sinit_pid f = un_ipid N⌝`.  `f` is chosen by the process and the kernel
never learns anything about it, so this is a PREMISE: it belongs on
`SpecUsertrap.wp_usertrap_sconf_body` beside its `f`, and the party that
discharges it is whoever applies that contract.  In B1b it is the one
`Admitted`.  Two ways to close it afterwards:
  (i) pin <init>'s pid to 1 -- `SpecAllocproc.allocproc_post` reports that
      the FIRST pid is <nextpid>'s incoming value, which `ProofMain` seals
      at 1 before userinit runs -- and then both sides name the literal;
  (ii) make the number ambient the way `FsCfg.fscfg`'s fields are, with
      userinit's seal as the boot-era obligation.

## THE B1b RULING (coordinator, VERBATIM IN EFFECT) AND WHAT I CHECKED

RULING: option (i) -- PIN <init>'s pid to the literal 1, so both sides name
the same number and `sinit_pid` / `kf_ipid` / `sfam_ip` and the pure
`ukn_ipid` all disappear (B1a's `(mword_of_int 0)` placeholders become 1 or
go, whichever leaves `lemma_diff` smallest).  Then `uexec_wait_F`'s row is
`uwait_ans_pid r (uvis_ch W) cs' (uvis_pid W) 1`, `uexec_fork_child_F`
gains `⌜pidc <> 1⌝`, and the two leaves hand the program
`⌜γ' ∈ Sc⌝ ∨ ⌜p = 1⌝` against its `upid` and the fork-side `⌜pidc <> 1⌝`.
Mechanism as ruled: `PidLock.nextpid_res_at` mirrors the counter in a ghost
whose other half a caller MAY hold; `ProofMain` mints `nextpid_is 1` where
it seals the counter at 1 and hands it to the group that calls userinit;
`ProofUserinit` learns `pid = 1` and seals `init_pid_is 1`.

### THE C FACT IS TRUE IN THIS TREE'S BOOT ORDER -- CHECKED
  * `int nextpid = 1;` and the `.data` carve hands the word out PINNED at 1
    (`BootShared.nextpid_bytes`); `ProofMain.mn_grp_kvm` takes it as
    `alp_nextpid ↦₄ (mword_of_int 1 : mword 32)`.
  * `allocproc` has exactly TWO callers in the tree: `ProofUserinit.v:428`
    and `ProofKforkB6.v:826` (kfork, reachable only from sys_fork, hence
    only once a user process exists).  `procinit` does not allocate --
    `SpecProcinit.v` mentions allocproc only in prose.
  * `started = 1` is published in `mn_grp_started` (main+0xa2 onward),
    STRICTLY AFTER userinit at main+0x9e, so no secondary hart has entered
    the scheduler -- and hence nothing else has run at all -- before it.
  So userinit's allocproc IS the first allocation and <init>'s pid IS 1.

### THE ENCODING HOLE IN THE MECHANISM AS SKETCHED -- A RULING IS OWED
An exact-value mirror of the counter has to be UPDATED by every party that
bumps the counter, and updating a two-half ghost needs both halves.  So
while main's half is out, a caller WITHOUT it cannot re-establish the
payload -- i.e. the "a caller without it gets the old post" corollary is
not merely unproven, it is FALSE as stated (its truth is exactly the global
fact "nobody else allocates while the tracker is live").  The same wall
closes on every variant I tried: a `bool` mirror with the conjunct
`b = true -> v = 1`, a one-shot whose Shot the payload must mint, a
`dfrac_agree` at a variable fraction -- in each the token-less caller has
to move the payload off the tracked side and owns nothing that lets it.
  The generic corollary therefore needs a side condition saying THE MIRROR
IS WHOLE, and that has to be observable to a token-less caller.  The
cheapest observable already in the tree is the PROC LEDGER'S REGIME:
`ProcAvail.procs_avail (Some n)` is the boot era and `procs_avail None` is
everything after userinit's park (`ProofUserinit` seals it, one-way), and
EVERY allocproc caller holds one or the other.  Two shapes worth ruling on:
  (A) the mirror's half rides the COUNTED regime -- `procs_avail (Some n)`
      carries it, `procs_avail None` does not -- so allocproc's two
      corollaries are exactly its two existing regimes and no caller gains
      a premise it does not already have;
  (B) allocproc takes the mirror half UNCONDITIONALLY (every caller
      threads `nextpid_is n` / `nextpid_is (n+1)`), which is one premise on
      kfork's chain and no disjunction at all.
(A) is smaller at the call sites, (B) is smaller in `SpecAllocproc`.

STOPPED GREEN at `31aff80ee` (= `origin/main`), working tree clean.

## B1b -- THE RULING IS SHAPE (A).  EXECUTABLE PLAN FOR A SUCCESSOR.

RULED (coordinator): the counter mirror's half rides the COUNTED REGIME of
the process ledger.  `ProcAvail.procs_avail (Some n)` carries `nextpid_is`
(the boot era, before userinit's park); `procs_avail None` does not -- the
mirror is WHOLE in `PidLock.nextpid_res_at`'s payload from then on.  So
`allocproc`'s two corollaries ARE its two existing regimes and no caller
gains a premise it does not already hold: in the counted regime the caller
learns `⌜pid = n⌝` and gets the half back at `n+1`; at `None` it gets the
old post.  `ProofUserinit` is in the counted regime, learns `pid = 1`,
seals `init_pid_is 1`, and its park moves the ledger to `None` (the half
goes into the payload, whole from then on).  Everything downstream is at
the literal, and `sinit_pid` / `kf_ipid` / `sfam_ip` / the pure `ukn_ipid`
are GONE (B1a's `(mword_of_int 0)` placeholders become 1 or the field
goes -- whichever leaves `lemma_diff` smallest).

### THE ONE SHAPE DECISION THE RULING LEAVES OPEN, AND ITS ANSWER
`procs_avail (Some n)`'s `n` is the FREE-SLOT COUNT, not the counter, so a
mirror half carried inside it would be at an existential value and userinit
could not read `1` off it.  Index it, with the corollary trick this lane
has used twice (`wp_uk_ecall_wait_null` / `uwait_ans`):

    Definition procs_avail_at (on : option nat) (p : Z) : iProp Σ := ...
    Definition procs_avail (on : option nat) : iProp Σ :=
      (∃ p : Z, procs_avail_at on p)%I.

`procs_avail`'s ARITY DOES NOT MOVE, so the ~17 files that merely thread or
weaken it (`procs_avail_le`, `SyscParkEnv`, `ProofSyscall`, `UsertrapRes`,
`SpecKfork`, `SpecSysFork`, `SpecForkret`, `BootShared`, `BootChain`) are
untouched.  Only the boot chain (`ProofMain`), `SpecUserinit`/
`ProofUserinit`, `SpecAllocproc`/`ProofAllocproc` and `ProofKforkB6` name
the `_at` form.  `procs_avail_at None p` ignores `p` (the mirror is in the
payload); `procs_avail_at (Some n) p` is today's `Some` arm plus
`PidLock.nextpid_is p`.

### THE FILES, IN ORDER, AND WHAT EACH OWES
 1. `Xv6Cameras.v` -- the mirror's camera and canonical name beside
    `wip_name`: a `ghost_varG Σ Z` is already on the bundle, so the cheapest
    is one more `gname` field (`npid_name`) on the class that carries
    `nextpid`'s other ghosts.
 2. `PidLock.v` -- `nextpid_is (p : Z) := ghost_var npid_name (1/2) p`;
    `nextpid_res_at`'s first conjunct becomes
    `∃ v, cell ↦₄ v ∗ ⌜1 <= bv_unsigned v <= PIDMAX⌝ ∗
     ∃ q, ghost_var npid_name q (bv_unsigned v) ∗ ⌜q = 1%Qp \/ q = (1/2)%Qp⌝`
    -- WHOLE when untracked, half when the ledger holds the other half.
    Re-prove `nextpid_res_at_morph` (`ghost_var` is context-free, so
    `ctx_morph_solve` should still go through; if the const payload hangs
    the search, see `ctx_morph_const_pay` in the durable notes).
 3. `ProcAvail.v` -- `procs_avail_at` as above, `procs_avail` as its
    existential closure, and `procs_avail_le` / `procs_avail_seal` /
    `procs_avail_zero` restated at `_at` with corollaries at the old names.
    `procs_avail_seal` PUTS THE HALF BACK: it takes the payload (the caller
    holds the pid lock at userinit's park -- check that it does; if not,
    the seal takes `nextpid_is p` and drops it, and the payload's `q` goes
    back to 1 at the NEXT allocproc, which is the honest alternative).
 4. `SpecAllocproc.v` -- ONE general lemma, two corollaries:
      OLD post (unchanged, at `procs_avail None`):
        success arm reports `1 <= bv_unsigned pid <= PIDMAX` and nothing
        about the counter.
      NEW post (at `procs_avail_at (Some n) p`):
        the same, PLUS `⌜bv_unsigned pid = p⌝`, and the ledger comes back
        as `procs_avail_at (Some n') (p + 1)`.
      The FAILING arms return the ledger unmoved at `p` (allocpid runs
      before the scan can fail?  CHECK: in the C, `allocproc` scans first
      and calls `allocpid` only on a found slot, so a failing allocproc
      never bumps the counter -- if the proof's order differs, the failing
      arm returns `p + 1`).
 5. `ProofAllocproc.v` -- at the `nextpid = nextpid + 1` store, update the
    mirror with `ghost_var_update_2` in the counted regime and leave it
    whole in the `None` regime.  This is the one real proof step.
 6. `SpecMain.v` / `ProofMain.v` -- the boot mints `ghost_var npid_name 1 1`
    where `mn_grp_kvm` seals the counter at 1, splits it, puts one half in
    the payload at the `newlock` and the other in `procs_avail_at (Some np)
    1`, which rides to `mn_grp_fs` exactly as `Hpavail` already does.
 7. `SpecUserinit.v` / `ProofUserinit.v` -- the contract takes
    `procs_avail_at (Some np) 1`; the allocproc call learns
    `⌜bv_unsigned pid = 1⌝`; `init_pid_set`/`init_pid_seal` are already
    there and now seal at the literal, so `WaitInv.init_gen (proc_addr j) 1`.
    `ut_names.un_ipid` becomes `1` at the record (or the field goes and
    every `un_ipid N` becomes the literal -- prefer the deletion if
    `lemma_diff` stays clean).
 8. THE LITERAL SWEEP -- `UserChildren.wait_ans … pidv 1`,
    `UexecRet.uwait_ans_pid r Sc Sc' pidv 1` (the `ip` parameter goes),
    `SpecKwait`/`SpecSysWait`'s `ipid` parameter and `init_pid_is ipid`
    premise go (the premise becomes `init_pid_is 1`, still needed -- it is
    what `ProofKwait.wait_ans_of_gen` spends), `SpecSyscall.sysc_init_id`
    keeps its shape.
 9. THE TWO LEAVES -- `UexecRet.uexec_wait_F`'s row becomes
    `uwait_ans_pid r (uvis_ch W) cs' (uvis_pid W) 1` and
    `uexec_fork_child_F` gains the wand `⌜pidc <> 1⌝`;
    `UkRunSys.wp_uk_ecall_wait_null_live` gets a `_pid` twin handing
    `⌜γ' ∈ Sc⌝ ∨ ⌜p = 1⌝` against the program's
    `upid (ukn_pid N) p` (B1a's fragment), `wp_uk_ecall_wait_null`
    UNCHANGED; `UkFork.wp_uk_ecall_fork`'s child arm hands
    `⌜pidc <> 1⌝` beside the `upid` fragment B1a already gives it.
10. THE KERNEL SIDE OF 9 -- `ProofUserretClosed` builds the wait row from
    `SpecUsertrap.ut_wait_out`, which must stop closing `ip` existentially
    (milestone A closed it there deliberately); at the literal there is
    nothing to close and no tie is owed.  The fork row's `⌜pidc <> 1⌝` is
    refuted at kfork's pid-registration INSERT against
    `WaitInv.init_gen`'s `pid_reg 1 DfracDiscarded g` -- `init_gen_reg_ne`
    is already written and unused, waiting for exactly this.

### WHAT IS ALREADY IN THE TREE FOR THIS
`WaitInv.init_gen` / `init_gen_pid_is` / `init_gen_reg_ne` /
`init_ident_at_of_gen`, `SlotGen.init_pid_is` / `_set` / `_seal` /
`slot_gen_persist` / `pid_reg_persist`, `UserChildren.wait_ans_gen` /
`wait_ans_of_gen`, `UexecRet.uwait_ans_pid`, `UserChildren.upid` and
`UkRun.ukn_pid` / `urun_ids` with its lending accessors.  Milestones A and
B1a are both on `origin/main`.

STOPPED GREEN at `31aff80ee` (= `origin/main`), working tree clean, no
build owed.  Next free build log `tr115`.
