# lane TRAP-ROWS-3 -- handover

Checkout `/shared/xv6iris-2-tlw`, branch `lane/trap-rows-3`, on
`origin/main = 9d1efd787` (IO-LEAF M4a(2a)).  VM tree
`/mnt/rocq/trees/_shared_xv6iris-2-tlw`.  Build logs `tr82`..`tr87` used;
**next free `tr88`**.  Rules: build only with
`./gcp-rocq/vmbuild.sh xv6iris-2-tlw <log>` from the repo root; one at a
time; a sync IS a build; never pattern-kill; never push; commit by path.

## T4(c) -- LANDED ON THE LANE, `2a372a9d7`, GREEN (2026-09-14)

9 files, +322/-83.  Build `tr87`: `COMPILED=560`, `EXIT=0`, zero `Error`;
`make -f CoqMakefile -n` 0 `ROCQ compile`; audit md5
`57f7327206c4b276d05035342fea8ecf`; `lemma_diff --ref origin/main` CLEAN
(nothing dropped, nothing admitted, no new assumption); `--check-dumps`
clean.  NOT a statements-only pass -- every proof is closed.

Trusted diff (statements) in `t4c-core.diff` (SlotGen / UserChildren /
SpecUsertrap / UexecRet) plus UkRunSys's new leaf.

* `SlotGen.gen_halves_at pa pid g` first conjunct
  `⌜bv_unsigned pid <> 0⌝` -> `⌜(1 <= bv_unsigned pid <= PIDMAX)%Z⌝`.
  `gen_halves_at_nz` keeps its statement (now by `lia`); new
  `gen_halves_at_rng` / `gen_halves_priv_rng`; `gen_halves_at_intro` and
  `gen_halves_priv_intro` take the range.  BOTH call sites
  (`ProofKforkMain.v:823`, `ProofUserinit.v:480`) already discharged it
  with `ltac:(lia)` off `SpecAllocproc.allocproc_post`'s
  `1 <= bv_unsigned pid <= PIDMAX`; NOTHING ELSE MOVED.
* `UserChildren`: requires `Riscv.rv64d`, `RiscvExtras`, `ProcGeom`,
  `stdpp bitvector.definitions`, `Lia` (they were not there);
  new pure `sext32_rng_not_neg1`; `wait_ans`'s reaping arm is
  `⌜cs' = cs ∖ {[γ']} /\ (1 <= bv_unsigned rv <= PIDMAX)%Z⌝ ∗ exit_tok ∗
  gen_uniq`; new `wait_ans_m1` (at `sign_extend' 64 rv = -1` the reaping
  arm is refuted, and what is left -- `⌜rv = -1 /\ cs' = cs⌝ ∗ wait_why`
  -- is wholly PERSISTENT).
* `SpecUsertrap.ut_live_out` is now a CONJUNCTION; the second clause is
  `sc = uecall_scause -> usys_num tf = USYS_wait ->
   uint (tf !!! tf_arg_idx 0) = 0 -> r = -1 -> cs' = ∅`.
  New `ut_live_wait_g` (+ its `Decision`); `ut_live_out_of` takes the
  second refutation; `ut_live_out_num` takes `usys_num tf <> USYS_wait`
  too; `_ne` / `_cong` / `uexec_live_ok_of_live` adapted.
* `UexecRet.uexec_live_ok` gains a `(cs' : gset gname)` and the same
  second clause (at `tf_w tf (tf_arg_idx 0)`); `uexec_live_ok_ne` takes
  `n <> USYS_wait`; `uexec_ret_cont_gen` reads it at the bound `cs'`.
  `UexecApply` passes `uvis_ch W'` / the round's `cs'`.
* `ProofUsertrapTail.ut_a6`: new `Hwwhy` hoist (the `Hrwhy` idiom at
  `Hwo`) -- case on `ut_live_wait_g`, apply `ut_wait_out`'s wand, read
  the reason off `wait_ans_m1`, rebuild the wand from `wait_ans_neg`;
  then a second `iAssert` inside the `killed()` accessor's zero-flag
  branch refutes the shot with `SchedCtx.kill_paid_shot_nz` and yields
  `Hnw`.
* `UkRunSys.wp_uk_ecall_wait_null_live` -- the leaf with
  `⌜r = -1 -> Sc' = ∅⌝` in the continuation.  `wp_uk_ecall_wait_null`
  KEEPS ITS STATEMENT VERBATIM, proved from `_live` by dropping the row,
  so `UkInit.wp_kinit_wait` and `UkShRun.wp_kshr_wait` (IO-LEAF's files)
  are UNTOUCHED.  IO-LEAF switches `wp_kshr_wait` to `_live` when it
  wants the row.
* `UkInitMain.v`: two `iDestruct` patterns for `wait_ans`'s reaping arm
  gained the extra pure conjunct (`[%Hcseq %Hrngc]`).  That is the WHOLE
  edit to that file.

## T4(b) -- NOT WRITTEN.  A ruling is owed; see the report.

The kernel half is fully determined and cheap; the U-TIER SPELLING IS
NOT, and writing it wrong costs a 559-file cone.  Findings:

1. `rows_unique` IS ENOUGH for `γ' ∈ cs`.  `WaitInv.children_inv_reap`
   (WaitInv.v:1035) ALREADY returns `⌜g ∈ cs \/ g ∈ orph_row O pj⌝` and
   its proof already closes the left disjunct exactly that way
   (`inv_slots` -> `in_row m pj g` -> `rows_unique` against
   `children_own_lookup`'s `m !! γrow = Some (pj, cs)`).  So T4(b)'s
   kernel half is ONLY "kill the right disjunct".
2. The orphan-at-init conjunct CANNOT be a bare `∃ ip` in the payload:
   the reaper must identify the payload's `ip` with the cell's, so the
   conjunct has to own a share of `initproc`.  It cannot be minted at
   `wait_res_alloc` either -- `ProofMain`'s `newlock` for wait_lock runs
   in `mn_grp_procinit`, LONG before userinit writes the cell, and the
   cell is exclusive until then.  THE SHAPE THAT WORKS is the implication
   form, vacuous at boot and persistent:
     `∀ pa g, ⌜g ∈ orph_row O pa⌝ → ctx_word_pointsto ξ initproc
                                      DfracDiscarded pa`
   (`impl_persistent`; `ctx_word_pointsto ξ _ DfracDiscarded _` already
   has a `CtxMorph` -- `UsertrapRes.park_globals_morph` uses it, so
   `wait_res_at`'s morph survives).  `ProofUserinit` discards the cell
   (`ProofUserinit.v:787`) and `UsertrapRes.ut_park_caps` PINS
   `un_dqi N = DfracDiscarded`, so kexit's `initproc ↦₈{dqi} ip` IS the
   persistent one on the live path -- but `SpecKexit`/`SpecReparent`/
   `SpecSyscall` state it at an opaque `dqi`, so either they gain
   `dqi = DfracDiscarded` or the conjunct takes a fraction.
3. THE U-TIER SPELLING IS THE PROBLEM.  Nothing pins init's pid to 1:
   `SpecAllocproc.allocproc_post`'s success arm reports only
   `1 <= bv_unsigned pid <= PIDMAX` and never relates the returned pid to
   <nextpid>'s incoming value, which `ProofMain` seals into pid_lock's
   payload (`ProofMain.v:1341`) before userinit runs.  And a resource
   spelling is not relayable: `uwait_ans` binds `gn` existentially, so a
   disjunct about the caller's GENERATION is absorbed exactly as
   `wait_why` is.  The only U-visible handle is `uvis_pid` / `urun`'s
   `pidv`.
   Three ways out, cheapest first -- ALL need something the ruling did
   not mention, namely a fact minted at FORK, because refuting "I am
   init" is not a theorem of the caller's own walk:
   (a) `pidinit` as a PARAMETER: `wait_ans`/`uwait_ans` gain the caller's
       pid and init's pid, reaping arm `⌜γ' ∈ cs⌝ ∨ ⌜pid = pidinit⌝`;
       `ProofUserinit` DISCARDS (instead of dropping -- see
       ProofUserinit.v:~470-480) init's 3/4 of `slot_gen` and its 3/4 of
       `pid_reg`, giving the persistent `init_ident ip pidinit g1`;
       kwait turns `pme = ip` into `pid = pidinit` through
       `slot_gen_agree` + `gen_pid` agreement; kfork's registration
       INSERT at a fresh key refutes `pidc = pidinit` against init's
       persistent registration, so the fork child arm can carry
       `⌜pidc <> pidinit⌝` and sh gets it from init's fork.
   (b) the same with `pidinit` pinned to 1, which removes the parameter
       everywhere but requires `allocproc_post` to report that the FIRST
       pid is the counter's incoming value (a real spec change to a
       function that takes <pid_lock> itself).
   (c) a PREMISE `pme <> ip` on kwait instead of a disjunct -- rejected:
       init's own wait (`UkInitMain`) could not discharge it, and the
       premise is a kernel ADDRESS the U tier cannot see.
   RECOMMENDATION: (a).  It touches `wait_ans` (559-file cone) once,
   together with anything else the row ever needs.

## What IO-LEAF receives from T4(c)

`UkRunSys.wp_uk_ecall_wait_null_live` -- same premises as
`wp_uk_ecall_wait_null`, one extra pure wand
`⌜r = (mword_of_int (-1) : mword 64) -> Sc' = ∅⌝` before `uwait_ans`.
sh's `wp_kshr_wait` refutes the reap-nothing arm with it at a nonempty
`Sc`.  It still CANNOT identify the reaped child (T4(b)).

## PHASE 1b -- T4(b) STOPPED ON TWO OBSTACLES (2026-09-14)

Checkout `/shared/xv6iris-2-tlw`, branch `lane/trap-rows-3` = `origin/main`
= `f982b2194`, WORKING TREE CLEAN.  Build `tr103`: COMPILED=1059, EXIT=0
(the VM tree is back at main).  Builds `tr82`..`tr103` used; **next free
`tr104`**.  The whole attempt is saved as `t4b-wip.patch` (15 files,
+569/-53) -- `git apply` it to resume.

WHAT THE PATCH CONTAINS, ALL OF IT COMPILING at the point I stopped
(`tr101`/`tr102`: WaitInv, SlotGen, ProcInv, UserChildren, ProofKwait,
ProofKexit, SpecKexit, SpecSysExit, SpecSyscall, ProofSyscall,
ProofSysExit all green):

 * `Xv6Cameras`: `ipidUR := optionUR (dfrac_agreeR (leibnizO (mword 32)))`,
   `wip_pre_inG`/`wip_inG`/`wip_name` on `wchGpreS`/`wchG`/`wchΣ`.
 * `SlotGen`: `init_pid_tok p` (whole) / `init_pid_is p` (discarded,
   persistent) with `_agree` / `_ne` / `_set` / `_seal` / `_tok_excl`;
   `gen_halves_at_sg` / `gen_halves_priv_sg` (the slot-generation quarter,
   lent).
 * `UserChildren`: `gen_is_init g := ∃ p0, init_pid_is p0 ∗ gen_pid g p0`
   (persistent), `gen_is_init_pid` (the pid form), `gen_is_init_ne` (the
   refutation a forked child spends).
 * `WaitInv`: `init_ident_at ξ ip` = the <initproc> cell at `ip`, the
   slot's CURRENT generation at `DfracDiscarded`, that generation's pid,
   and `init_pid_is` at it -- persistent, `CtxMorph`;
   `init_ident_gen` (a process at <init>'s address reads `gen_is_init` off
   it against its own block's quarter);
   `orph_at_init_at ξ O := [∗ map] pa ↦ Sr ∈ O, ⌜Sr = ∅⌝ ∨ init_ident_at ξ pa`
   (a BIG-OP, not a `□`-wand: `CtxMorph`'s transport is a `==∗` that spends
   its domination, so nothing under a `□` transports and the payload has
   to be structural);
   `orph_at_init_empty` / `_read` / `_shrink` / `_ins` / `_reap`;
   `children_inv_at ξ` (= the old two conjuncts + `orph_at_init_at ξ`),
   `children_inv := children_inv_at cur_ctx`, `wait_res_at` uses the `_at`
   form; `children_inv_reparent` gains `init_ident ip`; the reap and the
   boot re-establish the conjunct (`_shrink` / `_empty`); `children_boot`
   gains `init_pid_tok 0` and `children_res_alloc` mints it.
 * `ProcInv`: `proc_priv_core_slot_gen` / `proc_priv_slot_gen`.
 * `ProofKwait.kw_reap`: takes the caller's `slot_gen pme (1/4) gnr` LENT
   (returned in its continuation; `kw_found` opens the block at each of the
   two call sites and closes it after), and PRODUCES
   `⌜γ' ∈ cs⌝ ∨ gen_is_init gnr` out of `children_inv_reap`'s disjunction
   and `orph_at_init_reap`.  **SpecKwait's contract does not move.**
 * The kexit chain at the PERSISTENT share: `SpecKexit`, `SpecSysExit`,
   `SpecSyscall`, `ProofSyscall`, `ProofKexit`, `ProofSysExit` take
   `initproc ↦₈□ ip` (the `dqi` binder is left in place, unused, so no
   argument list moves) and gain `WaitInv.init_ident ip` beside it;
   `SpecReparent` is UNCHANGED (reparent really does work at any
   fraction; `ProofKexit` passes `DfracDiscarded`).

### OBSTACLE 1 -- WHERE THE SAVED PID CAN LIVE

`init_pid_is` is on `wchG`, and `wchG` is NOT a class the U tier declares.
The moment `UserChildren.wait_ans`'s reaping arm mentions `gen_is_init`,
every section that mentions `wait_ans`/`uwait_ans`/`uslot` needs
`Context {!wchG Σ}` -- **54 files** (`grep -rln "Context \`{!ctokG Σ}\."`),
including UkSh*, UShKernel, UConsLine, UInitSh, UkInit*, UkEcho, UkCat,
USyncKernel: i.e. IO-LEAF's whole working set.  I got as far as
UexecRet/UkStep/UexecApply before stopping.
  The class the U tier DOES have is `ChildTok.ctokG` -- but it carries no
gname (all its ghosts are keyed by an explicit `γ`), so a CANONICAL saved
pid cannot live there without splitting it into `ctokGpreS`/`ctokG` the way
`wchG` is split, which moves `Xv6G.xv6_ctok` and the adequacy files
(`SystemAdequacy`, `App`, `UInitBootAdequacy` -- and `UInitBootAdequacy` is
in IO-LEAF's M5 set).
  THE THIRD OPTION -- state the disjunct against the <initproc> CELL rather
than a ghost -- is worse: it drags `riscvGS` AND `TsoCtx.CurCtx` into
`UserChildren`, i.e. into the same 54 files, and makes `wait_ans`
context-dependent across the park.
  RULING NEEDED: (a) split `ctokG` (the saved pid rides the class the U
tier already has; ~4 files move, one of them IO-LEAF's), or (b) add
`Context {!wchG Σ}` to the 54 (mechanical, one line each, but collides with
IO-LEAF), or (c) leave `wait_ans` alone and deliver the disjunct only to
the kernel (see obstacle 2 -- it is stuck there anyway).

### OBSTACLE 2 -- THE U TIER CANNOT NAME ITS OWN PID

Ruling (3) says the disjunct is relayed "at `uvis_pid`/`urun`'s `pidv`".
`UkRun.urun` (UkRun.v:825-899) binds `pidv` EXISTENTIALLY **with no
resource beside it** -- exactly the wall that forced `wait_why`'s
absorption for `gn`.  `uvis_pid W` exists in the KEY, but a program holding
`urun` has no handle on it: there is no `upid` fragment the way there is
`uch (ukn_ch N) cs` for the children set and `ucwd` for the cwd.  So
`uwait_ans r cs cs' pidv` cannot be stated at the leaf: the leaf would have
to close `pidv` existentially, which loses the disjunct again.
  SMALLEST FIX, and it mirrors what is already there twice: `uk_names`
gains `ukn_pid : gname` beside `ukn_ch`/`ukn_cwd`, `urun` gains
`upid_auth (ukn_pid N) pidv`, the entry constructors hand the program
`upid (ukn_pid N) (uvis_pid W)`.  Only FIVE sites construct a `uk_names`
(`UkRun.v` ×3 -- the three `uslot_of_urun*` entry constructors -- and
`UkFork.v` ×2), so the record change is small; the ghost is
`UserCwd.ucwd`'s twin one value wide.  It is independently useful: it is
what makes getpid(2)'s answer sayable.
  With that, ruling (2)'s fork-side token lands on `wp_uk_ecall_fork`'s
CHILD arm as `∃ p0, init_pid_is p0 ∗ ⌜pidc <> p0⌝` (`pidc` is already bound
there), and the exec channel carries it into the new image beside the
child's `upid` fragment -- the one-line change IO-LEAF owns is in
`UInitSh.sh_slot_of_kexec` (and `UShKernel` if the row is re-stated there):
sh's entry gains that conjunct and hands it to `wp_kshr_wait`.

### WHAT I WOULD DO NEXT, GIVEN A RULING

1. host the saved pid (obstacle 1);
2. `ukn_pid` + `upid`/`upid_auth` (obstacle 2), five construction sites;
3. re-apply `t4b-wip.patch`, add the disjunct to `wait_ans`'s reaping arm
   and relay it on `uwait_ans_at`/`uwait_ans` and
   `wp_uk_ecall_wait_null_live` (`wp_uk_ecall_wait_null` keeps its
   statement, as in T4(c));
4. kfork's child arm mints `⌜pidc <> p0⌝` off the pid-registration INSERT
   against `init_pid_is`'s registration;
5. the BOOT END, still untouched: `children_boot` now carries
   `init_pid_tok 0` and NOTHING CONSUMES IT -- `ProofMain.mn_grp_procinit`
   (ProofMain.v:~1042) must destruct it and thread it to the group that
   calls userinit (main+0x9e..0xa2), where `ProofUserinit` (:~470-480)
   DISCARDS init's 3/4 of `slot_gen` and its 3/4 of `pid_reg` instead of
   dropping them, fires `init_pid_set`/`init_pid_seal` at the pid
   allocproc gave it, and seals `init_ident`.  `ut_caps` then carries
   `init_ident (un_ip N)` for the kexit chain.  THIS IS THE ONLY PART OF
   THE PATCH THAT IS NOT WRITTEN AT ALL.

## THE RULING ON BOTH OBSTACLES (coordinator, 2026-09-14, VERBATIM)

> Keep everything kernel-side that you built in the patch (the `ipidUR` on
> `wchG`, `init_pid_tok`/`init_pid_is`, `gen_is_init`, `init_ident_at`, the
> big-op `orph_at_init_at`, `kw_reap` producing `⌜γ' ∈ cs⌝ ∨ gen_is_init
> gnr`, the kexit chain at the persistent share, `children_boot` + the boot
> end through `ProofMain.mn_grp_procinit`/`ProofUserinit` discarding init's
> shares).  OBSTACLE 1 (the U tier cannot see `wchG`): it never will.  The U
> tier sees NUMBERS: the kernel's capability record `ut_caps` gains a PURE
> field `un_ipid : mword 32` tied kernel-side to the ghost by `init_pid_is
> (un_ipid N)` (carried in `ut_caps` from userinit's seal onward), and
> `wait_ans`/`uwait_ans` mention NO ghost -- `wait_ans`'s reaping arm is
> stated as `⌜γ' ∈ cs⌝ ∨ ⌜the caller's pid = ip⌝` for a pure `ip : mword 32`
> parameter (the relays already carry `nullst`-style pure parameters; add
> `ip` the same way), produced by kwait from `gen_is_init gnr` +
> `init_pid_is`'s agreement + `gen_pid` at the caller's registration (the
> caller's pid is in the block); the U-tier `uwait_ans r Sc Sc'` gains the
> pure disjunct `⌜γ' ∈ Sc⌝ ∨ ⌜pidv = ip⌝`.  OBSTACLE 2 (the U tier cannot
> name its own pid): your smallest fix, adopted -- `uk_names` gains
> `ukn_pid : gname` beside `ukn_ch`/`ukn_cwd`, `urun` gains `upid_auth
> (ukn_pid N) pidv`, the five `uk_names` construction sites (UkRun ×3,
> UkFork ×2) mint it, and the program holds the fragment `upid (ukn_pid N)
> p`; ALSO `uk_names` gains the PURE field `ukn_ipid : mword 32` (init's pid
> as a number; the entry constructors set it from `un_ipid`), so the
> fork-side token on `wp_uk_ecall_fork`'s child arm is the PURE
> `⌜pidc <> ukn_ipid N'⌝` (refuted at the registration insert against
> init's persistent registration at `un_ipid`), and
> `wp_uk_ecall_wait_null_live`'s reaping arm hands the program
> `⌜γ' ∈ Sc⌝ ∨ ⌜p = ukn_ipid N⌝` against its `upid (ukn_pid N) p`.  No
> `Context {!wchG Σ}` anywhere in the U tier; no `ctokGpreS` split.

## THE WORK ORDER FOR A SUCCESSOR (start from `t4b-wip.patch`)

`git apply` the patch onto `origin/main` first; it was green through
ProofKwait/ProofKexit/ProofSysExit at `tr101`/`tr102`.  Then, IN THIS
ORDER -- each step keeps the tree green:

**(1) THE BOOT END, which the patch does not have at all and which makes
everything else non-vacuous.**  Without it `SpecKexit`'s new
`WaitInv.init_ident ip` premise is UNSATISFIABLE and kexit goes vacuous --
do not land any of the patch before this closes.
  * ROUTING IS CHEAP, checked: `children_boot` reaches main as ONE premise
    of `SpecMain.wp_main_sconf_body` (SpecMain.v:654) and is consumed in
    `ProofMain.mn_grp_procinit` (ProofMain.v:1042).  Split it at
    ProofMain's TOP level instead: hand `mn_grp_procinit` the three old
    conjuncts and keep `init_pid_tok` for the group that calls userinit
    (main+0x9e..0xa2, `mn_grp_disk`, which already receives
    `∃ v0, initproc ↦₈ v0` -- SpecMain.v:382).  No group-to-group threading.
  * `ProofUserinit` (:~470-480) currently DROPS init's 3/4 of `slot_gen`
    ("the PARENT'S QUARTER IS DROPPED") and its 3/4 of `pid_reg` ("the
    row's eighth stayed in <p->lock>'s payload").  DISCARD them instead
    (both cameras support `DfracDiscarded`; `slot_gen` is `dfrac_agree` in
    a gmap, `pid_reg` a `ghost_map` fragment), fire
    `SlotGen.init_pid_set` then `_seal` at the pid allocproc returned, and
    build `WaitInv.init_ident ip` at the address it stores into
    <initproc>.  NOTE: discarding init's `slot_gen` 3/4 makes
    `slot_gen ip (DfracOwn 1)` forever unobtainable -- i.e. allocproc can
    never re-key <init>'s slot.  That is TRUE (init never exits; kexit
    panics on it) and nothing in the tree needs the converse, but say so
    in the note.
  * `SpecUserinit`'s post gains `∃ ip, WaitInv.init_ident ip` beside its
    `∃ v, initproc ↦₈□ v`.
  * `UsertrapRes.ut_names` gains the PURE field `un_ipid : mword 32`;
    `ut_caps` gains `⌜...⌝`-free row `SlotGen.init_pid_is (un_ipid N)` and
    `WaitInv.init_ident (un_ip N)` (both persistent, so `ut_park_caps` and
    the park cost nothing).  Record-building sites: `ProofUserinit`,
    `ProofKforkB5`.

**(2) THE KERNEL ROW AT NUMBERS.**  `UserChildren.wait_ans` gains TWO pure
`mword 32` parameters -- the caller's pid and `ip` -- and the reaping arm's
disjunct is `⌜γ' ∈ cs⌝ ∨ ⌜pidv = ip⌝`; `gen_is_init` stays in
`UserChildren` but is NOT mentioned by `wait_ans`, so **no U-tier file
needs `wchG`**.  `ProofKwait.kw_reap` already derives `gen_is_init gnr`
(patch); convert it with `gen_is_init_pid` against the caller's
`gen_pid gnr pid` (off its block) and `init_pid_is ip`'s agreement, so
`kw_reap` gains ONE persistent premise `init_pid_is ip` and the `ip`
parameter.  Relays that move: `SpecKwait` -> `SpecSysWait` ->
`SpecSyscall.sysc_wait_out` -> `SpecUsertrap.ut_wait_out` ->
`UexecRet.uwait_ans_at`; `ProofSyscall` supplies `ip := un_ipid N` and the
row off `ut_caps`.

**(3) KEEP `uwait_ans`'s ARITY.**  `UkShRun.wp_kshr_wait` and
`UkInit.wp_kinit_wait` mention `uwait_ans r cs cs'` and are IO-LEAF's
files.  Add `uwait_ans_pid r cs cs' pidv ip := ∃ gn b, uwait_ans_at …` and
keep `uwait_ans r cs cs' := ∃ pidv ip, uwait_ans_pid …` -- the SAME trick
T4(c) used for `wp_uk_ecall_wait_null_live` vs `wp_uk_ecall_wait_null`.
Then those two files do not move.

**(4) `ukn_pid` / `upid` (obstacle 2).**  TRAP, measured: a NEW class in
the U tier is exactly what obstacle 1 was about, so `upid`/`upid_auth`
must NOT introduce `ghost_varG Σ (mword 32)`.  `UkRunSys`'s section
already carries `ghost_varG Σ Z` (for `ucwd`) and `ghost_varG Σ (gset
gname)` (for `uch`) -- state `upid` over **`Z`**, at `bv_unsigned pidv`,
and no U-tier section moves.  Five construction sites: `UkRun.v:1526`,
`:1658`, `:1815` (the three `uslot_of_urun*`) and `UkFork.v:1067`, `:1073`.
`uk_names` also gains the pure `ukn_ipid : mword 32`; the CHEAPEST way for
the number to reach the entry constructors is a PARAMETER of
`uslot_of_urun*` (they are already ∀-general in the record they mint) --
NOT a `uvis` field, which would move `UexecSlot`, `UsysMemOk`, every
`bump`/`skey_eq` law and the whole U tier.

**(5) IO-LEAF'S ONE-LINE CHANGES, to be stated and left to them.**  The
entry constructors that hand a program its record --
`UInitKernel`/`UInitSh.sh_slot_of_kexec`, `UShKernel`, `UEchoKernel`,
`USyncKernel`, `UkCat*` -- each gain, at the point they build `uk_names`
or receive `urun`: the fragment `upid (ukn_pid N) p` beside
`uch (ukn_ch N) Sc`, and (for sh) the fork-side `⌜p <> ukn_ipid N⌝` off
init's fork.  They will NOT compile without the `upid` fragment once
`urun` carries the authority, so step (4) and step (5) must land together
or `urun`'s new conjunct must be introduced behind a `∨ True` for one
milestone.  IO-LEAF M5 is editing `UShKernel.v`/`UInitSh.v` right now.

## REBASED TO `5c48c3aa2` (IO-LEAF M5a), AND WHAT M5b NOW OWNS

`lane/trap-rows-3` = `origin/main` = `5c48c3aa2`, working tree CLEAN.
`t4b-wip.patch` touches NONE of IO-LEAF's files: ProcInv, ProofKexit,
ProofKwait, ProofSysExit, ProofSyscall, SlotGen, SpecKexit, SpecSysExit,
SpecSyscall, UexecApply, UexecRet, UkStep, UserChildren, WaitInv,
Xv6Cameras -- fifteen, all kernel-side.  It still applies.

IO-LEAF M5b is in `UkInitMain.v`, `UkInit.v`, `UInitKernel.v`,
`UInitBoot.v`, `UserConsole.v`.  Checked against the work order:

  * **Step (2) collides, in exactly one file.**  `UkInitMain.v` DESTRUCTS
    `wait_ans`'s two arms directly at `:1536` (`iDestruct "Hans" as (gnw
    bnw rv xs) "[%Hret Hwa]"`), `:1565` and `:1627` -- init reads the
    reaped pid, which is the whole reason it needs the arm open.  Adding
    the two pure `mword 32` parameters to `wait_ans` therefore forces
    those three intro patterns to gain one more binder each (exactly the
    `[%Hcseq %Hrngc]` edit T4(c) already made there).  THREE LINES, all
    inside `wp_kinit_wait`'s caller; nothing else in that file moves.
    Confine the edit to them and say so, or hand the three lines to
    IO-LEAF.
  * **`UkInit.v` does NOT collide** provided step (3) is honoured:
    `:1803` names `uwait_ans ret cs cs'` in `wp_kinit_wait`'s STATEMENT
    only, so keeping `uwait_ans`'s arity (the `uwait_ans_pid` corollary)
    leaves it untouched.  `:66` is a `Require` comment.
  * **`UInitKernel.v` is an entry constructor** and is therefore in step
    (5)'s list -- leave it to IO-LEAF as ruled; the one-line change is the
    `upid (ukn_pid N) p` fragment beside `uch (ukn_ch N) Sc`, plus
    `ukn_ipid := un_ipid` in the record it mints.
  * `UInitBoot.v`, `UserConsole.v`, `EchoLinks.v`, `UShLine.v`: no
    contact with any row in this lane.
