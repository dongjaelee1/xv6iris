# Project: WAIT-EXIT — a child's exit returns its resources to the parent through wait()

**STATUS: DESIGNED, NOT SCHEDULED.** Nothing is owed by it and nothing waits
on it. It was designed on the owner's ruling of 2026-09-09 and never started,
because it depends on L7's user-tier input resource existing to have something
to hand over. Lifted out of [`../completed/app-echo.md`](../completed/app-echo.md) when that project was archived
(2026-09-16), so that an unscheduled design does not get buried in
`completed/`.

WHY IT WOULD MATTER: init's loop is `fork; child: exec("sh"); parent: wait`
forever, and without this, nothing stops wait() returning while the first sh
still runs. The echo theorem as it stands does not need it — its statement is
about the console WIRE against the input discipline, and it is closed
(`UInitBootAdequacy.echo_adequacy_echoΣ`). What this would buy is a theorem
that can say "exactly one reader at a time", which is what a stronger
console-INPUT statement needs.

Prerequisite reading for whoever picks it up: `../design/proc-struct.md` §2
(pid cell ownership), `SpecKexit`/`SpecKwait` headers, `WaitInv`.

#### WAIT-EXIT — DESIGN OF RECORD (2026-09-09, owner asked for design + implementation)

WHAT THE TREE SAYS TODAY (verified).  `SpecKwait.wp_kwait_sconf_body`: the
only thing kwait writes is the four-byte xstate at `addr` (`d <= 4`, `d = 0`
at NULL); the return `rv` is FREE ("nothing in the tree ties a pid to the
private exit-status word a zombie carried").  `UsysMemOk`'s wait row (~222)
relays only the copyout; `UkRunSys.wp_uk_ecall_wait_null` returns at any `r`.
`SpecKexit`: exit closes fds, iputs cwd, `reparent`, wakeup parent, parks
ZOMBIE (`SchedCtx.park_pay ZOMBIE = proc_dormant_noctx` -- the private block
crosses into the slot lock: pagetable, trapframe page, kstack, bslots); the
trap loop's exit row is `emp` (`UexecRet.uexec_dep_F`: "exit returns
nothing").  `SpecKfork`: allocproc → pid in `[1, PIDMAX]`; the child's slot
is the PARENT'S deposit (`sysc_fork_in`/`ut_fork_in`: `uslot (uvis_of
(kfork_child U) sts)`), parked steady (`park_token_park_steady`); kfork
holds `wait_lock` when it writes `np->parent` (`is_lock γw wait_lock_addr
… wait_res_at`, `WaitInv.parents_own ps` = the NPROC parent cells).
`proc_pub` (p->lock payload) holds `p_killed`, `p_xstate`, a quarter of
`p_pid`.  `uvis` (the key) = trapframe, image, perm, sz, `uvis_fd : list
fdstate` (a pure reading of p->ofile), `uvis_cwd : Z`; the program mirrors
each with its own ghost in `urun` (`ufd_auth`, `ucwd_auth`) stepped by the
round's pure rows (`usys_fd_ok`, `usys_cwd_ok`).  Pid uniqueness among live
slots is "a further step nothing consumes" (PidLock header) -- this design
consumes it.

THE DESIGN (revised with the owner, 2026-09-09: ESCROW tokens; every process
tracked; the caller hands nothing in).
- GENERATIONS.  allocproc mints a fresh ghost `γ` for EVERY process (kernel
  cell in the slot; fresh names, nothing reset, freed at freeproc).  The key
  gains `uvis_gen : gname` (own generation) and `uvis_ch : gset gname` (the
  generations of this process's live children, including children reparented
  to it), both pure readings of kernel state like `uvis_fd`; the program
  mirrors `uvis_ch` with `uch_auth (ukn_ch N) S` in `urun` (sixth record
  field, the cwd mold), stepped by the round's row.  `gen_pid γ pid` is a
  persistent fact (a generation has one pid forever).
- FORK.  The parent's fork bundle chooses `Q : Z -> iProp` (generic parents:
  `fun _ => True`).  Parent arm: `r = pid ∗ child_tok γ pid Q` (the parent's
  half of `saved_pred γ Q` + `gen_pid γ pid`), `uvis_ch' = uvis_ch ∪ {γ}`.
  The kernel keeps the other half in the child's slot; the child's slot is
  built by the parent (`uexec_fork_child_F`) at a key with `uvis_gen = γ`,
  `uvis_ch = ∅`, and receives the persistent `my_pay γ Q`.  kfork adds γ to
  `children(parent)` under the `wait_lock` it holds.
- EXIT.  The deposit (`uexec_dep_F` at `USYS_exit`, today `emp`): `∃ Q,
  my_pay (uvis_gen W) Q ∗ Q xs` (generic slots pay it at `Q = True`).  kexit
  stores `exit_tok γ pid xs := saved_pred γ (1/2) Q ∗ Q xs` (the kernel's
  half + the payload: the ESCROW) in the ZOMBIE slot (`park_pay ZOMBIE`);
  `reparent` moves `children(p)` into `children(init)`.
- WAIT, ONE SPEC, TWO ARMS.  (a) `r = pid ∗ exit_tok γ' pid xs ∗ ⌜γ' ∈
  uvis_ch W⌝ ∗ ⌜∀ γ ∈ uvis_ch W, gen_pid γ = pid → γ = γ'⌝` (pid uniqueness
  among live processes -- PidLock's further step, consumed here), row
  `uvis_ch' = uvis_ch ∖ {γ'}`; (b) `r = -1 ∗ ⌜uvis_ch W = ∅⌝`.  Nothing is
  handed in.  THE RULE: `child_tok γ pid Q ∗ exit_tok γ pid xs ⊢ Q xs`
  (agreement of the halves) -- indexed by the GENERATION, not the pid: a
  stale token (child reaped, escrow dropped, pid reused) can never combine.
  sh needs nothing back (its payload for echo is trivial): it drops the
  escrow without comparing pids.  init needs the input resource back: from
  `child_tok γsh pidsh Q`, `γsh ∈ uvis_ch W` (nothing removed it) and the
  uniqueness fact, `r = pidsh` forces `γ' = γsh`; on `r ≠ pidsh` (an
  orphan) it drops the token, as its code does.  Blocking is liveness and is
  not stated.
- GENERIC SLOT / TAINT.  A generic slot pays exit at `Q = True`; a verified
  process that becomes generic (the taint) needs its parent's `Q` payable
  from `T` -- the parent supplies `□ (∀ xs, T -∗ Q xs)` beside `Q`
  (application choice; init/sh choose `Q xs := input-token ∨ T`).  Exec keeps
  `uvis_gen` (the identity survives exec); `my_pay` is persistent so it
  travels for free.
LANES (in order; each a brief; all after ARM-c (1a)):
  WX-KEY: `uvis` gains `uvis_gen`/`uvis_ch`; `uvis_of U sts g cs`; the trap
    route carries them beside `sts`; `kfork_child`, `exec_key`, `bump`,
    `skey_eq`, `urun_eq`; the generation cell at allocproc/freeproc;
    WaitInv's `children_own` + invariant (`γ ∈ children j ⇒ a live-or-zombie
    slot with gen γ and parent j`); PidLock uniqueness; `uk_names.ukn_ch` +
    `urun`'s `uch_auth`; quiet rows everywhere.  Green with no semantic
    change (all sets empty, no token minted).
  WX-FORK: `Q` in the fork bundle, `child_tok`/`my_pay`, kfork/sys_fork/
    dispatcher/round/u-tier fork leaf; generic parents at `Q = True`.
  WX-EXIT: the exit deposit through the route into `park_pay ZOMBIE` as the
    escrow; reparent moves children to init; u-tier exit leaf takes `Q xs`.
  WX-WAIT: kwait/sys_wait return the escrow with the two facts; the row;
    u-tier wait leaf; the combination rule; init's `wp_kinit_wait`; L7 then
    hands the console-input resource as `Q`.
Brief for WX-KEY:.

#### WAIT-EXIT — DESIGN (owner's ruling 2026-09-09): a child's exit returns its resources to the parent through wait()

THE PROBLEM.  init's loop is `fork; child: exec("sh"); parent: wait` forever.
If wait() could return while the first sh is still running, init would spawn a
second sh, which could intercept console input meant for the first, and no
meaningful theorem about input survives.  In proof terms: starting sh means
handing it OWNERSHIP of the console-input resource (the user-tier reading of
L5's `uart_rx_tok`/console ledger -- L7 territory), and init cannot hand it out
twice unless wait() hands it back on sh's exit.  So process exit must be tracked
precisely: when a process exits it can RETURN resources to its parent, and
wait() returns the resources of the reaped pid to the parent.  The same
machinery proves the safety half of what init needs: if a child has not exited,
wait cannot return its pid (the resource has not been deposited), and if the
parent has no other children wait cannot return -1 (the parent holds a child
token the -1 arm's "no children" fact contradicts) -- so init's wait returns
only when sh has exited, carrying sh's resources.  Blocking itself (wait
sleeping until the child exits) is liveness and is not what the WP states; the
safety reading is what the theorem consumes.

WHAT EXISTS TODAY.  `UsysMemOk`'s wait row (~222) says only "copyout of the
zombie's xstate at argument 0, or nothing at NULL"; the return value `r` is
free.  `UkRunSys.wp_uk_ecall_wait_null` (~1479) returns at ANY `r` with the
run unchanged; `UkInit.wp_kinit_wait` (~585) relays it, and init's loop
re-forks on whatever came back.  Kernel side: `SpecKwait`/`SpecSysWait` (wait
walks the table under `wait_lock`, reaps a ZOMBIE child, copies xstate,
`freeproc`), `SpecKexit`/`SpecSysExit` (close fds, iput cwd, `reparent`, wakeup
parent, ZOMBIE, sched), `WaitInv` (the `parent` cells under `wait_lock`;
`parents_own`/`wait_res`), `SpecReparent`.  Fork's row: `kfork_post`'s pid arm
is `1 <= pidv <= PIDMAX` (PID-ROW); uniqueness of live pids is "a further step
nothing consumes yet" -- THIS consumes it.

THE SHAPE (to be designed in full when scheduled).  A per-child EXIT DEPOSIT:
- fork mints, for the parent, a CHILD TOKEN keyed by the child's pid, carrying
  the parent's chosen exit payload `P : iProp` (the resources it expects back);
  the child's slot is built with the matching obligation (its exit must deposit
  `P`).  At the U tier this is the fork leaf's parent arm (`UkFork.
  wp_uk_ecall_fork`: `r = pid` gains `child_tok pid P`) and the child arm's
  slot premise (the child's `urun`/slot carries "exit deposits P").
- exit: `UkRunSys.wp_uk_ecall_exit` takes `P` from the program (sh's proof hands
  back the console-input resource and whatever else the parent lent); the
  kernel's `kexit` contract moves the deposit into the slot's ZOMBIE state
  (a row of `proc_pub`/`SchedCtx` beside `p->state = ZOMBIE`, or a per-pid ghost
  slot the parent's token names), across `reparent` (a reparented child's
  deposit goes to init: init's token set grows -- design the token as
  parent-indexed so reparent re-keys it, or make init's wait accept "any
  deposit" -- decide when scheduled).
- wait: `kwait`'s success arm returns `r = pid` AND the deposit `P` for that
  pid (consuming the parent's token); the -1 arm carries `⌜the parent has no
  live child⌝` (the kernel's `havekids` scan), refutable by a held token; the
  U-tier row `usys_wait_ok` relays both; `wp_uk_ecall_wait_null` returns
  `(r = pid ∧ P) ∨ (r = -1 ∧ no children)`.
- pid uniqueness: tokens keyed by pid need live pids distinct (PID-ROW's
  further step: `allocpid`'s scan guarantees it; carry "no two live slots share
  a pid" in `PidLock`'s payload).
- init: its exec bundle's payload `Pay`/refund carries the console-input
  resource into sh (`init_sh_slot`'s `Pay` is where it enters); sh's exit
  returns it; init's wait gets it back and re-forks with it.  The theorem's
  console-input statement (L7) then has exactly one reader at a time.
NOT SCHEDULED YET ("at some point"); depends on L7's user-tier input resource
to have something to hand over.  Prerequisite reading for whoever designs it:
proc-struct.md §2 (pid cell ownership), SpecKexit/SpecKwait headers, WaitInv.
