# spec-cleanup — generic syscall specs, read first

STATUS: COMPLETE 2026-09-17, modulo the PARKED R-a (owner: "park and
relay") and the relay queue below.  Every lane RD-0..RD-6, RD-TR and
RA-1/RA-3 landed; RA-2 stopped at three engine walls, recorded in
`design/user-read.md` §8.4; RA-4 never launched (nothing to consume).

## EXEC (opened 2026-09-18, owner: "exec is something we could tackle")

Design of record: `design/user-exec.md`.  FINDING: the kernel-side
exec-success spec is ALREADY GENERAL (`exec_slot_pre` over any ELF,
`kexec_image_ok` near-functional, loadability decidable, unverified
targets served by the taint arm); what is pinned is the U-tier
assembly, which fuses three separable obligations — (W) the resolution,
(L) loadability, (E) the exec'd program's entry theorem `image_entry`.
Lanes EX-1 (entry + assembly, zero semantic change), EX-2 (the
FRAGMENT walk supplier — the pin-free route; feasibility check first),
EX-3 (the general argv/path reading), EX-4 (the rule, the test, the
TR figure).  ~~Nothing relay-shaped unless EX-2's share check fails.~~
EX-2's share check FAILED and it is still not relay-shaped: the block
is a standing owner ruling (cross-syscall stability = the tree layer's
exclusivity fact), not a kernel ask.

- [x] **EX-1 ENTRY + ASSEMBLY** LANDED (branch `ex1-entry`).  New
  `iris/ExecEntry.v` — `image_entry_at` / `image_entry` /
  `image_entry_taint`, the two readings of obligation (E), plus
  `image_entry_of_at` / `image_entry_at_of` between them — and
  `iris/ExecBundle.v` — `ex_node_id`, `exec_slot_of_entry_at`,
  `sys_exec_slot_of_entry`, `exec_bundle_of`, `exec_bundle_of_at`, the
  assembly with (W)/(L)/(E) as premises and NO pin anywhere in it.
  `PinnedExec` re-derives at byte-identical statements through the new
  `pobs_node_id`; `UInitSh`, `UShEchoPay`, `UInitBoot` untouched by the
  change and green.  Extracted entries: `UShKernel.sh_image_entry_at`,
  `UInitSh.init_sh_image_entry` (which now IS the constructor that was
  inline in `init_exec_sup_of_sh_slot`), `UShEcho.echo_image_entry`
  with its new pure `echo_room_of_det`.  (L) needed nothing —
  `ElfLoadable.kexec_loadable_of_b` was already the decision lemma.
  Two rulings recorded in `design/user-exec.md` §1: the caller's four
  readings are PARAMETERS of the entry, and the argv reading is INSIDE
  it (without it neither landed entry's room bound is provable).
  `exec_bundle_of` and `pinned_exec_bundle` are closed under the global
  context; the three program entries sit at the standing platform bar.
  Echo audit 14, `make -f CoqMakefile -j16` green whole-tree.
- [x] **EX-2 FRAGMENT WALK** — **STOPPED AT DELIVERABLE 0** (branch
  `ex2-fragments`; notes only, ZERO Rocq).  The pin-free supplier is
  REFUTED in the tree, three ways, all landed: (a) `ic_loaded` and
  `ipool_alloc` carry the era leg at `DfracOwn 1`, so any client `nview`
  share of a live inum is inconsistent (`FsAbs.top_frag_1_nview_excl`,
  `FsAbsEra.ic_loaded_nview_excl` / `ipool_alloc_nview_excl` /
  `apn_pin_loaded_excl`); (b) the read arm's 3/4 is what the ESCROW
  KEEPS (`ic_rd_arm`), the quarter that leaves is the read-locking
  KERNEL thread's (`ic_rd_held`'s `inode_rd_era` at 1/4, produced only
  by `FsAbsEra.inode_rd_era_nview`, borrow-scoped `ilock`→`iunlock`, and
  only at `ProofFileread.v:2374` / `ProofFilestat.v:692`) — so §1's
  feasibility note had the fraction backwards and NOTHING is outstanding
  for a client across an ecall; (c) exec takes the WRITE arm at both of
  its reads anyway — namex's per-hop `ilock` and kexec's own `ilock`
  before `readi` are `Ilock.wp_ilock_tx_sconf` (`ProofNamexEra.v:2631`,
  `ProofNamex.v:2785`, `ProofKexecACode.v:1262`).  A supplier would
  type-check and be vacuous, the fourth such consumer after read's
  `wp_uk_cat_read_learns` and mknod's `mkr_chain`.  NOT A RELAY: the
  owner already ruled (2026-08-28, and `fs-syscall-specs.md` §2's
  "Duration of a held share, honestly") that cross-syscall stability is
  the TREE LAYER's exclusivity fact, not a fraction — so EX-2 re-opens
  in the tree-layer campaign and nowhere else.  The wall, with the
  consequences for EX-3/EX-4 and the TR's fragment sentence, is
  `design/user-exec.md` §4's EX-2 as-landed block.  Mirror: echo audit
  14, whole tree green at `b5fb202cf3` (no Rocq touched).
  ONE OWED ONE-LINER out of it: `FsAbs.top_frag_1_nview_excl` is stated
  at `DfracOwn q` only, so the DISCARDED flavour (`nview_dq Γ
  DfracDiscarded`, which is what `SpecSysMknod.mkr_pin` uses) is refuted
  by the same algebra (`DfracOwn 1 ⋅ DfracDiscarded` is invalid) and by
  no landed lemma — write it if a later lane wants the wall total in
  Rocq.
- [ ] **EX-3 ARGV READING** — STILL OPEN; EX-4's budget went to the rule
  and the TR, and nothing was attempted.  The shape is priced in
  `design/user-exec.md` §4's EX-3 entry: one layout-abstract reading
  (`n+1` `uwordq` vector words at `av + 8i`, each string's `ubytesq`
  bytes and terminator, two range bounds — i.e. `UShEcho.echo_node_img`
  with the offsets abstract), with `UInitSh.init_args_det` (constant
  image, literal addresses) and `UShEcho.echo_args_det` /
  `echo_node_img_of_cmd` (malloc'd node, induction on the count) as
  instances at their statements.  The prize is the agreement lemma that
  would lift `M`/`av` out of `image_entry` and the entry out of the
  key's ∀ (EX-4's §2 block).
- [x] **EX-4 THE RULE + THE TEST + THE TR** LANDED (branch `ex4-rule`).
  New `iris/ExecRun.v` — the U-tier exec rule over
  `ExecBundle.exec_bundle_of`:
  - `sbundle_pay_refR_of_exec` — THE SEAM, one key: an exec bundle at
    `uvis_of_run m pc M pm sz fdv c gn cs pidv false` IS the deposit the
    exec leaf consumes.  Both program supplies ended in these four lines
    inline; it is here once.
  - `uexec_sup_run` / `uexec_sup_run_ids` — the supply: the bundle at
    EVERY key the run may be at, lent the heap and the fd authority (and
    the identity authorities, for a caller that reads the resumed key's
    children set and pid), with `Pay` handed over inside.
  - `wp_uk_ecall_exec_run` / `_ids` — THE RULE: (L) pure, the taint arm
    and `□ (Pay -∗ R)` beside it, ONE continuation (the −1 arm), no
    success case — success is `X` inside `image_entry`.
  - `exec_walk_of` — (W) as one resource, families closed — with its
    two suppliers `exec_walk_of_pin` (`PinnedObs` off `app_inv`) and
    `exec_walk_of_taint`; `ex_start_triv` (`FsAbsEra.ep_start_triv`'s
    missing twin) is proved here rather than in the fs seam.
  - THE CONSUMER TESTS `wp_uk_ecall_exec_pin_test` and
    `wp_uk_ecall_exec_taint_test`, plus `image_entry_of_taint` and
    `uexec_path_reading` (the path read back off whatever heap the run
    is at — the shape both landed programs have).
  THE TWO PROGRAM SUPPLIES ARE NOW INSTANCES, at their exact statements:
  `UInitSh.init_exec_sup_of_sh_slot` through
  `udepw_at_refR_ids_of_sup_ids`, `UShEchoPay.sh_exec_sup_echo_wq_holds`
  through `udepw_at_refR_of_sup`; each still spells only its own
  readings.  `sbundle_pay_exec_intro_refR` MOVED from `UInitSh` (a
  program file) to `ExecRun` at its exact statement — `UShEchoPay` gains
  the import.  NO SEAM GAP: neither program's exec site consumes
  anything the rule does not offer.  `Print Assumptions`: the seam
  `sbundle_pay_refR_of_exec` is CLOSED UNDER THE GLOBAL CONTEXT; both
  rules and both consumer tests sit at the standing bar (the two Sail
  platform axioms + funext, no `PrimInt63`/`PrimString`).  TR: `xv6iris-doc` `63d2ff8`, `fig:uk-exec` in
  `user.tex` §7 with the entry-as-theorem prose, the taint reading, and
  the pin-free supplier as FUTURE work gated on the tree layer.
  Also fixed `design/user-write.md`'s "the read side has no such wall"
  misreading (twice: the design page and this worklist's RD-6 entry).
  `iris/_CoqProject` gains `ExecRun.v` — the gate must regen
  `CoqMakefile` (it does).  Mirror: whole tree green, echo audit 14.

## NEXT (owner ruled 2026-09-17: "ex-3, the wait/kill pair, and the tree-layer campaign")

In order: EX-3 (LAUNCHED, Opus, branch `ex3-argv`, brief
`brief-ex3-argv.md`) → RD-7 WAIT (a real status pointer: the kernel
writes the child's exit status to user memory — the read/write
"kernel writes user memory" row pattern) + RD-8 KILL (per-PID spec in
place of the global predicate the TR flags) → the TREE-LAYER campaign
(`design/fs-syscall-specs.md` §6: the client-visible fs vocabulary and
the cross-syscall exclusivity that makes "I know what this file is" a
resource — what unlocks pin-free exec, per EX-2).  Briefs for RD-7/8
and the tree-layer design page follow while EX-3 runs.

## RELAY QUEUE (for upstream, via the owner's push)

1. **The R-a walls + the `uheld` proposal** (`design/user-read.md`
   §8.4): offset ownership needs one of — a per-process held-set
   resource `uheld γ H` beside `ucwd`/`uch` (in/out on fork/exec), a
   deposit-capable fork (out of `free_num`), or a tier index on
   `sysc_fd_ok`'s parked conjunct.  All engine-design calls.  Every
   supporting lemma is landed and closed (`FdPark.v`, `UserOff.v`);
   the resume worklist is the 13 grep-able markers.
2. **The pipe queue ghost** (`design/user-read.md` §3 RD-5 block +
   `design/pipe.md`'s own hooks): contents-indexed pipe refinement
   would make read's/write's pipe arms content-carrying; plus the
   pipe EOF row.
3. **The count/window join** at the pipe read receipt, and **row 16's
   missing return blanket** (`design/user-write.md`): one conjunct
   each, wide cones, both priced in the design pages.

OPENED 2026-09-15 (owner: "focus on cleanup... the read system
call spec needs generalization... a generic read spec... will allow us
to prove more user level applications correct").  Goal: the syscall
specs the echo theorem runs on are tailored to echo and its string;
re-cut them so each syscall has ONE general, application-independent
spec, with the echo/sh leaves as INSTANCES.  Read is the pilot; write
follows on the same pattern.  The tech report is the aesthetic bar: the
end state of each spec should be presentable as a figure in
`/shared/xv6iris-doc/tr/user.tex` (§7) — but the tree's version is the
deliverable, the TR only records it.  The TR already names one defect
in read's figure (`\nz{fix up spec: actually give ownership of offset
to user-level proof}`); lane RD-1 is that fix.

EXECUTION NOTE: proof lanes are gated on a build mirror (none since
~2026-09-10); RD-0 (design) proceeds without one.

## The inventory — where read's spec lives today, and what is tailored

Four read-shaped statements, three tiers:

1. **Kernel AU spec** (`SpecSysRead.v`, `SysReadDefs.v`,
   `FsAbsReadFire.aread_commit_at`, `OffGv.v`, `FileOffCell`): the
   atomic-update spec against the fs abstract state (`aview`), caller
   picks `Φ`, `ard_pre`/`ard_count`/`ard_ret_tie` name the returned
   bytes for the INODE arm.  Already general in `Φ` — this is the shape
   the TR's fig shows.  Its defect is the OFFSET: the user half of
   `off_gv` is parked in a persistent, existential-valued invariant
   (`off_user_inv` — "its offsets are anybody's"), so a user-level
   proof cannot know its own file position.  fileread's commit LENDS
   the kernel half and takes it back unmoved; the fire advances it
   against the parked invariant.
2. **U-tier base leaf** `UkRunSys.wp_uk_ecall_read` ("cat's"): exact
   count owned, buffer returned at UNCONSTRAINED contents, return value
   untied to the delivered count.  General but too weak to prove any
   program that looks at what it read.
3. **U-tier window leaf** `wp_uk_ecall_read_win` (sh's `getcmd`
   shape): any owned run covering the count, written prefix `d` with
   the tail pinned — still no contents, no `r`/`d` tie.  Its header
   already records the merge debt with (2): "the two should eventually
   merge (this one generalizes)".
4. **U-tier recv leaf** `wp_uk_ecall_read_recv` (+ its sh wrapper
   `UkSh.ush_read_recv_leaf`, paid by the era's console link/lease —
   IO-LEAF M5): the ONLY content-carrying read.  It keeps the kernel's
   post (`spost_at`) instead of dropping it — that machinery is
   general and is the seed of the target spec — but everything around
   it is console-fixed: the deposit is ledger-fixed to the console arm
   (`udepwf_std` + `ustd`, the console reader token), the post is
   `SpecFileread.console_receipt`, and the wrapper is paid out of the
   ECHO APPLICATION's era claims.  This is where "tailored to echo and
   the string it is printing" lives.

The general principle, extracted: TAILORING = (a) the content-carrying
post exists only on the console path, (b) the payment for it is the
application's own machinery, (c) the offset knowledge a file-arm post
would need is parked out of reach.  The fix is one leaf whose ARM is
chosen by the caller's own descriptor knowledge, whose content post
comes from the kernel AU spec's `Φ` at every arm, and whose per-arm
payment is a resource the PROGRAM owns (offset half, console claim,
pipe end) — with the anybody's forms remaining as the opt-out for
unverified processes.

## The target — the generic read spec (what §7 of the TR should show)

    caller owns:  buffer run of k ≥ cnt bytes at a1 (window form)
                  a descriptor handle: ufd fd st        (kind decides the arm)
                  the arm's resource:
                    Inode i γo:  uoff γo off  (the OWNED user half — RD-1)
                                 + aread_commit Φ  (AU against aview; caller's choice)
                    Console:     console-input AU  (against the merged IO
                                 claim, post-R1 — NOT echo's era ledger)
                    Pipe:        pipe-read AU (the read end's bytes)
    returns:      r = d ≤ cnt, written prefix at named bytes, tail pinned,
                  arm content:  File bs → d = min(cnt, |bs| − off),
                                bytes = bs[off .. off+d), uoff γo (off+d)
                                + Φ av off a d
                  and the fd handle back unchanged (read retypes nothing)

Derived corollaries, in order of what applications actually use:
- **the owned-offset file read** (unshared descriptor): no AU visible at
  all — `uoff` in, bytes and `uoff` bumped out.  This is the TR figure.
- the shared-descriptor form keeps the AU on (off, aview) jointly — the
  honest general case; the current parked-invariant behaviour is the
  `Φ := True` instance.
- sh's line read = the console arm at the echo application's claims
  (today's `ush_read_recv_leaf`, re-derived as an instance).

## Lanes

- [x] ~~**RD-0 DESIGN**~~ LANDED 2026-09-15 (`design/user-read.md`):
  (a)–(d) all written; ONE OWNER RULING OPEN — fork vs. owned offset
  (§4 there; recommendation = fork parks every held `uoff`, the
  fractional route recorded as the escape).  RD-1's brief is cut from
  its §2, RD-2's from §3+§5, RD-TR's figure from §6.  Original scope:
  (a) OFFSET OWNERSHIP: `off_gv`'s user half becomes a holdable linear
      resource `uoff γo off` minted to the caller at sys_open's publish;
      `off_user_inv` (the parked form) stays as the opt-out a process
      can park INTO (one-way: own → parked; never back — parked is
      persistent).  FORK RULING NEEDED (owner): a forked child shares
      the open file, so an owned `uoff` cannot be duplicated — options:
      (i) fork parks every owned offset (child+parent both drop to the
      anybody's form — simple, matches Unix sharing semantics), or
      (ii) the half is fractional over the SHARING SET and reads keep
      an AU on it — general but heavy.  Recommendation: (i); a program
      that forks around a shared offset is exactly the racy case the
      AU form exists for.
  (b) ARM DISPATCH: the U-tier leaf cases on the caller's own
      `fdstate` (the handle's kind), the way close/dup rows already do;
      the deposit-family naming that `read_recv` needed (`udepwf_std`)
      generalizes to "ledger-fixed at the arm the handle names".
  (c) THE Φ CHANNEL: how `aread_commit_at Γ E i γo Φ` rides the trap
      row to the U tier — the recv leaf's kept-post walk is the
      mechanism; what changes is only WHICH receipt (`console_receipt`
      → per-arm receipt family).
  (d) the TR figure sketch (both forms: general AU + owned-offset
      corollary), so the end state is agreed before proof work starts.
- [x] **RD-1 OFF-OWN** (kernel; LANDED 2026-09-15, branch
  `rd1-off-own`, mirror-green incl. `ProofFileread`/`ProofFilewrite`
  and the echo audit at 14): implemented (a) —
  `uoff`, fileread's/filewrite's fire against a HELD half (both halves
  in hand: no invariant open), fork per the ruling; the generic-WP path
  keeps `off_user_inv` untouched, byte for byte.  WHAT LANDED:
  - `iris/UserOff.v` (NEW, above `OffGv.v`): `uoff γo off`, `uoff_park`
    (the one-way door, `={E}=∗` — invariant allocation is a fancy
    update), `uoff_advance`, `uoff_agree`/`uoff_agree_k`, the supplier
    `off_supply γo E off d R` with its two answers
    (`off_supply_parked` / `off_supply_held`), and the publish's two
    modes `off_pub_park` / `off_pub_hand`.
  - ONE FIRE, TWO SUPPLIERS, in all three fires:
    `FsAbsReadFire.arf_read_fire_gen` + `_held` (+`_held_1`),
    `FsAbsWriteFire.wrf_awrite_fire_gen` + `_held`,
    `wrf_apart_fire_gen` + `_held`.  The four existing names
    (`arf_read_fire`, `arf_read_fire_1`, `wrf_awrite_fire`,
    `wrf_apart_fire`) keep their EXACT former statements as the parked
    instances, so `ProofFileread`/`ProofFilewrite`'s four call sites and
    every contract above them are untouched.  `aread_commit_at` and the
    write chain's two arms keep their types: they still LEND the kernel
    half unmoved, so `fs-syscall-specs.md` §4 holds — the half that
    moves client-side is the CLIENT'S OWN `uoff`.
  - `ProofSysOpenPub.v`'s publish now names its mode
    (`off_pub_park`); behaviour identical.
  - `Print Assumptions` on all 17 new/re-derived lemmas: **closed under
    the global context** (not even funext).
  THE ONE DEFERRAL, and RD-2 must rule on it: **mode `hand` cannot be
  wired to the descriptor bundle yet.** `FdSlots.foff_row` is a pure
  function of the fdstate AND persistent, so a descriptor whose half was
  handed out has no invariant and no row — wiring `hand` is a change to
  the ROW FAMILY (the per-row policy `FdSlots.v` already anticipates),
  cheapest as the mode IN THE STATE, which is also §3's arm dispatch for
  free.  See `design/user-read.md` §2/§4 as-landed notes and the trailing
  notes in `UserOff.v`.  FORK: the kernel owes NOTHING (checked:
  `ProofKforkB3` takes the parent's row persistently), so deliverable 5
  is the park lemma + a U-tier statement-side obligation for RD-2.
  This lane discharges the TR's `\nz` note.
- [~] **RD-2 FILE-LEAF** (U tier; branch `rd2-file-leaf`, 2026-09-15):
  **RE-SCOPED BY A FINDING — the mode-in-state ruling is not
  implementable as scoped, and RD-2 stopped rather than restructure the
  generic-safety tier.**  Full argument in `design/user-read.md` §3's
  AS-LANDED block; one-line version: a HELD offset half has to reach
  `ProofFileread`'s fire, the only channel into it is
  `SpecFileread.fileread_in`'s inode arm, and that arm must be payable
  at EVERY descriptor state from a PERSISTENT credential because
  `UexecSG.sbundle_of_supply_ne` is a class field at an arbitrary key
  (`FsAbsInvFire.fsabs_fileread_in`, `∀ st`, `□ ssupply`).  An exclusive
  `uoff` there is not merely unavailable, it is inconsistent.  Two extra
  consequences the ruling had not priced: with the mode in the state,
  PARKING becomes a descriptor retype (a kernel step — xv6 has no park
  syscall), and `ProofKforkB3` cannot copy a held row (it hands the
  parent's row to the child persistently, at an arbitrary `sts`).
  THREE ROUTES OUT are written up in §3: **R-a** mode in the state +
  a parked-table discipline through the generic tier and a
  mode-parameterized sys_open publish (a campaign: `SpecSysOpen`'s 15
  sites + six `ProofSysOpen*` files + `ProofKforkB3` + the class field
  and its consumers) — the only route that delivers §6's figure;
  **R-b** the mode-free disjunctive row (recorded escape, does not
  deliver the File row); **R-c** the file-arm leaf AT A PARKED
  DESCRIPTOR with the offset REPORTED by the receipt instead of owned —
  zero kernel change, delivers §3's whole File CONTENT row and the
  `cat` consumer today, and upgrades to R-a later by one conjunct.
  **RD-2 TOOK R-c AND LANDED IT** (`iris/UkReadFile.v`, mirror-green,
  whole tree; `Print Assumptions` at the standing bar — and
  `read_arms_file_learn` is CLOSED UNDER THE GLOBAL CONTEXT):
  `udepwf_st` (§3's arm-indexed deposit — the STATE-fixed third sibling
  of `udepwf_at`/`udepwf_std`) + `udepwf_st_read_file` (its supplier:
  ONE observation commit and nothing beside it), `xfam_rdf` /
  `read_file_fam`, `wp_uk_ecall_read_file` (the leaf: recv's walk with
  the post kept, at the file arm — which CHECKS §5's claim that recv's
  six bridge rows are arm-independent), `read_arms_file_learn` (§3's
  File row: `r = min(cnt, |bs| − off)` and the bytes ARE
  `bs[off, off+d)`), and the consumer test `wp_uk_cat_read_learns`.
  R-a IS STILL OWED as its own campaign — it is what buys the PREDICTED
  offset, §6's figure and the TR's `\nz` note.  OWNER RULING WANTED on
  whether to schedule it.
  ALSO LANDED: RD-3 below (folded in as briefed), and §3/§5's
  as-landed blocks.  Also recorded in §5: the "receipt family indexed by
  the arm" needs NOTHING new — the inode member IS
  `FsAbsReadFire.read_arms` and the family IS
  `SpecFileread.fileread_extra_core`; only the DEPOSIT needs a new
  member, fd-fixed rather than ledger-fixed (`udepwf_fd`, since
  `udepwf_at` already names the cwd-fixed form).
- [x] **RD-3 BASE/WIN MERGE** — LANDED 2026-09-15 on `rd2-file-leaf`
  (folded into RD-2 as briefed).  `UkRunSys.wp_uk_ecall_read` is now a
  COROLLARY of `wp_uk_ecall_read_win`, at its exact former statement
  (so `UkCat`'s read stub and every other caller is untouched); the
  130-line walk is retired and upstream's relay note in that file is
  closed.  The derivation's one real step is the ADDRESS SPELLING —
  the base leaf names its buffer by a `Z` tied to a1 through
  `mword_of_int`, the window leaf by `uint` of the register — which is
  paid by a new accessor `UkRunSys.urun_ubytes_run` (the no-wrap fact
  read off `urun` rather than off the heap `urun` binds
  existentially); at a count of ZERO no byte is owned, no agreement
  exists and none is needed, since both spellings of an empty run are
  `emp`.  Mirror-green (whole tree).
- **R-a CAMPAIGN OPENED 2026-09-16** (owner's word; design =
  `design/user-read.md` §8: the all-parked generic tier beats the
  supply-law wall on the console arm's disjunctive precedent; boundary
  parks ride fork/exec's own kernel step).  Lanes RA-1..RA-4 listed
  there; RA-1 (offmode + all-parked + class-field premise, zero
  semantic change) LAUNCHED 2026-09-16, Opus, branch `ra1-offmode`,
  brief scratchpad `brief-ra1-offmode.md`.
- [x] **RA-1** LANDED (branch `ra1-offmode`): the STATE half at zero
  semantic change, bought by the `fdstate_ok` pin; the class-field
  premise did NOT land and re-scoped the lanes to RA-3 → RA-2 → RA-4.
  See `design/user-read.md` §8.1's AS-LANDED block for the three
  findings.
- [x] **RA-3 BOUNDARY PARKS** (LANDED 2026-09-16, branch
  `ra3-boundary`, mirror-green whole tree, echo audit at 14).  Design
  of record: `design/user-read.md` §8.3's AS-LANDED block.  WHAT
  LANDED: `iris/FdPark.v` — `fdst_park`/`fdv_park` and their laws, the
  surrender (`uoff_surr`/`uoff_surrs`, a big-op that quantifies over
  the held subset and degenerates to `emp`), §8.3's one park step
  (`foff_rows_park`), the retype (`fd_frags_park`, `fd_st_move` per
  row), and **the boundary slot `uoff_surr_at = ⌜all parked⌝ ∨ the
  halves` with ONE step and TWO suppliers (`fd_frags_park_at`)** — the
  console arm's disjunctive precedent at fork and exec.  Plus the
  `usys_fd_ok` OPEN-ROW CONJUNCT (`fdst_parked (FdOpen rd wr t)`,
  carried out of the arms by `open_arms_*_split`; `usys_fd_ok_parked`
  is now premise-free, `_ne_open` deleted), and BOTH CROSSINGS proved:
  fork's `ProofKforkB3.kfk_at_parked` and exec's
  `SpecKexec.kexec_image_ok_parked` / `exec_key_ok_parked`.
  THREE FINDINGS THAT RE-SCOPE, all in §8.3's block: **(A)** the array
  half of the retype is UNINHABITED under the pin (`ofile_slot` shares
  its `st` with `file_ref`, which carries `fdstate_ok`), so it cannot
  be written before the pin is relaxed; **(B)** the SURRENDER SLOT'S
  PLUG-IN cannot precede §8.1's class premise, from either end — the
  deposit end because `xv6_sbundle_of_supply_ne` pays at an arbitrary
  key, the U-tier end because a `ufd` at a held state is not refutable
  there (the brief's STOP fired at `UkShRun.wp_kshr_fork`, whose
  descriptor map is universally quantified); **(C)** there is NO U-TIER
  CARRIER for "my whole table is parked", which three of the five mint
  sites need — `ustd` pins the low `NSTD` slots and `ufd` pins named
  ones, and nothing pins the rest.  **(C) IS AN OWNER DECISION ON THE
  CRITICAL PATH.**  Consequence for the campaign: everything that
  remains is RA-2's ONE commit; `grep -rn 'RA-2: held case here' iris/`
  is its worklist, left in the tree at each attachment point.
- [~] **RA-2 THE ONE COMMIT** (RAN 2026-09-16, branch `ra2-onecommit`,
  mirror-green whole tree, echo audit at 14).  **THE SEMANTIC CHANGE DID
  NOT LAND: three walls, each checked at the statement, all in
  `design/user-read.md` §8.4's AS-LANDED block.**  **(1)** `hand` at open
  is REFUTED BY RA-3's OWN landing — `UsysMemOk.usys_fd_ok`'s open arm
  pins `fdst_parked` on the ACTUAL successor table and that relation is
  threaded for BOTH TIERS with no tier index (`SpecSyscall.sysc_fd_ok`,
  `SpecUsertrap`), so a held open kills `ProofSyscall`'s arm 15 and the
  three `open_arms_*_split`; the conjunct cannot come off because the
  generic Löb step reads successor-parkedness off it (RA-1's finding 3),
  so the carrier must first move to the slot's post
  (`UexecSG.spost_at`'s `fdv'`, chosen by the family) — a new lane, RA-5.
  **(2)** Relaxing the pin DELETES `ProcInv.proc_priv_parked`
  (`fdstate_ok_parked` → `file_ref_parked` → the export is the pin, in
  three steps), which is the ONLY supplier of §8.3's premise on
  `SpecKexec.exec_slot_pre`'s wands — change (1) of the commit refutes
  change (3) of the same commit; the replacement is to discharge from the
  POST-PARK table (`fd_frags_park_at`'s `⌜fdv_all_parked sts'⌝`), which
  restates the wands and moves every applier.  AND the check RA-3 left for
  RA-2 comes back NO independently of the pin: `proc_priv_parked` needs the
  block AND the bundle, the block is in scope at the wand applications
  (`Hpriv`) but `fd_frags` occurs **zero** times in the whole kexec chain
  (`SpecKexec`, `ProofKexec*`, `KexecOkQ`, `KexecBridge`) — it is on the
  syscall channel one layer out (`UsertrapRes.ut_own`, `ProofSyscall`), so
  it is a new parameter through that chain, not the local step finding C
  assumed.  **(3)** THE STOP: fork is a
  FREE number (`UexecSG.free_num` excludes only exec/5/6/15..20), so its
  `xv6_sbundle` arm is `emp`, and `UkFork.wp_uk_ecall_fork` takes NO
  deposit premise — it mints from the law packed inside `UkRun.urun`
  (`udep_dep`), and that law is **a PURE proposition** (`UkRun.udep`'s
  second conjunct, inside `⌜ ⌝`; `udep_free` proves all of it from
  nothing), so it can carry neither a resource nor a key-indexed fact at
  any key.  The surrender slot therefore has NO PAYER — it forces fork out
  of `free_num` and every site onto the explicit route, where a verified
  program holds nothing about its table — and the class premise does not
  reach it (it lands on the supply law, the generic tier's route) — which
  CORRECTS §8.3's finding B:
  the U-tier wrappers cannot discharge once the premise exists, they
  cannot discharge at all.  **ROUTE OUT, and it supersedes finding C's
  "no carrier exists": a U-tier HALF OF THE HELD SET (`uheld γ H`), the
  third sibling of `UserCwd.ucwd` / `UserChildren.uch`** — a program that
  never opened at `hand` holds `H = ∅` and can SAY so at the leaf, which
  is not RA-1's finding-2 brute fix (it makes no program unable to hold a
  `uoff`).  OWNER DECISION: a fourth piece of per-process U-tier state,
  plus an in/out pair on every fork/exec wrapper.  LANDED instead, zero
  semantic change: `iris/FdPark.v` §6 — the arm split's kernel half
  (`uoff_rcpt`, `uoff_rcpt_surr`, `off_supply_of_st{,_eq}`: row + payment
  + the kernel's own half give the fire's supplier and its receipt at BOTH
  modes in one statement), and the finding that §8.2's arm payment and
  §8.3's boundary surrender are THE SAME PROPOSITION at one row.
- OWNER RULED 2026-09-15: BREADTH FIRST — RD-4/RD-5/RD-6 on the landed
  R-c pattern; route R-a (the owned-offset campaign) queued behind them,
  upgrading each arm by one conjunct when it runs.
- [x] **RD-4 CONSOLE ARM** (LANDED 2026-09-15, branch rd4-cons-arm,
  mirror-green whole tree, echo audit at 14): the console arm is
  `iris/UkReadCons.v` (`wp_uk_ecall_read_cons`,
  `udepwf_std_read_cons`, `uread_cons_ans`), and the judgment the lane
  owed is that **the input side was ALREADY NEUTRAL** — one level BELOW
  the merged claim.  `SpecFileread.fileread_in`'s console arm is
  `ConsoleInv.cons_acc` (the ring) beside `WpUart.cons_read_pay`, and
  `cons_read_pay` IS ConsLog's `EvRead` event as an atomic update
  (`read_link`'s premise is `ConsLog.read_ok pops dl ws` =
  `cons_ev_ok H (EvRead ws)`; its conclusion is `dl ++ ws` =
  `cons_step H (EvRead ws)`).  Echo enters only as the caller's choice
  of `Rd`/`Rin`, so NOTHING had to be factored out of `EchoOut.v` and
  nothing there was touched; the merged claim (`ecl`, `ecl_step_read`)
  is one ANSWER to this AU and the arm does not wait on it being wired.
  `UShLine.ush_read_recv_era`'s console branch is now a wrapper
  (`ush_read_pay_era` answers both payments off sh's lease;
  `ush_read_sup_era` is the neutral supplier at echo's `Rd`/`Rin`), and
  `UkSh.ush_read_recv_leaf` / `ush_read_recv_leaf_holds` /
  `ush_read_ans_era` keep their exact statements.
  AND THE READ WALK IS NOW ONE: `UkRunSys.wp_uk_ecall_read_at`,
  parametric in the caller's descriptor resource `D` and the pure
  reading `K` it buys, with `UkRunSys.udepwf_K` the deposit at the same
  reading; `wp_uk_ecall_read_recv` (ledger) and
  `UkReadFile.wp_uk_ecall_read_file` (handle) are its two corollaries
  at their exact former statements, and ~150 duplicated lines of walk
  are gone.  `iris/UkReadRows.v` is the shared home RD-2's report asked
  for: the `sbundle_at_read_intro` / `spost_at_read_elim` pair (two
  word-for-word copies before), the `xfam_rd` / `xfam_rdf` family pair
  (which ARE the two arms), the two `fd_st_of_key` readings and the
  count's sign-boundary bridges.  Design of record: `design/user-read.md`
  §3's RD-4 AS-LANDED block and §5's.
- [x] **RD-5 PIPE ARM** (LANDED 2026-09-15, branch rd5-pipe-arm,
  mirror-green whole tree, echo audit at 14): the pipe arm is
  `iris/UkReadPipe.v` (`wp_uk_ecall_read_pipe`, `udepwf_st_read_pipe`,
  `uread_pipe_ans`, `upipe_ends_handles`, `wp_uk_pipe_read_end`), and the
  judgment the lane owed is the OPPOSITE of RD-4's: **the pipe arm's
  payment is NOT already an AU on the queue, because THERE IS NO QUEUE
  GHOST.**  `PipeInvDefs.pipe_names`' four gnames are all about the ENDS
  (two reference fractions, two open marks); the ring's contents are the
  `bs` bound existentially inside `pipe_res_at`, under the pipe's own
  spinlock, and the queue coupling is deliberately not imposed
  (`design/pipe.md`: "the CONTENTS of the live window stay existential …
  the hooks a future contents-indexed refinement builds on";
  `SpecPiperead`: "`bs` … which no contract at this tier can name").  So
  the kernel's read contract at a pipe is a no-op on both sides —
  `fileread_in` at `FdOpen true _ FdPipe` is the `_ => P` arm and
  `fileread_extra_core` there is `emp` — and §3's Pipe row is today
  exactly its **Dev (other)** row.  WHAT LANDED at that honest strength:
  the supplier proved FROM `emp` (a pipe read costs its caller nothing
  beyond its handle — §1's principle at its limit case), the pure content
  post `uread_pipe_ans` = `pipe_rw_ret` at the caller's own `nat` count
  (-1 is not refuted, correctly: `uexec_live_ok` refutes it only at the
  console), and the member as `UkRunSys.wp_uk_ecall_read_at` at the handle
  reading — the walk's `D`/`K` FIT the pipe handle with nothing added, so
  the brief's STOP rule did not fire.  OWED, BOTH KERNEL-SIDE: the EOF row
  (a fact about `pipe_endstate` and the counters, under the lock) and —
  sharper — the COUNT/WINDOW JOIN, the exact analogue of `UsysMemOk`'s
  SS2c: the inode and console arms tie the window length `d` to the return
  value `r`, the pipe arm ties nothing, so a pipe reader cannot conclude
  its buffer above `r` is unchanged.  The consumer test is the SEAM, not
  the bytes (neither a two-process nor a one-process write-then-read
  content fact is derivable): `wp_uk_pipe_read_end` reads
  `wp_uk_ecall_pipe`'s post one step further into the two members' own
  premises, handing out `ufd a (FdOpen true false FdPipe)` and `ufd b
  (FdOpen false true FdPipe)` — **RD-6 should take the write end from
  there, and should expect the same wall**: `SpecFilewrite.filewrite_env`
  and `filewrite_extra` are BOTH `emp` at `FdOpen _ _ FdPipe` (checked, so
  RD-6 need not re-survey), so the write member is this one's mirror image
  — supplier from `emp`, pure `filewrite_ret` post, same two owed rows.  Housekeeping NOT done, with the reason: the lower home for
  `UkReadRows.uread_count_le` / `UkSh.ush_narrow_count_le` is `UserBits.v`
  (41 importers), a whole-tree rebuild for zero proof content.  Design of
  record: `design/user-read.md` §3's RD-5 AS-LANDED block and §5's.
- [x] **RD-6 WRITE** (LANDED 2026-09-15, branch `rd6-write`,
  mirror-green whole tree, echo audit at 14): the same programme for
  write, and it needed a NEW DESIGN PAGE —
  **`design/user-write.md` is the design of record** (why a sibling and
  not a §8 of `user-read.md` is its own opening paragraph: the tailoring
  is on the OUTPUT side, and write's arms report through a CHAIN THE
  CALLER BUILDS where read's report through a RECEIPT THE KERNEL FILLS).
  THE SURVEY'S ONE-LINE ANSWER: **write's spec was already general in its
  PAYMENT and not general in its ARM**.  `SpecFilewrite.filewrite_in`'s
  two heavy arms are both a chain over the caller's own prefix cursor
  `Q` (per CHUNK on the inode arm, per BYTE on the console arm) since
  lane OUT-FUPD retired the located receipts, and `UkWriteLeaf.v` — the
  write-side `UkReadRows.v` — was cut application-free from the start,
  so echo's and sh's output leaves (`UEchoOut`, `UShOut`, `UShPanic`,
  `UInitBanner`, `UInitDiag`, `UkWriteClosed`) were ALREADY INSTANCES and
  nothing was touched in any of them.  Upstream's word-list
  generalization de-tailored the CALLER (`UEchoOut`/`EchoDisc`/
  `UkShEcho`), not the spec, and left this ground untouched.  What was
  missing was §3 of `user-read.md` at the write side: all three U-tier
  write leaves were LEDGER-fixed, so **no U-tier write could reach the
  INODE arm at all**.  WHAT LANDED:
  - `UkRunSys.wp_uk_ecall_write_at` — THE ONE WRITE WALK, the read
    walk's twin: parametric in `D`/`K` (the same `udepwf_K`, which was
    already syscall-generic) and, additionally, in the caller's SOURCE
    RUN `S` through a new reading `UkRunSys.usrc_ok` (the IMAGE row —
    "the key's image along the run IS my bytes", new, and the piece the
    file arm was missing — beside the MAPPED row the buffer leaf already
    had), with `usrc_ok_ubytesq` / `usrc_ok_utext` its DATA and TEXT
    answers.  `wp_uk_ecall_write_chain_buf` and `_txt` are now its two
    corollaries at their EXACT former statements, so every program stub
    and every application file is untouched; ~150 duplicated lines gone.
  - `iris/UkWriteCons.v` — the console member assembled with the short
    arm ALREADY REFUTED (`wp_uk_ecall_write_cons`: a console write of a
    run the program owns returns the FULL count and the caller's own
    cursor at it) plus `wp_uk_ecall_write_cons_licence`.  The payment is
    `WpUart.out_link` per byte — the console history's OUTPUT event as an
    atomic update, the exact mirror of RD-4's `cons_read_pay`/`read_link`
    finding on the input side.
  - `iris/UkWriteFile.v` — the file member: `udepwf_st_write_file` (ONE
    chunk chain and nothing beside it), `wp_uk_ecall_write_file` (the
    one walk at the HANDLE reading), `write_arms_file_learn` (**the
    bytes the kernel committed ARE the program's own**, via the new
    image row and the one-line bridge `ubytes_at_src`; CLOSED UNDER THE
    GLOBAL CONTEXT), and the consumer test `wp_uk_write_file_lands`.
  - `iris/UkWritePipe.v` — the pipe member: supplier from `emp`
    (§1's principle at its limit case), and `wp_uk_pipe_write_end` at
    exactly the handle RD-5's `wp_uk_pipe_read_end` hands back.
  - HOUSEKEEPING TAKEN (RD-5 recorded it): `UkReadFile.udepwf_st`,
    `udepwf_st_K` and `ufd_key_agree` MOVED to `UkReadRows.v`, at their
    exact statements — they are syscall-independent as well as
    arm-independent, and the write walk invalidated that cone anyway.
  TWO FINDINGS THAT RE-SCOPE, both written up in `user-write.md`:
  **(i) A PROGRAM CANNOT HOLD A PIN ACROSS ITS OWN WRITE**, so the
  cat-shaped dual is not merely missing, it is VACUOUS: the kernel's
  mover needs the WHOLE γtop element to update the row, and that is what
  `IcacheEscrow.ic_loaded` holds while the inode is ilock'd
  (`FsAbs.top_frag_1_nview_excl` is the algebra), so any client `nview`
  share contradicts the chain node's own premises.  (The read side has
  the SAME wall — EX-2 refuted the "its arm leaves a client share
  outstanding on purpose" reading: the 3/4 is the escrow's, the quarter
  that leaves goes to the read-locking kernel thread, and nothing
  crosses an ecall.  What read has is that its STATEMENT stays true when
  the anchor arrives.)
  What is NOT missing is the R-c pattern: `awrite_full_at`'s phase 1
  already hands the caller the offset, the chunk bytes AND the row's
  pre-content (`FsAbsWriteFire.wri_pre`), and phase 2 the delta, all in
  scope where `Q (S k)` is built — so a cursor CAN record what happened
  per chunk.  What is missing is the ANCHOR for the first chunk's
  pre-content, and the tree's candidate is the caller's own
  `AppInv.app_step` claim.  Cutting that anchored cursor is the write
  side's R-a — a campaign, and it wants an owner ruling on the anchor.
  **(ii) ROW 16 CARRIES NO RETURN BLANKET.**  `UexecExecInst.xv6_spost`'s
  read row has `⌜fileread_ret …⌝` beside the extra and the write row
  deliberately does not, so at a PIPE (where the arm is `emp`) a U-tier
  write learns NOTHING about `r` — not even that it is `-1` or in range.
  One conjunct to fix, a wide cone to land; owed, named, priced.
- [x] **RD-TR** LANDED 2026-09-16 (xv6iris-doc `e5859f3`; user.tex §7):
  fig:sys-read KEPT as the general kernel-boundary AU form; NEW
  fig:uk-read = the ECALL-tier inode-arm rule (dup-figure style);
  offset paragraph made honest (receipt-reported today; ownership is
  stated as the outlook, no campaign jargon); XXX + the nz offset note
  deleted; console/pipe arms and write's mirror in prose, pipe's gap
  stated as future work.  Original scope: rewrite the read figure to the RD-0
  sketch (general spec + owned-offset corollary), delete the `\nz`
  note and the "XXX" paragraph.  LAST — the tree leads, the TR
  records.

## Territory / coordination

- RD-4 is DONE and it did NOT need the merged claim as an input: the
  console arm's AU is the kernel's own console boundary
  (`WpUart.cons_read_pay`, i.e. ConsLog's `EvRead`), which the merged
  claim answers rather than owns.  `EchoOut.v` was not touched.
- RD-3's merge is the relay note upstream left in `UkRunSys.v`; taking
  it here closes their note — say so in the commit.
- `UkRunSys.v` / the engine files have been upstream's workspace all
  month; this campaign enters them ON THE OWNER'S WORD (this file's
  opening).  Coordinate via worklist notes as usual if upstream is
  mid-flight in the same file.

Related: `projects/noninterference.md` (PAUSED behind this — and NB:
RD-1's owned offset and RD-2's functional file row are exactly the
determinism upgrades its M0 wants; this cleanup is NOT a detour from
NI, it is NI's §4 "functional rows" arriving under another name),
`design/fs-syscall-specs.md` §4 (a piece may not ask a client to move
a kernel-owned ghost — RD-1 must respect it: the HELD half is the
process's own, so the fire moves BOTH halves holder-side),
`projects/app-echo.md` (the echo instances being re-derived).
