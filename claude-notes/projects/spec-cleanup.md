# spec-cleanup — generic syscall specs, read first

STATUS: OPENED 2026-09-15 (owner: "focus on cleanup... the read system
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
- [ ] **RD-4 CONSOLE ARM** (WAITS for upstream's post-Qed R1 — the
  merged IO claim is being built right now and is exactly the resource
  this arm should be stated at): re-cut `read_recv`'s console arm at
  the merged claim, application-neutral; re-derive
  `ush_read_recv_leaf` as an instance; echo's proof re-points, its
  statement unchanged.
- [ ] **RD-5 PIPE ARM**: the read end against the pipe's AU
  (`usys_pipe_ok` names the slots; the content row is new).
- [ ] **RD-6 WRITE**: the same program for write (its tailorings:
  `sh_deps`' write(16) deposit, the echo output ledger) — brief cut
  after RD-2 proves the pattern.
- [ ] **RD-TR**: rewrite `user.tex` §7's read figure to the RD-0
  sketch (general spec + owned-offset corollary), delete the `\nz`
  note and the "XXX" paragraph.  LAST — the tree leads, the TR
  records.

## Territory / coordination

- RD-4 sits inside the post-Qed redesign's blast radius — do not start
  until R1 lands; the merged claim is an INPUT to this lane.
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
