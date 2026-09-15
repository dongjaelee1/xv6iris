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

- [ ] **RD-0 DESIGN** (Fable; no build needed; NOW).  The ruling set,
  written into a `design/` page (new `design/user-read.md`, linking
  `design/user-fd.md`):
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
- [ ] **RD-1 OFF-OWN** (kernel; BLOCKED on box): implement (a) —
  `uoff`, sys_open's mint, fileread/filewrite's fire against a HELD
  half (both halves in hand: no invariant open), fork per the ruling;
  the generic-WP path keeps `off_user_inv` untouched.  This lane
  discharges the TR's `\nz` note.
- [ ] **RD-2 FILE-LEAF** (U tier; BLOCKED on box): the inode arm —
  `wp_uk_ecall_read` at kind `FdInode`: window walk + kept post at
  `aread`'s receipt; post = the target's File row.  First consumer to
  prove: `cat` reading a known file (a new small app, or a lemma-level
  instance) — the test that the spec is actually general.
- [ ] **RD-3 BASE/WIN MERGE**: retire the base leaf into the window
  form (the debt UkRunSys's own comment records).  Small; fold into
  RD-2's edit of the same file.
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
