# Design: the generic read spec (spec-cleanup RD-0)

Status: DESIGN OF RECORD for `projects/spec-cleanup.md` lanes RD-1..RD-5
(2026-09-15, Fable).  One owner ruling is open (§4, fork); everything
else here is decided unless a lane's as-landed note contradicts it.
Companion pages: `user-fd.md` (the descriptor ledger this dispatches
on), `fs-syscall-specs.md` (§4's ghost-ownership rule, the AU shape),
`user-wp-slot.md` (the trap contract the leaf rides).

## 1. The principle

A syscall's U-tier spec is general when three things are true at once:

1. its CONTENT post (what the bytes are) is available at EVERY arm, not
   just the one an application needed;
2. the per-arm payment is a resource the PROGRAM owns and understands
   (its offset half, its console claim, its pipe end) — never an
   application's private machinery;
3. the arm is selected by the caller's OWN knowledge of its descriptor
   (the `ufd` handle's kind), the way close/dup's rows already work.

Everything echo-specific then lives in echo: `ush_read_recv_leaf`
becomes an INSTANCE of the console arm at echo's claims, not a leaf of
its own.

## 2. The offset becomes the program's resource (`uoff`) — RD-1

`OffGv.v` today: the kernel owns one half of `off_gv γo`, and the USER
half is parked in `off_user_inv` — persistent, value existential,
"offsets are anybody's".  That parking is right for the generic-safety
WP and WRONG as the only option: it is why no verified program can know
its file position, and it is the TR's `\nz` note.

THE CHANGE.  The user half becomes holdable:

    uoff γo (off : nat) := off_gv γo (1/2) (Z.of_nat off)

- MINT: sys_open's publish currently mints `off_user_inv` from the
  returned half.  The enriched open row instead HANDS the half to the
  caller (`uoff γo 0` beside the `ufd` handle); the generic tier's open
  keeps parking.  Parking stays available later as a one-way door
  (`uoff_park : uoff γo off ==∗ off_user_inv γo`) for a program that
  stops caring — one-way because the invariant is persistent.
- SPEND: fileread/filewrite's fs AU currently LENDS the kernel half
  and takes it back UNMOVED, and the fire advances the offset against
  the parked invariant.  The general form: the caller's AU supplies the
  user half at its current value and receives it back ADVANCED
  (`uoff γo off` in, `uoff γo (off + d)` out, inside the commit's view
  shift).  This respects `fs-syscall-specs.md` §4 — the half the
  commit moves is the CLIENT'S OWN ghost, supplied by the client, and
  the kernel half moves kernel-side in the same fire; no piece asks a
  client to move a kernel-owned ghost.
- The parked path is the `Φ := True`-shaped instance of the same
  commit (open the invariant instead of presenting a half), so the
  kernel proof has ONE fire lemma with two suppliers, not two specs.

## 3. Arm dispatch by the handle — RD-2/4/5

The U-tier read leaf cases on the `fdstate` the caller's `ufd fd st`
handle carries (`FdOpen readable _ kind`); `readable = true` is a
premise, not an arm.  Per kind:

    Inode i γo :  payment  = uoff γo off  +  aread_commit Φ (caller's choice)
                  content  = d = min(cnt, |bs| − off), bytes = bs[off, off+d),
                             uoff γo (off+d), Φ av off a d
    Console    :  payment  = an AU on the merged IO claim (post-Qed R1's
                             resource — NOT echo's era ledger)
                  content  = the delivered bytes are the claim's next input
                             segment (the input-queue reading)
    Pipe       :  payment  = an AU on the pipe's byte queue at the read end
                  content  = delivered bytes = a prefix of the queue,
                             queue advanced
    Dev (other):  the base weak form (bytes exist, tail pinned) — honest,
                  since the device model gives nothing to name

The DEPOSIT generalizes the way `udepwf_std` already did for the
console: ledger-fixed AT THE ARM THE HANDLE NAMES.  One deposit family
`udepwf_at (kind)` replaces the per-arm ad-hoc forms; the supplier that
answers it is selected by the same kind the leaf cased on, so the
kernel-side wiring is one table, not four lemmas.

## 4. OWNER RULING NEEDED: fork (and dup) versus an owned offset

An owned `uoff γo off` cannot be duplicated, and xv6 shares the open
FILE OBJECT (hence `f->off`) across both fork and dup:

- dup within one process: unproblematic — γo is per file object, the
  one `uoff` serves both descriptor numbers.
- fork: parent and child both hold descriptors on the same object; two
  owners of one half is unsound.

Options:
(i) FORK PARKS: the fork row consumes every held `uoff` into
    `off_user_inv` (both sides drop to "anybody's").  Simple; matches
    the semantics — a shared offset IS racy; a program that wants
    post-fork offset knowledge should not share the object (open again
    in the child), which is also the Unix idiom.  The AU form remains
    for programs that genuinely race a shared descriptor.
(ii) FRACTIONAL over the sharing set, reads carry an AU on the
    fraction.  General, heavy, and buys nothing until some program
    actually coordinates a shared offset.
RECOMMENDATION: (i), with (ii) recorded as the escape if a program
ever needs it.  NOTE: fork need only park the offsets of descriptors
that are OPEN at the fork; close returns/drops the half (the off box
dies with the file object's last reference).

## 5. The Φ channel through the trap row

`wp_uk_ecall_read_recv` already built the mechanism: the window walk
with the kernel's `spost_at` KEPT, the receipt read out of the resume
image.  What generalizes: the receipt becomes a FAMILY indexed by the
arm (`read_receipt kind …`), of which `SpecFileread.console_receipt`
is the console member; the bridge rows the recv leaf hands out (resume
image bytes, wmapped destination, trapframe-argument ties, lazy bit)
are ARM-INDEPENDENT and move unchanged into the shared walk.  RD-2
adds the Inode member (`aread`'s receipt: `ard_pre`, `ard_count`,
slice + `Φ`), RD-4 re-cuts the console member at the merged claim,
RD-5 adds the pipe member.

## 6. The two presentation forms (and the TR §7 figure)

The GENERAL spec is the leaf of §3: AU payment, content post per arm.
The figure the TR shows is its derived OWNED-OFFSET COROLLARY — the
unshared-file common case, with no AU visible at all:

    { ubytes a1 k f * ufd fd (Open r w (Inode i γo)) * uoff γo off *
      afile i bs }                                   (k ≥ cnt, r = true)
        read(fd, a1, cnt)
    { ret d.  d = min(cnt, |bs| − off) *
      ubytes a1 k (bs[off, off+d) ⧺ f[d, k)) *
      ufd fd (Open r w (Inode i γo)) * uoff γo (off + d) *
      afile i bs }

(`afile i bs` = the caller's fragment of the abstract view, unmoved —
readable via a `Φ` that snapshots it; the corollary bakes that choice
in.)  Beside it the TR shows the general AU form once, and says the
corollary is what applications use.  This replaces the current
fig:sys-read + the `\nz` offset note + the "XXX" paragraph.

## 7. What does not change

- fileread/filewrite's PROOFS: the commit interface keeps its shape;
  only the fire's offset supplier gains the held-half case (§2).
- The generic-safety tier: parking remains its story end to end.
- The echo THEOREM's statement: RD-4 re-derives its leaves as
  instances; `echo_adequacy_echoΣ` and its assumption audit are
  untouched.
- `usys_mem_ok`'s read row (the trap-contract row): the leaf still
  discharges it; the content post is ADDITIONAL, riding the kept
  receipt, exactly as recv does today.
