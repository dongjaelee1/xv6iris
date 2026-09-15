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

**AS LANDED (RD-1, 2026-09-15 — `iris/UserOff.v`, branch `rd1-off-own`).**
`uoff γo off := off_gv γo (1/2) (Z.of_nat off)` is in a new thin
`UserOff.v` above `OffGv.v`, not in `OffGv.v` itself — the design left
the choice open and the operational reason decided it: an edit to
`OffGv.v` changes its digest and invalidates the .vo of everything
below the fd layer, so the mirror cannot compile a single file again
without a full rebuild.  `uoff_park` is `={E}=∗`, not `==∗` (allocating
an invariant is a fancy update; there is no `==∗` form).  The rest
landed as written, with ONE name the design did not have: the fire's
premise is a SUPPLIER,

    off_supply γo E off d R :=
      off_gv γo (1/2) (Z.of_nat off) ={E}=∗ off_gv γo (1/2) (Z.of_nat (off+d)) ∗ R

— "take the kernel's half at `off`, give it back at `off+d`, leave `R`"
— which is what makes "one fire, two suppliers" literal: each of the
three fires (`arf_read_fire_gen`, `wrf_awrite_fire_gen`,
`wrf_apart_fire_gen`) takes one and returns `R`, and
`off_supply_parked` (R = `True`, opens `off_user_inv`) /
`off_supply_held` (R = `uoff γo (off+d)`, opens nothing) are the two
answers.  The old lemma names keep their EXACT former statements as the
parked instances, so no kernel proof changed.

**THE ONE THING THAT DID NOT LAND: the MINT at open.**  `off_pub_park`
and `off_pub_hand` are both proved and the publish
(`ProofSysOpenPub.v`) now goes through `off_pub_park` — the mode is
named at the call site — but mode `hand` cannot be wired yet, and the
obstacle is not in open: `FdSlots.foff_row` is a PURE FUNCTION OF THE
DESCRIPTOR STATE and PERSISTENT (`FdInode _ γo ↦ off_user_inv γo`,
every row, no per-row choice).  There is only one user half, so a
descriptor whose half was handed out HAS NO INVARIANT and its row
cannot claim one.  Wiring `hand` is therefore a change to the ROW
FAMILY — the per-row policy `FdSlots.v`'s own comment anticipates — and
the cheapest shape that keeps both properties is to put the mode IN THE
STATE (an `FdInode` that records parked-vs-held), which is also §3's
arm dispatch for free.  That is an `fdstate` change with a wide match
cone: **RD-2's call, not a side effect of RD-1.**

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

**RULED (RD-2, 2026-09-15, from RD-1's finding): the offset MODE lives
IN THE STATE.**  `FdInode` gains the parked-vs-held mode (an
`offmode`), because it is the only shape that keeps `FdSlots.foff_row`
both PERSISTENT and A PURE FUNCTION OF THE STATE once a half can be
handed out: a held descriptor's row claims nothing, a parked one's
claims `off_user_inv`, and which one applies is readable off the
descriptor itself — which is also this section's arm dispatch for
free.  Consequences RD-2 must carry through the `fdstate` match cone:
open's publish selects the mode (`off_pub_park`/`off_pub_hand` — both
already proved), fork's U-tier row demands mode = parked on every
inode descriptor (the pre-fork `uoff_park` re-mints the row the
child's copy consumes — `foff_row_inode` is the one step), close/dup
are mode-indifferent.

## 4. Fork (and dup) versus an owned offset — RULED 2026-09-15: PARK

THE OWNER RULED option (i): fork parks every held `uoff`.  The analysis
that led there is kept below; (ii) remains the recorded escape.

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

**AS LANDED (RD-1): the kernel owes NOTHING, checked not assumed.**
kfork's descriptor-bundle copy (`ProofKforkB3.v`'s scan) takes the
parent's row PERSISTENTLY (`#Hprow`) and hands the same row to the
child — "THE CHILD'S OFFSET ROW IS THE PARENT'S: one file, one shadow,
and the parent's entry is persistent".  So the child's table costs the
proof nothing exactly as long as the parent's row carries an
`off_user_inv`, which under mode `park` it always does; RD-1 changed no
fork proof and the ruling changes none.  Read the other way, this is
the same sentence as §2's as-landed note: under a future mode `hand` a
handed row has NO invariant, so the pre-fork park is not politeness —
it is what RE-MINTS the row the child's copy consumes.  The obligation
is therefore purely U-tier and purely the caller's: the enriched fork
row's premise asks the program to `uoff_park` every held offset before
the ecall and gives back `off_user_inv` = `FdSlots.foff_row` at that
state (`foff_row_inode` is the one step between them).  RD-1 landed the
door (`uoff_park`) and this finding; the premise itself is written when
RD-2 cuts the U-tier rows.  dup needs nothing at all: `γo` is per FILE
OBJECT, so one `uoff` already serves both descriptor numbers.

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
