(* UserOff.v -- THE OFFSET AS THE PROGRAM'S OWN RESOURCE: the third shape
   the USER half of [OffGv.off_gv] takes, and the ONE SUPPLIER through
   which every fire advances it.

   [OffGv.v] gives the shadow two user-side shapes: the half PARKED in the
   persistent existential invariant ([off_user_inv] -- "offsets are
   anybody's", what the generic user-mode safety WP holds), and the permit
   derived from it.  Neither lets a VERIFIED program know its own file
   position: that is the defect design/user-read.md section 2 names (and
   the tech report's [\nz] note).  This file adds the third shape:

     uoff γo off := off_gv γo (1/2) (Z.of_nat off)

   -- the user half HELD, at a value the program knows.  Everything about
   the shadow still goes through [off_gv], never a bare [ghost_var] at [Z]
   (the pinned-class rule, [OffGv.v]'s header).

   ONE-WAY DOOR.  [uoff_park] turns a held half back into the parked
   invariant, and there is no lemma the other way: [off_user_inv] is
   PERSISTENT, so nothing can ever take the half back out of it.  A
   program that stops caring about its position parks; a program that
   never cared was parked from birth (sys_open's publish, mode [park]).

   THE TWO MODES AT THE PUBLISH.  [off_pub_park] / [off_pub_hand] are the
   publish's split, named: the whole ghost becomes the kernel's half plus
   EITHER the parked invariant (what [ProofSysOpenPub] does today, and
   what the generic tier must keep doing) or the held [uoff γo 0] the
   enriched open row hands to its caller.  See the AS-LANDED note at the
   bottom of this file for what still stands between mode [hand] and the
   descriptor bundle.

   ONE FIRE, TWO SUPPLIERS.  fileread's and filewrite's offset advance
   ([FsAbsReadFire.arf_read_fire], [FsAbsWriteFire.wrf_awrite_fire] /
   [wrf_apart_fire]) needs BOTH halves at the instant: the kernel's, which
   it holds out of the file's off box, and the user's, which it does not
   own.  [off_supply γo E off d R] is exactly what those fires need of the
   user side and nothing more -- "take the kernel's half at [off], give it
   back at [off + d], and leave [R] behind" -- so the fire is ONE lemma
   and the two ways to pay it are two SUPPLIERS:

     parked ([off_supply_parked]): open the row's invariant, move both
       halves against its existential, leave [R = True].  This is the
       generic-safety path, verbatim what the fires did before.
     held   ([off_supply_held]):   the caller presented its own
       [uoff γo off]; both halves move together in one basic update -- no
       invariant is opened, no mask is needed -- and [R = uoff γo (off+d)]
       goes back to the caller.

   The held supplier is why design/fs-syscall-specs.md section 4 is
   respected: the half the fire moves user-side is the CLIENT'S OWN ghost,
   handed in by the client; the kernel half moves kernel-side in the same
   fire.  No piece asks a client to move a kernel-owned ghost, and the
   commit interfaces ([FsAbsReadFire.aread_commit_at],
   [FsAbsWriteFire.awrite_full_at] / [awrite_part_at]) keep their types --
   they still LEND the kernel half and take it back UNMOVED.

   Design of record: claude-notes/design/user-read.md sections 2 and 4
   (fork: RULED = park), claude-notes/design/fs-syscall-specs.md section 4. *)
From Stdlib Require Import ZArith Lia.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvPtsto.    (* [riscvGS] -- the [invGS] the invariant lives at *)
Require Import Xv6Cameras.    (* [offboxG] -- the shadow's pinned class          *)
Require Import OffGv.         (* [off_gv], [off_user_inv], [foffN]               *)

Section UserOff.
  Context `{!riscvGS Σ, !offboxG Σ}.

  (* ================================================================== *)
  (*  1.  THE HELD HALF                                                  *)
  (* ================================================================== *)

  (* THE PROGRAM'S OFFSET.  A [nat], because every consumer of a file
     position -- the read count bridge ([SysReadDefs.ard_count]), the
     write splice ([FsBlocks.blk_splice]), the fires' own [off + d] -- is
     stated at [nat]; the ghost's [Z] is an encoding detail of the C
     field, and [Z.of_nat] is the only place the two meet. *)
  Definition uoff (γo : gname) (off : nat) : iProp Σ :=
    off_gv γo (1/2) (Z.of_nat off).

  Global Instance uoff_timeless γo off : Timeless (uoff γo off).
  Proof using . rewrite /uoff. apply _. Qed.

  (* two holders of the half agree on the position (the kernel's half and
     a held one agree the same way -- [OffGv.off_gv_agree] directly). *)
  Lemma uoff_agree γo (off off' : nat) :
    uoff γo off -∗ uoff γo off' -∗ ⌜off = off'⌝.
  Proof using .
    rewrite /uoff. iIntros "H1 H2".
    iDestruct (off_gv_agree with "H1 H2") as %Heq. iPureIntro. lia.
  Qed.

  (* the kernel's half, read against a held one: this is what a proof that
     holds [uoff] knows about the value in the off box. *)
  Lemma uoff_agree_k γo (off : nat) (z : Z) :
    uoff γo off -∗ off_gv γo (1/2) z -∗ ⌜z = Z.of_nat off⌝.
  Proof using .
    rewrite /uoff. iIntros "H1 H2".
    iDestruct (off_gv_agree with "H1 H2") as %Heq. iPureIntro. lia.
  Qed.

  (* THE ONE-WAY DOOR (design/user-read.md section 2).  There is no
     converse: [off_user_inv] is persistent. *)
  Lemma uoff_park (E : coPset) γo (off : nat) :
    uoff γo off ={E}=∗ off_user_inv γo.
  Proof using .
    rewrite /uoff. iIntros "H". iApply (off_user_inv_alloc E γo _ with "H").
  Qed.

  (* THE ADVANCE, HOLDER-SIDE: the held half and the kernel's move
     TOGETHER, in a basic update -- no invariant, no mask side condition.
     This is the whole content of the held supplier below. *)
  Lemma uoff_advance γo (off d : nat) :
    uoff γo off -∗ off_gv γo (1/2) (Z.of_nat off) ==∗
      off_gv γo (1/2) (Z.of_nat (off + d)) ∗ uoff γo (off + d).
  Proof using .
    rewrite /uoff. iIntros "Hu Hk".
    iMod (off_gv_update_halves (Z.of_nat (off + d)) γo _ _ with "Hk Hu")
      as "[$ $]". done.
  Qed.

  (* ================================================================== *)
  (*  2.  THE SUPPLIER: what a fire needs of the user side               *)
  (* ================================================================== *)

  (* [off_supply γo E off d R]: "the kernel's half goes in at [off] and
     comes back at [off + d], and [R] is what the supplier leaves behind".
     A fire takes ONE of these and returns [R]; which supplier answered is
     invisible to it. *)
  Definition off_supply (γo : gname) (E : coPset) (off d : nat)
      (R : iProp Σ) : iProp Σ :=
    (off_gv γo (1/2) (Z.of_nat off) ={E}=∗
       off_gv γo (1/2) (Z.of_nat (off + d)) ∗ R)%I.

  (* SUPPLIER 1 -- PARKED: the generic-safety path, where the process
     knows nothing of its descriptors and the row's existential invariant
     ([FdSlots.foff_row] at an [FdInode]) is the whole user side.  The
     mask must contain [foffN]; every fire has that from
     [↑ftopN ∪ ↑appN ⊆ E], since [foffN] sits under [appN]. *)
  Lemma off_supply_parked (E : coPset) γo (off d : nat) :
    ↑foffN ⊆ E ->
    off_user_inv γo -∗ off_supply γo E off d True.
  Proof using .
    intros HE. rewrite /off_supply. iIntros "#Hinv Hk".
    iMod (off_user_inv_move E γo (Z.of_nat off) (Z.of_nat (off + d)) HE
            with "Hinv Hk") as "Hk".
    iModIntro. by iFrame.
  Qed.

  (* SUPPLIER 2 -- HELD: the caller presented its own half at the offset
     the transfer used and takes it back ADVANCED.  Note what is NOT here:
     no invariant is opened, so this supplier is good at EVERY mask. *)
  Lemma off_supply_held (E : coPset) γo (off d : nat) :
    uoff γo off -∗ off_supply γo E off d (uoff γo (off + d)).
  Proof using .
    rewrite /off_supply. iIntros "Hu Hk".
    iMod (uoff_advance γo off d with "Hu Hk") as "[$ $]". done.
  Qed.

  (* ================================================================== *)
  (*  3.  THE PUBLISH, IN TWO MODES                                      *)
  (* ================================================================== *)

  (* sys_open's publish owns the WHOLE shadow of the file it is opening
     (it allocated it), and splits it: one half into the file's off box
     ([FileOffCell.off_resident]), the other to the process.  These two
     lemmas are that second half's fate, named.

     MODE PARK -- what [ProofSysOpenPub] does, and what the generic tier
     must keep doing: the user half becomes the row invariant the
     descriptor bundle carries for every [FdInode] row. *)
  Lemma off_pub_park (E : coPset) γo (z : Z) :
    off_gv γo 1 z ={E}=∗ off_gv γo (1/2) z ∗ off_user_inv γo.
  Proof using .
    iIntros "H". iDestruct (off_gv_halves with "H") as "[Hk Hu]".
    iMod (off_user_inv_alloc E γo z with "Hu") as "#Hinv".
    iModIntro. by iFrame "Hk Hinv".
  Qed.

  (* MODE HAND -- the enriched open row: the half is HANDED to the caller
     at the position the publish stored, which at [sys_open] is 0 (the
     open path stores a zero [f->off]), hence [off_pub_hand_0].  Not a
     modality at all: handing IS the split; it is the mint that costs a
     step. *)
  Lemma off_pub_hand γo (off : nat) :
    off_gv γo 1 (Z.of_nat off) -∗
      off_gv γo (1/2) (Z.of_nat off) ∗ uoff γo off.
  Proof using .
    rewrite /uoff. iIntros "H".
    iDestruct (off_gv_halves with "H") as "[$ $]".
  Qed.

  Lemma off_pub_hand_0 γo :
    off_gv γo 1 0 -∗ off_gv γo (1/2) 0 ∗ uoff γo 0.
  Proof using . exact (off_pub_hand γo 0). Qed.

End UserOff.

(* ==================================================================== *)
(*  WHERE MODE HAND STANDS (RA-1)                                        *)
(* ==================================================================== *)
(* The ROW FAMILY now has the per-row policy [FdSlots.v]'s own comment
   anticipated, and it has it in the shape design/user-read.md section 3
   ruled: the mode is IN THE STATE.  [FdSlots.offmode] is the third field
   of [FdInode], and [FdSlots.foff_row] reads it --

     parked -> [OffGv.off_user_inv γo]   (what every inode row was)
     held   -> nothing

   -- which keeps the family both PERSISTENT and A PURE FUNCTION OF THE
   STATE, the two properties a forked child's copy, a dup, and every
   syscall that threads [fd_frags] opaquely all rest on.

   STILL NOTHING HANDS A [uoff] OUT, and that is now a pin rather than a
   wall.  [FileInvDefs.fdstate_ok]'s FD_INODE arm requires [OffParked], so
   every descriptor the file invariant describes is parked and the kernel
   meets no held state: fileread's and filewrite's fires read the same
   [foff_row] they always did.  Wiring mode HAND is exactly the act of
   relaxing that conjunct, and what it costs is design/user-read.md
   section 8.2's mode-split arms (the held arm's payment is the caller's
   own [uoff], riding [UkReadFile.udepwf_st]) plus section 8.3's boundary
   parks at fork and exec.

   WHAT DOES NOT BLOCK ON IT: everything above.  The park path is
   unchanged end to end, the held supplier is proved and plugged into all
   three fires, and a proof that obtains a [uoff] by any route (including
   a future [hand] publish) can fire reads and writes against it today. *)

(* ==================================================================== *)
(*  FORK AND DUP AGAINST A HELD OFFSET -- RULED 2026-09-15: PARK         *)
(* ==================================================================== *)
(* design/user-read.md section 4, the owner's ruling: at fork, every held
   [uoff] is PARKED; both parent and child drop to "offsets are anybody's".
   A shared [struct file] IS a shared [f->off], so two owners of one half
   would be unsound, and a program that wants post-fork offset knowledge
   opens the file again in the child (the Unix idiom).  dup needs nothing:
   [γo] is per FILE OBJECT, so the one [uoff] already serves both
   descriptor numbers.

   WHAT THE KERNEL OWES: NOTHING, and this was checked rather than
   assumed.  kfork's descriptor-bundle copy ([ProofKforkB3.v]'s scan)
   takes the parent's row PERSISTENTLY and hands the same row to the
   child --

     iDestruct (fd_frags_acc ... with "Hpfrag") as "(Hpfr & #Hprow & ...)"
     ...
     iDestruct ("Hcfrback" with "Hcfr Hprow") as "Hcfrag"
       (* "THE CHILD'S OFFSET ROW IS THE PARENT'S: one file, one shadow,
           and the parent's entry is persistent" *)

   -- so the child's table costs the proof nothing AS LONG AS the parent's
   row carries an [off_user_inv], which under mode [park] it always does.
   The kernel proof is therefore unchanged by RD-1, and it is unchanged by
   the ruling: it is the PARK ITSELF that keeps supplying the row family
   [ProofKforkB3] consumes.  (Read the implication in the other direction
   and it is the same sentence as the AS-LANDED note above: a HANDED row
   has no invariant, so under mode [hand] the pre-fork park is not a
   politeness -- it is what RE-MINTS the row the child's copy needs.)

   SO THE OBLIGATION IS THE CALLER'S, and it is a U-tier statement: the
   enriched fork row's premise asks the PROGRAM to park -- [uoff_park] on
   every descriptor whose offset it holds -- before the ecall, and what it
   gets back per descriptor is [OffGv.off_user_inv], i.e.
   [FdSlots.foff_row] at that descriptor's state ([FdSlots.foff_row_inode]
   is the one step from the one to the other).  That premise belongs to
   the U-tier fork row, which RD-2 cuts; RD-1 lands the door it goes
   through and this note. *)
