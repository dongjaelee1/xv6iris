(* ===================================================================== *)
(*  UCatKernel.v -- cat's ROUND AT THE FILE CLAIM (lane CAT-WALK-2, K3). *)
(*                                                                       *)
(*  [UCatOut.v] is cat's console payment at the FILE stage and            *)
(*  [UkCatDeed.v] is its syscall pair at the deed; this file is the ONE   *)
(*  place they meet -- [UkCatCat.kcat_round], the persistent law that     *)
(*  funds a whole turn of cat's loop, built at the claim.                 *)
(*                                                                       *)
(*  WHAT IS HERE AND WHAT IS NOT.  The ENTRY                             *)
(*  ([UShEcho.echo_image_entry]'s shape at [FsCatPin] and argv            *)
(*  ["cat"; "f"]) is NOT here: it waits on lane OFF-HAND-6's HELD read    *)
(*  leaf, because the ordering of cat's output is exactly the premise     *)
(*  [UkCatDeed.kcat_r_of_deed_at] names and a PARKED row cannot discharge *)
(*  it ([FdInode i γo OffParked] records no offset at all).  What IS here *)
(*  is the round at that premise, taken as the section hypothesis [Hpin]  *)
(*  below -- so that when the held leaf lands, the entry is ONE           *)
(*  instantiation and not a second proof of the loop.                     *)
(*                                                                       *)
(*  THE ORDERING CLOSES ENTIRELY PAYER-SIDE, which is the point of        *)
(*  stating the loop's payment as a round law rather than as a chain.     *)
(*  [UkCatCat.kcat_round] says nothing about offsets: the payer holds its *)
(*  own cursor, and at a turn whose cursor is [p] it reads the deed at    *)
(*  [off0 := p], gets the count back as [ard_count 512 p (length bs)],    *)
(*  funds that turn's write at [UCatOut.cch … p], and comes out at        *)
(*  [p + count].  [cat_round_line] is the pure half of that -- the bytes  *)
(*  the read delivered ARE the continuation's bytes at the cursor -- and  *)
(*  it is what [UCatOut.cch_chain] consumes.                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunSys.
Require Import VcGen.              (* [trunc32_subrange] -- a2 read as a C [int] *)
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import UCodeCat.
Require User.CatSyms User.CatInstrs.
Require Import FdSlots ProcGeom UserFd UserCwd.
Require Import UexecSG UexecSlot UexecRet.
Require Import UkCat.
Require Import UkCatCat.
Require Import UkFileOpen.
Require Import UkCatDeed.
Require Import AppCfg AppInv AppFile FileOpen FsCfg FsImgCheck.
Require Import ConsoleInv.
Require Import SysReadDefs.     (* [ard_count] *)
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import LineWords EchoDisc.
Require Import FileState FileDisc FileOut.
Require Import EchoOut AppEcho.
Require Import UCatOut.
Require Import UkCatMain.    (* [cm_lit] / [cm_msg_q] / [kcat_dg_open] *)
Require Import SpecKexec.    (* [kexec_image_ok] and its readings *)
Require Import ArgPath.      (* [arg_path_of] / [arg_path_shape] *)
Require Import PathElems.    (* [path_elems] / [SLASH] *)
Require Import FsAbsEra.     (* [um_start_of] *)
Require Import UkAbi.        (* [uk_args_c] / [uka_argc] *)
Require Import ExecEntry.    (* [image_entry] / [image_entry_of_at] *)
Require Import UEchoKernel.  (* [uvis_sp] / [uvis_av] / [uvis_argc] and the
                                argument reading off the key -- none of it
                                names a program *)
Require Import UShCat.       (* cat's exec/argv geometry and its entry carve *)
Require Import ExecWords.        (* [exec_ok]: [line_ok] without the command *)
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE HALF: THE BYTES THE READ DELIVERED ARE THE ROUND'S      *)
(*                                                                       *)
(*  [UCatOut.cch_chain] asks for one row per byte -- the continuation of  *)
(*  cat's round holds [fb j] at [p + j] -- and the deed-aware read hands  *)
(*  back exactly the two facts that give it: the count IS                 *)
(*  [ard_count 512 p (length bs)], and byte [j] IS [bs !!! (p + j)].      *)
(*  The continuation at [RCRan] is [bs ++ u_prompt]                       *)
(*  ([UCatOut.cat_out_of_tie]), so the prompt is never reached: the count *)
(*  stops at [length bs].                                                *)
(* ===================================================================== *)
Lemma cat_round_line (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (s : dst) (i : Z) (bs : list (bv 8))
    (p nb : nat) (gb : nat -> bv 8) :
  cat_tie cs0 s0 I0 s -> s = Some (i, bs) ->
  (p <= length bs)%nat ->
  nb = ard_count 512 p (length bs) ->
  (forall j : nat, (j < nb)%nat -> gb j = bs !!! (p + j)%nat) ->
  forall j : nat, (j < nb)%nat ->
    cont (cat_st cs0 s0 I0) LCat (ralt_dec (ralt_enc RCRan)) !! (p + j)%nat
    = Some (gb j).
Proof using .
  intros Htie Hs Hple Hnb Hgb j Hj.
  rewrite ralt_dec_enc.
  rewrite (cat_out_of_tie cs0 s0 I0 s i bs Htie Hs).
  assert (Hlt : (p + j < length bs)%nat).
  { subst nb. unfold ard_count in Hj. lia. }
  rewrite (lookup_app_l bs u_prompt (p + j)%nat Hlt).
  rewrite (Hgb j Hj).
  exact (list_lookup_lookup_total_lt bs (p + j)%nat Hlt).
Qed.

(* ...and the cursor's own arithmetic: a turn that read [nb] bytes at [p]
   lands at [p + nb], still inside the content. *)
Lemma cat_round_cursor (bs : list (bv 8)) (p nb : nat) :
  (p <= length bs)%nat ->
  nb = ard_count 512 p (length bs) ->
  (p + nb <= length bs)%nat.
Proof using . intros Hple ->. unfold ard_count. lia. Qed.

(* ...AND THE READING THAT REFUTES THE `cat: read error` TAIL (lane
   CAT-GEOM-2).  A word whose UNSIGNED value is at most 512 -- which is
   what lane OFF-LINK's count bound says of every count cat's read can
   report -- has the same SIGNED value, so [bv_signed ret < 0] is a
   contradiction.  [ProofVirtioDiskInit.vdi_bv_signed_small] is the same
   reading at [2 ^ 32]; it is restated here rather than imported, because
   that file's cone is the disk driver's. *)
Lemma cat_signed_small (x : mword 64) :
  (bv_unsigned x <= 512)%Z -> bv_signed x = bv_unsigned x.
Proof using .
  intro H. pose proof (bv_unsigned_in_range _ x) as [Hl _].
  unfold bv_signed. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 9223372036854775808%Z)
    by (vm_compute; reflexivity).
  rewrite Hhm. split; [ lia | ].
  apply (Z.le_lt_trans _ 512); [ exact H | reflexivity ].
Qed.

Section UCatKernel.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  (* NO [uexecSG] AND NO [uprogSG] SECTION VARIABLE (lane CAT-WALK-2, K2):
     [UkFileOpen.v] and [UkCatDeed.v] state their [UkRun.urun] at the
     AMBIENT pair resolution finds, and a variable of either class here
     would be a SECOND instance whose [urun] prints identically and does
     not unify. *)
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).

  (* the argument registers, at [UkCat.v]'s own spelling (a7 is
     [UmodeCap]'s and the rest [UmodeAbi]'s; both are these literals) *)
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  2.  THE ROUND'S INVARIANT: THE LEDGER, AND -- AT ONE AND THE SAME  *)
  (*      POSITION -- THE DEED'S HANDLE AND THE CONSOLE CURSOR.          *)
  (*                                                                     *)
  (*  THE POSITION IS EXISTENTIAL because [UkCatCat.kcat_round] is ONE    *)
  (*  PERSISTENT LAW for every turn and the cursor advances; and the      *)
  (*  handle and the cursor are at the SAME [p] because that tie is the   *)
  (*  whole content of "cat's output is the file's content IN ORDER".     *)
  (*  [Hold] is abstract for one reason: the handle that carries an       *)
  (*  offset is [FdInode i γo (OffHeld p)] and lane OFF-HAND-6 has not    *)
  (*  landed it, so this file names the SHAPE and not the resource.      *)
  (* =================================================================== *)
  Definition cat_round_inv (Hold : nat -> iProp Σ) (l : list fdstate)
      (bs : list (bv 8)) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat) : iProp Σ :=
    (UserFd.ustd γfd l
     ∗ ∃ p : nat, ⌜(p <= length bs)%nat⌝ ∗ Hold p
                  ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P p)%I.

  (* =================================================================== *)
  (*  2b. THE SHAPE GUARD: [Hpin]'s BODY IS [kcat_r_of_deed_at]'s.        *)
  (*                                                                     *)
  (*  One cursor at a time, and that is the whole point.  Given the row   *)
  (*  the held leaf owes AT [off0] -- every reported offset IS [off0] --  *)
  (*  lane CAT-WALK's [UkCatDeed.kcat_r_of_deed_at] already yields        *)
  (*  exactly the proposition [cat_round_at] takes boxed over the cursor. *)
  (*  So the round is not vacuously true: its read premise is inhabited   *)
  (*  at every position for which the row holds, and what a PARKED        *)
  (*  descriptor cannot do is hold the row at more than one of them --    *)
  (*  which is precisely why [Hold] is a FUNCTION of the position.        *)
  (* =================================================================== *)
  Lemma cat_pinned_read_at (c : file_fixed) (r : file_names) (q : Qp)
      (jc : Z) (i : Z) (bs : list (bv 8)) (fd : nat) (wb : bool)
      (γo : gname) (off0 : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (fd < NOFILE)%nat ->
    (off0 <= length bs)%nat ->
    □ (∀ (rv : mword 64) (gb : nat -> bv 8) (off : nat),
         ⌜Z.to_nat (bv_unsigned rv) = ard_count 512 off (length bs)⌝ -∗
         ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
            gb j = bs !!! (off + j)%nat⌝ -∗
         ⌜off = off0⌝) -∗
    cat_code γt -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    UkCat.kcat_r N (mword_of_int (Z.of_nat fd)) CatSyms.buf 512%nat
      (UkCatDeed.kcat_deed_hold N fd wb i γo r q bs)
      (fun (rv : mword 64) (gb : nat -> bv 8) =>
         (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat⌝
          ∗ ((⌜Z.to_nat (bv_unsigned rv) = ard_count 512 off0 (length bs)⌝
              ∗ ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                   gb j = bs !!! (off0 + j)%nat⌝
              ∗ UkCatDeed.kcat_deed_hold N fd wb i γo r q bs)
             ∨ ((∃ p' : nat, ⌜(p' <= length bs)%nat⌝
                             ∗ UkCatDeed.kcat_deed_hold N fd wb i γo r q bs)
                ∗ file_taint c)))%I).
  Proof using .
    intros Heq Hfdlt Hoff.
    iIntros "#Hrow #Hcode #Hm #Hinv".
    iApply (UkCat.kcat_r_mono_out N (mword_of_int (Z.of_nat fd))
              CatSyms.buf 512%nat _ _ _ with "[] []"); last first.
    { iApply (UkCatDeed.kcat_r_of_deed_at N CatSyms.buf 512%nat fd wb i γo
                c r q jc bs off0 Heq
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                Hfdlt
                with "Hrow Hcode Hm Hinv"). }
    iIntros (rv gb) "[%Hbnd [Hhold [[%Hc1 %Hc2] | #HT]]]".
    - iSplitR; [ by iPureIntro | ].
      iLeft. iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hhold".
    - iSplitR; [ by iPureIntro | ].
      iRight. iFrame "HT". iExists off0.
      iSplitR; [ by iPureIntro | ]. iExact "Hhold".
  Qed.

  (* =================================================================== *)
  (*  3.  THE ROUND, AT THE OFFSET-PINNED READ OBLIGATION                *)
  (*                                                                     *)
  (*  [Hpin] IS WHAT THE HELD LEAF STILL OWES, AND THE ONLY THING THIS   *)
  (*  FILE TAKES ON CREDIT.  At a PARKED row the read leaf reports the    *)
  (*  bytes at SOME offset ([UkFileOpen.wp_uk_read_deed_learns_mapped]'s  *)
  (*  [∃ off]) because [FdInode i γo OffParked] records no offset at all: *)
  (*  the kernel holds the file's own [f->off] and the descriptor state   *)
  (*  says nothing about it.  [UkCatDeed.kcat_r_of_deed_at] turns the     *)
  (*  existential into the pinned obligation given one row -- every       *)
  (*  reported offset IS [off0] -- and at the HELD row                    *)
  (*  [FdInode i γo (OffHeld off0)] that row is the descriptor state's    *)
  (*  own, discharged by the held leaf from that row and nothing else.    *)
  (*                                                                     *)
  (*  NOTE THE SHAPE, because the obvious one is VACUOUS.  The ROW may    *)
  (*  NOT be boxed over [off0]: at two different [off0] the box is        *)
  (*  inconsistent and the round it builds says nothing.  Nor may the     *)
  (*  OBLIGATION be boxed over the cursor at a FIXED handle: one          *)
  (*  descriptor has one offset, so "at any [p] I can read at [p]" is     *)
  (*  unsuppliable.  What is boxed is the obligation AT [Hold p] -- the   *)
  (*  handle that is itself at [p] -- and the read hands [Hold] back at   *)
  (*  [p] plus the count.  That is exactly the held descriptor's law,     *)
  (*  and the payer's own tie [the deed's offset IS the console cursor]   *)
  (*  is what the invariant above states.                                *)
  (*                                                                     *)
  (*  [Hw] IS THE TURN'S WRITE, at the cursor and back at the cursor      *)
  (*  plus the count -- the shape [UCatOut.cch_chain] yields through      *)
  (*  [UkCat.wp_kcat_write_chain].                                        *)
  (* =================================================================== *)
  (* =================================================================== *)
  (*  [Hheld]: THE HELD READ'S OBLIGATION, NAMED (lane CAT-ENTRY-2, T3).  *)
  (*                                                                     *)
  (*  This is the ONE thing cat's entry takes on credit, and it is        *)
  (*  written here once so that the entry is ONE INSTANTIATION when lane  *)
  (*  OFF-HAND-6's [wp_uk_ecall_read_file_held] lands.  Read it as: at a  *)
  (*  cursor [p] inside the content, the descriptor HELD AT [p] reads the *)
  (*  deed at [p] -- the count is [ard_count 512 p (length bs)], byte [j] *)
  (*  is [bs !!! (p + j)] -- and comes back HELD AT [p + count]; or the   *)
  (*  era is tainted and the handle comes back at some position.          *)
  (*                                                                     *)
  (*  [Hold] IS ABSTRACT, and deliberately so: OFF-HAND-6's design        *)
  (*  records the offset VALUE in the descriptor state ([OffHeld off])    *)
  (*  and lets the half ride the kernel's bundle, so [Hold p] may end up  *)
  (*  being just [UserFd.ufd γfd fd (FdOpen true wb (FdInode i γo         *)
  (*  (OffHeld p)))] with the deed fraction and no user-side [uoff] at    *)
  (*  all.  Either shape instantiates this.                              *)
  (*                                                                     *)
  (*  NOTE THE SHAPE, because the two obvious ones are VACUOUS            *)
  (*  (CAT-WALK-2).  The ROW may NOT be boxed over the expected offset:   *)
  (*  at two different ones the box is inconsistent.  Nor may the         *)
  (*  OBLIGATION be boxed over the cursor at a FIXED handle: one          *)
  (*  descriptor has one offset.  What is boxed is the obligation AT      *)
  (*  [Hold p] -- the handle that is ITSELF at [p].                       *)
  (* =================================================================== *)
  Definition cat_held_read (Hold : nat -> iProp Σ) (c : file_fixed)
      (fd : nat) (bs : list (bv 8)) : iProp Σ :=
    (□ (∀ p : nat, ⌜(p <= length bs)%nat⌝ -∗
          UkCat.kcat_r N (mword_of_int (Z.of_nat fd)) CatSyms.buf 512%nat
            (Hold p)
            (fun (rv : mword 64) (gb : nat -> bv 8) =>
               (* THE COUNT'S BOUND, ON BOTH ARMS (lane OFF-LINK, relayed
                  through [UkCatDeed.kcat_r_of_deed]).  It is what
                  CAT-ENTRY-2 named as the missing kernel row: without it
                  the TAINT arm says nothing about [rv], and [Hw] below
                  is unsuppliable there. *)
               (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat⌝
                ∗ ((⌜Z.to_nat (bv_unsigned rv) = ard_count 512 p (length bs)⌝
                    ∗ ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                         gb j = bs !!! (p + j)%nat⌝
                    ∗ Hold (p + Z.to_nat (bv_unsigned rv))%nat)
                   ∨ ((∃ p' : nat, ⌜(p' <= length bs)%nat⌝ ∗ Hold p')
                      ∗ file_taint c)))%I)))%I.

  (* A FRAME RIDES THE READ.  The read's law is boxed over the cursor, so a
     linear [F] the caller must carry across the whole loop (what sh's
     child owes its parent beside the fraction -- PROGRAM-STREAM stretch
     11, defect 2) cannot be handed in beside it; it goes IN the hold the
     law is stated at and comes back in it, on both arms. *)
  Lemma kcat_r_frame_in (fdv : mword 64) (a : Z) (cnt : nat)
      (Ri F : iProp Σ) (Ro : mword 64 -> (nat -> bv 8) -> iProp Σ) :
    UkCat.kcat_r N fdv a cnt Ri Ro -∗
    UkCat.kcat_r N fdv a cnt (Ri ∗ F)
      (fun (ret : mword 64) (gb : nat -> bv 8) => Ro ret gb ∗ F)%I.
  Proof using .
    iIntros "Hr" (h m avail f)
      "%Ha0 %Ha1 %Ha2 #Hcode [HRi HF] Hbs Hrun Hcont".
    iApply ("Hr" $! h m avail f with "[%] [%] [%] Hcode HRi Hbs Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret gb) "HRo Hbs Hrun".
    iApply ("Hcont" $! h' ret gb with "[HRo HF] Hbs Hrun"). iFrame "HRo HF".
  Qed.

  Lemma cat_held_read_frame (Hold : nat -> iProp Σ) (c : file_fixed)
      (fd : nat) (bs : list (bv 8)) (F : iProp Σ) :
    cat_held_read Hold c fd bs -∗
    cat_held_read (fun p : nat => (Hold p ∗ F)%I) c fd bs.
  Proof using .
    iIntros "#H". rewrite /cat_held_read. iIntros "!>" (p) "%Hp".
    iApply (UkCat.kcat_r_mono_out with "[] [-]"); last first.
    { iApply kcat_r_frame_in. iApply ("H" $! p with "[%]"). exact Hp. }
    iIntros (rv gb) "[[%Hb Harm] HF]". iSplitR; [ by iPureIntro | ].
    iDestruct "Harm" as "[(%Hc & %Hby & Hh) | [Hh #HT]]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iFrame "Hh HF".
    - iRight. iFrame "HT". iDestruct "Hh" as (p') "[%Hp' Hh]".
      iExists p'. iSplitR; [ by iPureIntro | ]. iFrame "Hh HF".
  Qed.

  Lemma cat_round_at (c : file_fixed) (i : Z) (bs : list (bv 8)) (fd : nat)
      (Hold : nat -> iProp Σ) (l : list fdstate)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (Cend : iProp Σ) :
    c = fgn_cl g ->
    cat_tie cs0 s0 I0 (Some (i, bs)) ->
    (* [Hheld]: the offset-pinned read, at a handle that is itself at [p] *)
    cat_held_read Hold c fd bs -∗
    (* [Hw]: the turn's write, at the cursor -- COUNT-EXACT (RULING (g)).
       Its output is read at the value [write] RETURNED, and it says that
       value IS the count: [UkWriteLeaf.uwrite_no_short] gives exactly
       that at a console destination the caller owns, and it is what
       refutes cat's `write error` tail inside the walk.  So the round
       this file builds never funds [UkCatCat.kcat_dg_cw] and does not
       take it as a premise. *)
    □ (∀ (p nb : nat) (rv : mword 64) (fbb : nat -> bv 8),
         (* THE COUNT IS READ OFF THE RETURNED WORD, not off the walk's
            [nb].  [UkCatCat.kcat_round]'s write arm is quantified over
            EVERY [nb] with [rv = mword_of_int (Z.of_nat nb)], and above
            2^64 that equation no longer identifies [nb] -- so the cursor
            advances by what the WORD says, which is what the kernel's
            own [sys_rw_count] reads too. *)
         ⌜rv = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
         (* the turn's bytes ARE the round's, or the era is TAINTED and
            the free write law is the taint's own ([AppInv.app_sup] /
            [AppFile.file_taint_of_sup]) *)
         (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
           /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                cont (cat_st cs0 s0 I0) LCat (ralt_dec (ralt_enc RCRan))
                  !! (p + j)%nat = Some (fbb j)⌝
          ∨ (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat⌝ ∗ file_taint c)) -∗
         UserFd.ustd γfd l -∗
         UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P p -∗
         UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
           (ubytes γd CatSyms.buf 512 fbb)
           (fun wret : mword 64 =>
              (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
               ∗ UserFd.ustd γfd l
               ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P
                   (p + Z.to_nat (bv_unsigned rv))%nat
               ∗ ubytes γd CatSyms.buf 512 fbb))) -∗
    (* the read-error tail, and the loop's normal exit.  [Cend]'s wand
       takes the cursor and the handle's position SEPARATELY: the loop
       exits on [read] returning zero, and it is the ENTRY -- which owns
       the arithmetic of [ard_count] -- that reads off that the two are
       then the same. *)
    (* NO [kcat_dg_cr] PREMISE (lane CAT-GEOM-2).  The `cat: read error`
       tail used to be a resource this round carried and never spent, and
       at a claim-bearing era it is UNSATISFIABLE -- sixteen bytes the
       model's continuation does not hold at any cursor, which no console
       credential can file.  A premise like that makes the round
       VACUOUSLY true.  With lane OFF-LINK's count bound the arm is
       REFUTED instead, on both arms of the read: the count is at most
       512, so the returned word's SIGNED reading is its unsigned one and
       [bv_signed ret < 0] is a contradiction. *)
    (* ...AND THE LOOP'S EXIT, AT CAT'S OWN END CURSOR (lane CAT-GEOM-3).
       This wand used to take the console cursor [p] and the handle's
       position [p'] as two unrelated numbers below [length bs], and a
       payload owed at [length bs] -- which is what [UCatOut.catq_filed]
       is, restated at [UCatOut.cat_out_len] -- was then not
       instantiable.  It IS pinned, and by the loop's own exit
       condition: cat stops when [read] returns ZERO, the count is
       [SysReadDefs.ard_count 512 p (length bs)], and [ard_count] is zero
       exactly at [p = length bs].  The disjunct is the TAINT, where the
       model says nothing and the cursor's own right arm funds the
       payload anyway. *)
    □ (∀ p p' : nat, ⌜(p <= length bs)%nat⌝ -∗ ⌜(p' <= length bs)%nat⌝ -∗
         (⌜p = length bs /\ p' = length bs⌝ ∨ file_taint c) -∗
         UserFd.ustd γfd l -∗ Hold p' -∗
         UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P p -∗ Cend) -∗
    cat_code γt -∗
    UkCatCat.kcat_round N (mword_of_int (Z.of_nat fd))
      (cat_round_inv Hold l bs v vf ps0 cs0 s0 I0 P) Cend.
  Proof using .
    intros Hgc Htie.
    iIntros "#Hpin #Hw #Hend #Hcode".
    rewrite /cat_held_read /UkCatCat.kcat_round. iModIntro.
    iIntros (h m avail f) "%Ha0 %Ha1 %Ha2 _ HI Hbuf Hrun Hcont".
    iDestruct "HI" as "[Hstd Hcur]".
    iDestruct "Hcur" as (p) "(%Hple & Hhold & Hc)".
    (* THE READ, at the cursor's OWN offset *)
    iDestruct ("Hpin" $! p with "[%]") as "Hr"; [ exact Hple | ].
    iApply ("Hr" $! h m avail f with "[%] [%] [%] Hcode Hhold Hbuf Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret gb) "Hro Hbuf Hrun".
    iApply ("Hcont" $! h' ret gb with "[Hstd Hc Hro] Hbuf Hrun").
    iDestruct "Hro" as "[%Hbnd Hro]".
    iDestruct "Hro" as "[(%Hcnt & %Hbyt & Hhold) | [Hhold #HT]]"; last first.
    { (* THE TAINT: the cursor's own right disjunct funds every arm *)
      iDestruct "Hhold" as (p2) "[%Hp2 Hhold]".
      iSplit; [| iSplit ].
      - iIntros "%Hneg". exfalso.
        pose proof (bv_unsigned_in_range 64 ret) as [Hr0 _].
        assert (Hu : (bv_unsigned ret <= 512)%Z).
        { rewrite <- (Z2Nat.id (bv_unsigned ret) Hr0). lia. }
        rewrite (cat_signed_small ret Hu) in Hneg.
        exact (Z.lt_irrefl 0 (Z.le_lt_trans 0 (bv_unsigned ret) 0 Hr0 Hneg)).
      - iIntros "_".
        iApply ("Hend" $! p p2 with "[%] [%] [] Hstd Hhold Hc");
          [ exact Hple | exact Hp2 | ].
        iRight. iExact "HT".
      - iIntros (nb) "%Hret _".
        iApply (UkCat.kcat_wr_mono N (mword_of_int 1)
                  (mword_of_int CatSyms.buf) nb
                  (ubytes γd CatSyms.buf 512 gb)%I
                  (fun wret : mword 64 =>
                     (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
                      ∗ UserFd.ustd γfd l
                      ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P
                          (p + Z.to_nat (bv_unsigned ret))%nat
                      ∗ ubytes γd CatSyms.buf 512 gb)%I)
                  _ with "[Hhold] [Hstd Hc]").
        { iIntros (wret) "(%Hws & Hstd & _ & Hb)".
          iSplitR "Hb"; [ | iExact "Hb" ].
          iLeft. iSplitR; [ by iPureIntro | ].
          rewrite /cat_round_inv. iFrame "Hstd".
          iExists p2. iSplitR; [ by iPureIntro | ]. iFrame "Hhold".
          rewrite /UCatOut.cch. iRight. rewrite <- Hgc. iExact "HT". }
        iApply ("Hw" $! p nb ret gb with "[%] [] Hstd Hc");
          [ exact Hret | ].
        iRight. iSplitR; [ by iPureIntro | ]. iExact "HT". }
    (* THE CONTENT ARM *)
    assert (Hnble : (Z.to_nat (bv_unsigned ret) <= 512)%nat)
      by (rewrite Hcnt; apply ard_count_le).
    assert (Hnext : (p + Z.to_nat (bv_unsigned ret) <= length bs)%nat)
      by exact (cat_round_cursor bs p (Z.to_nat (bv_unsigned ret))
                  Hple Hcnt).
    iSplit; [| iSplit ].
    - (* [cat: read error] is VACUOUS at a deed: the count that came back
         is an [ard_count], which is not negative (lane READ-RELAY) *)
      iIntros "%Hneg". exfalso.
      pose proof (bv_unsigned_in_range 64 ret) as [Hr0 _].
      assert (Hu : (bv_unsigned ret <= 512)%Z).
      { rewrite <- (Z2Nat.id (bv_unsigned ret) Hr0). lia. }
      rewrite (cat_signed_small ret Hu) in Hneg.
      exact (Z.lt_irrefl 0 (Z.le_lt_trans 0 (bv_unsigned ret) 0 Hr0 Hneg)).
    - iIntros "%Hzero".
      (* the loop exits on a ZERO count, and [ard_count] is zero exactly
         at the end of the content *)
      pose proof (bv_unsigned_in_range 64 ret) as [Hr0 _].
      assert (Hu : (bv_unsigned ret <= 512)%Z).
      { rewrite <- (Z2Nat.id (bv_unsigned ret) Hr0). lia. }
      assert (Hu0 : bv_unsigned ret = 0%Z).
      { rewrite <- (cat_signed_small ret Hu). exact Hzero. }
      assert (Hz : ard_count 512 p (length bs) = 0%nat).
      { rewrite <- Hcnt. rewrite Hu0. reflexivity. }
      assert (Hpe : p = length bs) by (unfold ard_count in Hz; lia).
      iApply ("Hend" $! p (p + Z.to_nat (bv_unsigned ret))%nat
                with "[%] [%] [] Hstd Hhold Hc");
        [ exact Hple | exact Hnext | ].
      iLeft. iPureIntro. rewrite Hu0. cbn [Z.to_nat].
      rewrite Nat.add_0_r. exact (conj Hpe Hpe).
    - iIntros (nb) "%Hret %Hnb0".
      iApply (UkCat.kcat_wr_mono N (mword_of_int 1)
                (mword_of_int CatSyms.buf) nb
                (ubytes γd CatSyms.buf 512 gb)%I
                (fun wret : mword 64 =>
                   (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
                    ∗ UserFd.ustd γfd l
                    ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P
                        (p + Z.to_nat (bv_unsigned ret))%nat
                    ∗ ubytes γd CatSyms.buf 512 gb)%I)
                _ with "[Hhold] [Hstd Hc]").
      { iIntros (wret) "(%Hws & Hstd & Hc' & Hb)".
        iSplitR "Hb"; [ | iExact "Hb" ].
        iLeft. iSplitR; [ by iPureIntro | ].
        rewrite /cat_round_inv. iFrame "Hstd".
        iExists (p + Z.to_nat (bv_unsigned ret))%nat.
        iSplitR; [ by iPureIntro | ]. iFrame "Hhold". iExact "Hc'". }
      iApply ("Hw" $! p nb ret gb with "[%] [] Hstd Hc");
        [ exact Hret | ].
      iLeft. iPureIntro. split; [ exact Hnble | ].
      exact (cat_round_line cs0 s0 I0 (Some (i, bs)) i bs p
               (Z.to_nat (bv_unsigned ret)) gb
               Htie eq_refl Hple Hcnt Hbyt).
  Qed.

  (* =================================================================== *)
  (*  4.  [Hw]: THE TURN'S WRITE AT THE CURSOR (lane CAT-ENTRY-2,        *)
  (*      RULING (h)) -- cat's twin of [UEchoOut.kecho_w_of_link_data].   *)
  (*                                                                     *)
  (*  ONE call of [write(1, buf, n)] paid out of the era's own console    *)
  (*  credential at cat's cursor, with THREE differences from echo's.     *)
  (*                                                                     *)
  (*  (1) THE SOURCE RUN IS OWNED, NOT PERSISTENT.  echo writes its argv  *)
  (*  strings ([ustr … DfracDiscarded]), so one copy serves both the      *)
  (*  chain's deposit and the leaf underneath.  cat writes its 512-byte   *)
  (*  READ BUFFER at [DfracOwn 1], and the copy put into the deposit's    *)
  (*  wand is consumed there.  So the run is HALVED                       *)
  (*  ([UkWriteLeaf.ubytes_halve]): one half goes to the leaf and comes   *)
  (*  back in its continuation, the other goes into the wand and comes    *)
  (*  back through the chain's own payload                                *)
  (*  ([UkWriteLeaf.uwrite_chain_sup_ret]), and the two rejoin.  The      *)
  (*  buffer is whole again for the next turn of the loop, which is what  *)
  (*  the round's invariant needs.                                       *)
  (*                                                                     *)
  (*  (2) THE COUNT IS THE READ'S RETURN and not a string length, so the  *)
  (*  bytes written are a PREFIX of the buffer; the tail is split off     *)
  (*  with [UserHeap.ubytes_app] and framed across the call.              *)
  (*                                                                     *)
  (*  (3) THE NO-SHORT FACT IS KEPT.  echo's twin reads                   *)
  (*  [UkWriteLeaf.uwrite_no_short] and DROPS its equation; cat's loop    *)
  (*  branches on exactly that word ([beq a0,s1]), so it is the output --  *)
  (*  and it is what refutes the `cat: write error` tail (RULING (g)).    *)
  (*  It holds whether or not the era is tainted, because it is a fact    *)
  (*  about the LEAF -- a console write of a run the caller owns returns  *)
  (*  the full count -- and not about the claim.                          *)
  (* =================================================================== *)

  (* the syscall's count register, read as the C [int] it is.  The same
     reading as [UEchoOut.echo_count_is] and [UShOut]'s, at the WORD
     rather than at a [nat]: the payer may not compute the count from the
     walk's [nb] (above 2^64 the equation [ret = mword_of_int nb] does not
     identify it), so everything below reads it off [bv_unsigned].  Its
     home is [SpecSysRead.v], whose cone is the whole read/write tower. *)
  Lemma cat_count_is (nb : nat) :
    (Z.of_nat nb < 2 ^ 31)%Z ->
    sys_rw_count (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb.
  Proof using .
    intros Hlt. change (2 ^ 31)%Z with 2147483648%Z in Hlt.
    assert (Hu : uint (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb)
      by (apply uint_moi; unfold Z64; lia).
    rewrite uint_unsigned in Hu.
    rewrite /sys_rw_count. unfold bv_signed.
    rewrite trunc32_subrange subrange_31_0_unsigned Hu.
    rewrite (Z.mod_small (Z.of_nat nb) 4294967296); [| lia].
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
  Qed.

  (* ...and a word IS the machine integer of its own unsigned value, which
     is how the count the payer reads off the word gets back into the
     [mword_of_int] shape the walk's equation is stated at. *)
  Lemma cat_moi_uint (v : mword 64) :
    (mword_of_int (bv_unsigned v) : mword 64) = v.
  Proof using . rewrite <- uint_unsigned. apply moi_of_uint. Qed.

  (* the deposit family row 16 is read at, at cat's own cursor
     ([UEchoOut.kec_fam]'s mould: an [xfam]-typed argument is not an
     [sfam] until the instance is fixed) *)
  Definition cat_fam (Q : nat -> iProp Σ) : sfam := xfam_wr Q (ukn_pay N).

  (* =================================================================== *)
  (*  [Hw] ITSELF.  The count is [Z.to_nat (bv_unsigned rv)] throughout   *)
  (*  and the walk's [nb] is used ONLY where the register rows demand it, *)
  (*  which is CAT-WALK-2's smaller finding taken seriously.              *)
  (*                                                                     *)
  (*  THE CAP IS A PREMISE AND NOT A CONSEQUENCE, and this is the one     *)
  (*  thing [cat_round_at]'s TAINT arm cannot supply.  The no-short       *)
  (*  refutation is a fact about bytes the CALLER OWNS, and cat owns 512  *)
  (*  of them; so a write of more than 512 is not fundable by this        *)
  (*  payment at all.  In the CONTENT arm the cap rides in [Hw]'s own     *)
  (*  left disjunct ([ard_count 512 p _ <= 512]); in the TAINT arm        *)
  (*  nothing bounds the read's return, because                           *)
  (*  [UkFileOpen.wp_uk_read_deed_learns_mapped]'s taint disjunct is      *)
  (*  [fdq ∗ file_taint c] and says nothing about [rv].  THE MISSING ROW  *)
  (*  IS "a read of [cnt] returns at most [cnt]", and its home is         *)
  (*  [UkRunSys.wp_uk_ecall_read_file]'s post (lane OFF-HAND-6's file),   *)
  (*  relayed through [FileOpen.file_read_arms_learn] -- so it belongs    *)
  (*  with the HELD leaf's obligation and not here.                       *)
  (* =================================================================== *)
  Lemma cat_w_of_link (c : file_fixed) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (l : list fdstate) (rb : bool)
      (p nb : nat) (rv : mword 64) (fbb : nat -> bv 8) :
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    rv = (mword_of_int (Z.of_nat nb) : mword 64) ->
    (Z.to_nat (bv_unsigned rv) <= 512)%nat ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
      /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
           cont (cat_st cs0 s0 I0) LCat (ralt_dec (ralt_enc RCRan))
             !! (p + j)%nat = Some (fbb j)⌝
     ∨ file_taint c) -∗
    UserFd.ustd γfd l -∗
    UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P p -∗
    UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
      (ubytes γd CatSyms.buf 512 fbb)
      (fun wret : mword 64 =>
         (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
          ∗ UserFd.ustd γfd l
          ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P
              (p + Z.to_nat (bv_unsigned rv))%nat
          ∗ ubytes γd CatSyms.buf 512 fbb)).
  Proof using Hcons.
    intros Hgc Hst Hl1 Hrv Hcap.
    set (cnt := Z.to_nat (bv_unsigned rv)).
    pose proof (bv_unsigned_in_range 64 rv) as [Hrvnn _].
    assert (Hmoi : (mword_of_int (Z.of_nat cnt) : mword 64) = rv).
    { unfold cnt. rewrite Z2Nat.id; [ | exact Hrvnn ].
      exact (cat_moi_uint rv). }
    assert (Hcz : sys_rw_count rv = Z.of_nat cnt).
    { rewrite <- Hmoi. apply cat_count_is.
      change (2 ^ 31)%Z with 2147483648%Z. lia. }
    assert (Hok : ralt_ok LCat (ralt_dec (ralt_enc RCRan)))
      by (rewrite ralt_dec_enc; exact UCatOut.cat_ralt_ok_ran).
    pose proof UCatOut.cat_ralt_panic_ran as Hnp.
    iIntros "#Hpin #Hfp Hjust Hstd Hc" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode Hbuf Hrun Hcont".
    (* the three argument rows, at the register file the leaf runs on *)
    assert (Hua : uint (m !!! Regidx a1_idx) = CatSyms.buf).
    { rewrite Ha1. apply uint_moi.
      unfold Z64, CatSyms.buf. lia. }
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx = rv).
    { rewrite Hrv. rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1)
      by (rewrite Ham0; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = cnt)
      by (rewrite Ham2 Hcz; lia).
    (* ---- THE CHAIN, from the row or from the taint ---- *)
    iAssert (∀ M : gmap Z (bv 8),
               ⌜forall j : nat, (j < cnt)%nat ->
                  M !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
                  = Some (fbb j)⌝ -∗
               cons_out_chain (S gen_id) M (m !!! Regidx a1_idx)
                 (fun j : nat => UCatOut.cch g v vf ps0 cs0 s0 I0
                                   (ralt_enc RCRan) P (p + j)%nat)
                 0%nat cnt)%I with "[Hc Hjust]" as "Hmk".
    { iDestruct "Hjust" as "[[%_ %Hline] | #HT]".
      - iIntros (M) "%HM".
        iApply (UCatOut.cch_chain g Hcons (S gen_id) v vf ps0 cs0 s0 I0
                  (ralt_enc RCRan) P p M (m !!! Regidx a1_idx) fbb
                  Hst Hok Hnp cnt 0%nat
                  ltac:(intros j _ Hj; apply Hline; lia)
                  ltac:(intros j _ Hj; apply HM; lia)
                  with "Hpin Hfp [Hc]").
        by rewrite Nat.add_0_r.
      - iIntros (M) "_".
        iApply (UCatOut.cch_chain_taint g Hcons (S gen_id) v vf ps0 cs0 s0 I0
                  (ralt_enc RCRan) P p M (m !!! Regidx a1_idx) cnt 0%nat
                  with "[HT]").
        rewrite <- Hgc. iExact "HT". }
    (* ---- THE RUN: the prefix the call writes, and its two halves ---- *)
    pose (nr := (512 - cnt)%nat).
    assert (Hsz : (cnt + nr)%nat = 512%nat) by (unfold nr; lia).
    iAssert (ubytes γd CatSyms.buf cnt fbb
             ∗ ubytes γd (CatSyms.buf + Z.of_nat cnt) nr
                 (fun j : nat => fbb (cnt + j)%nat))%I
      with "[Hbuf]" as "[Hpre Hsuf]".
    { rewrite <- (ubytes_app γd CatSyms.buf cnt nr fbb).
      rewrite Hsz. iExact "Hbuf". }
    iAssert (ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx)) cnt fbb
             ∗ ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx))
                 cnt fbb)%I with "[Hpre]" as "[Hh1 Hh2]".
    { rewrite Hua. rewrite <- (ubytes_halve γd CatSyms.buf cnt fbb).
      iExact "Hpre". }
    (* ---- THE CALL ---- *)
    iApply (UkCat.wp_kcat_write_chain N h m avail
              (cat_fam (fun j : nat =>
                          (UCatOut.cch g v vf ps0 cs0 s0 I0
                             (ralt_enc RCRan) P (p + j)%nat
                           ∗ ubytesq γd (DfracOwn (1/2))
                               (uint (m !!! Regidx a1_idx)) cnt fbb)%I))
              l (DfracOwn (1/2)) cnt fbb
              with "Hcode Hrun [Hmk Hh2] Hstd Hh1").
    { (* THE DEPOSIT: cat's own chain at its own cursor, and the half of
         the run that the wand hands back through the chain's payload *)
      iApply (uwrite_chain_sup_ret N
                (fun j : nat => UCatOut.cch g v vf ps0 cs0 s0 I0
                                  (ralt_enc RCRan) P (p + j)%nat)
                (ubytesq γd (DfracOwn (1/2))
                   (uint (m !!! Regidx a1_idx)) cnt fbb)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int CatSyms.write : mword 64) 2)
                l 1%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl1).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat γt γd (ukn_s N) M pm sz
                   (DfracOwn (1/2)) (m !!! Regidx a1_idx) cnt fbb
                   with "Hheap Hh2") as %HM.
      iFrame "Hheap Hh2".
      rewrite Ham1 Hcnt.
      iApply ("Hmk" $! M with "[%]"). exact HM. }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hh1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun j : nat =>
                    (UCatOut.cch g v vf ps0 cs0 s0 I0
                       (ralt_enc RCRan) P (p + j)%nat
                     ∗ ubytesq γd (DfracOwn (1/2))
                         (uint (m !!! Regidx a1_idx)) cnt fbb)%I)
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W) cw' cs'
                 l 1%nat rb cnt
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl1
                 ltac:(rewrite Hka2 Ha2 -Hrv; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hws [Hcc Hh2]]".
    iApply ("Hcont" $! h' ret with "[Hstd Hcc Hh1 Hh2 Hsuf] Hrun").
    iSplitR.
    { iPureIntro. rewrite Hws Hmoi. exact Hrv. }
    iFrame "Hstd Hcc".
    rewrite <- Hsz. rewrite (ubytes_app γd CatSyms.buf cnt nr fbb).
    iSplitR "Hsuf"; [ | iExact "Hsuf" ].
    rewrite (ubytes_halve γd CatSyms.buf cnt fbb) -Hua.
    iFrame "Hh1 Hh2".
  Qed.


  (* =================================================================== *)
  (*  6.  THE `cat: cannot open %s` DIAGNOSTIC, FUNDED AT THE CURSOR      *)
  (*      (lane CAT-GEOM, M2).                                           *)
  (*                                                                     *)
  (*  ulib's [fprintf] reaches [write(2, ...)] ONE BYTE AT A TIME out of  *)
  (*  putc's own frame ([UkCatPutc]), so what the arm spends is           *)
  (*  [UkCat.kcat_pay_seq] -- a chain of [UkCat.kcat_wb]s -- and not a    *)
  (*  buffer write.  (a) is [cat_w_of_link] at count ONE with the LENT    *)
  (*  FRAME BYTE as the run, (b) is one induction over the chain, and (c) *)
  (*  is the pure half: the literal's bytes with the argument's spliced   *)
  (*  at [cm_msg_q] ARE [FileDisc.alt_catopen], which is the round's      *)
  (*  continuation at an ABSENT deed ([UCatOut.cat_cont_ran_none];        *)
  (*  CAT-ENTRY's ruling: an absent deed files [RCRan], not [RCNoOpen]).  *)
  (* =================================================================== *)

  (* a ONE-byte run IS the byte, which is what lets putc's lent frame byte
     be halved the way [cat_w_of_link] halves cat's buffer. *)
  Lemma cat_ubytes_one (a : Z) (b : bv 8) :
    ubytes γd a 1%nat (fun _ : nat => b) ⊣⊢ ubyte γd a b.
  Proof using .
    rewrite /ubytes /ubytesq /ubyte /=.
    rewrite Z.add_0_r. apply bi.sep_emp.
  Qed.

  (* ---- (a) ONE BYTE AT THE CURSOR, AT fd 2 -------------------------- *)
  (*                                                                     *)
  (*  [cat_w_of_link] at count 1.  The run is the byte putc LENDS the     *)
  (*  payment ([UkCat.kcat_wb] carries it in [Ci] and takes it back in    *)
  (*  [Co]), the halving is the same, and the no-short equation is needed *)
  (*  HERE TOO: a short write would leave the era's cursor where it was   *)
  (*  while the chain had already advanced.                              *)
  Lemma kcat_wb_of_link (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (a P : nat)
      (l : list fdstate) (rb : bool) (p : nat) (b : bv 8) :
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    ralt_ok LCat (ralt_dec a) ->
    ralt_panic (ralt_dec a) = false ->
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    cont (cat_st cs0 s0 I0) LCat (ralt_dec a) !! p = Some b ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    UkCat.kcat_wb N (mword_of_int 2) b
      (UserFd.ustd γfd l ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P p)
      (UserFd.ustd γfd l ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P (S p)).
  Proof using Hcons.
    intros Hst Hok Hnp Hl2 Hb.
    iIntros "#Hpin #Hfp" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [[Hstd Hc] Hbyte] Hrun Hcont".
    assert (Hcz : sys_rw_count (mword_of_int (Z.of_nat 1) : mword 64)
                  = Z.of_nat 1)
      by (apply cat_count_is; change (2 ^ 31)%Z with 2147483648%Z; lia).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 2)
      by (rewrite Ham0; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2 Hcz; lia).
    (* ---- THE CHAIN: one node, at the round's own cursor ---- *)
    iAssert (∀ M : gmap Z (bv 8),
               ⌜forall j : nat, (j < 1)%nat ->
                  M !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
                  = Some b⌝ -∗
               cons_out_chain (S gen_id) M (m !!! Regidx a1_idx)
                 (fun j : nat => UCatOut.cch g v vf ps0 cs0 s0 I0 a P
                                   (p + j)%nat)
                 0%nat 1%nat)%I with "[Hc]" as "Hmk".
    { iIntros (M) "%HM".
      iApply (UCatOut.cch_chain g Hcons (S gen_id) v vf ps0 cs0 s0 I0
                a P p M (m !!! Regidx a1_idx) (fun _ : nat => b)
                Hst Hok Hnp 1%nat 0%nat
                ltac:(intros j _ Hj;
                      assert (Hj0 : j = 0%nat) by lia; subst j;
                      rewrite Nat.add_0_r; exact Hb)
                ltac:(intros j _ Hj; apply HM; lia)
                with "Hpin Hfp [Hc]").
      by rewrite Nat.add_0_r. }
    (* ---- THE RUN: the lent byte, halved ---- *)
    iAssert (ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx)) 1%nat
               (fun _ : nat => b)
             ∗ ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx)) 1%nat
                 (fun _ : nat => b))%I with "[Hbyte]" as "[Hh1 Hh2]".
    { rewrite <- (ubytes_halve γd (uint (m !!! Regidx a1_idx)) 1%nat
                    (fun _ : nat => b)).
      rewrite cat_ubytes_one Ha1. iExact "Hbyte". }
    (* ---- THE CALL ---- *)
    iApply (UkCat.wp_kcat_write_chain N h m avail
              (cat_fam (fun j : nat =>
                          (UCatOut.cch g v vf ps0 cs0 s0 I0 a P (p + j)%nat
                           ∗ ubytesq γd (DfracOwn (1/2))
                               (uint (m !!! Regidx a1_idx)) 1%nat
                               (fun _ : nat => b))%I))
              l (DfracOwn (1/2)) 1%nat (fun _ : nat => b)
              with "Hcode Hrun [Hmk Hh2] Hstd Hh1").
    { iApply (uwrite_chain_sup_ret N
                (fun j : nat => UCatOut.cch g v vf ps0 cs0 s0 I0 a P
                                  (p + j)%nat)
                (ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx))
                   1%nat (fun _ : nat => b))
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int CatSyms.write : mword 64) 2)
                l 2%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl2).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat γt γd (ukn_s N) M pm sz
                   (DfracOwn (1/2)) (m !!! Regidx a1_idx) 1%nat
                   (fun _ : nat => b) with "Hheap Hh2") as %HM.
      iFrame "Hheap Hh2".
      rewrite Ham1 Hcnt.
      iApply ("Hmk" $! M with "[%]"). exact HM. }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hh1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun j : nat =>
                    (UCatOut.cch g v vf ps0 cs0 s0 I0 a P (p + j)%nat
                     ∗ ubytesq γd (DfracOwn (1/2))
                         (uint (m !!! Regidx a1_idx)) 1%nat
                         (fun _ : nat => b))%I)
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W) cw' cs'
                 l 2%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl2
                 ltac:(rewrite Hka2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hws [Hcc Hh2]]".
    iApply ("Hcont" $! h' ret with "[Hstd Hcc Hh1 Hh2] Hrun").
    iSplitR "Hh1 Hh2".
    - iFrame "Hstd". rewrite Nat.add_1_r. iExact "Hcc".
    - rewrite <- cat_ubytes_one. rewrite Ha1.
      rewrite (ubytes_halve γd (uint ua) 1%nat (fun _ : nat => b)).
      rewrite <- Ha1. iFrame "Hh1 Hh2".
  Qed.

  (* ---- (b) A RUN OF BYTES, BY INDUCTION OVER THE CHAIN --------------- *)
  Lemma kcat_pay_seq_of_link (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (a P : nat)
      (l : list fdstate) (rb : bool) (fb : nat -> bv 8) :
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    ralt_ok LCat (ralt_dec a) ->
    ralt_panic (ralt_dec a) = false ->
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    forall (k i p : nat),
      (forall d : nat, (d < k)%nat ->
         cont (cat_st cs0 s0 I0) LCat (ralt_dec a) !! (p + d)%nat
         = Some (fb (i + d)%nat)) ->
      era_pin (fgn_echo g) (S gen_id) v -∗
      file_era_pin g (S gen_id) vf -∗
      UkCat.kcat_pay_seq N (mword_of_int 2) fb i k
        (UserFd.ustd γfd l ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P p)
        (UserFd.ustd γfd l
         ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P (p + k)%nat).
  Proof using Hcons.
    intros Hst Hok Hnp Hl2.
    induction k as [| k IH]; intros i p Hline; iIntros "#Hpin #Hfp".
    - cbn [UkCat.kcat_pay_seq]. rewrite Nat.add_0_r. by iIntros "$".
    - cbn [UkCat.kcat_pay_seq].
      iExists (UserFd.ustd γfd l
               ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P (S p))%I.
      iSplitR.
      + rewrite <- (Nat.add_0_r i).
        iApply (kcat_wb_of_link v vf ps0 cs0 s0 I0 a P l rb p
                  (fb (i + 0)%nat) Hst Hok Hnp Hl2
                  ltac:(rewrite <- (Nat.add_0_r p);
                        exact (Hline 0%nat ltac:(lia)))
                  with "Hpin Hfp").
      + iPoseProof (IH (S i) (S p)
                      ltac:(intros d Hd;
                            replace (S p + d)%nat with (p + S d)%nat by lia;
                            replace (S i + d)%nat with (i + S d)%nat by lia;
                            exact (Hline (S d) ltac:(lia)))
                      with "Hpin Hfp") as "Hc".
        replace (p + S k)%nat with (S p + k)%nat by lia. iExact "Hc".
  Qed.

  (* ---- (c) THE PURE HALF -------------------------------------------- *)
  (*                                                                     *)
  (*  [FileDisc.alt_catopen] is `cat: cannot open f\n$ ` -- nineteen      *)
  (*  bytes of cat's own output and then the SHELL's prompt.  The three   *)
  (*  readings below say that cat's nineteen ARE the literal's first      *)
  (*  seventeen, the argument's bytes, and the literal's newline; and     *)
  (*  they hold ONLY at an argument of one byte, which is what makes them *)
  (*  closed computations.  (The family over a longer file name is a      *)
  (*  claim about a DIFFERENT alternative -- [FileDisc]'s [alt_catopen]   *)
  (*  names `f` -- so there is nothing to generalise over here.)          *)
  Lemma cat_dg_lit_low (d : nat) :
    (d < UkCatMain.cm_msg_q)%nat ->
    alt_catopen !! d = Some (UkCatMain.cm_lit d).
  Proof using .
    intro Hd.
    assert (Hall : forallb (fun j : nat =>
                              bool_decide (alt_catopen !! j
                                           = Some (UkCatMain.cm_lit j)))
                     (seq 0 UkCatMain.cm_msg_q) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in Hall.
    assert (Hin : In d (seq 0 UkCatMain.cm_msg_q)) by (apply in_seq; lia).
    pose proof (Hall d Hin) as Hb. cbv beta in Hb.
    exact (bool_decide_eq_true_1 _ Hb).
  Qed.

  Lemma cat_dg_lit_high (d : nat) :
    (d < UkCatMain.cm_msg_len - S (S UkCatMain.cm_msg_q))%nat ->
    alt_catopen !! (UkCatMain.cm_msg_q + 1 + d)%nat
    = Some (UkCatMain.cm_lit (S (S UkCatMain.cm_msg_q) + d)%nat).
  Proof using .
    intro Hd.
    assert (Hall : forallb (fun j : nat =>
                              bool_decide
                                (alt_catopen !! (UkCatMain.cm_msg_q + 1 + j)%nat
                                 = Some (UkCatMain.cm_lit
                                           (S (S UkCatMain.cm_msg_q) + j)%nat)))
                     (seq 0 (UkCatMain.cm_msg_len
                             - S (S UkCatMain.cm_msg_q))) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in Hall.
    assert (Hin : In d (seq 0 (UkCatMain.cm_msg_len
                               - S (S UkCatMain.cm_msg_q))))
      by (apply in_seq; lia).
    pose proof (Hall d Hin) as Hb. cbv beta in Hb.
    exact (bool_decide_eq_true_1 _ Hb).
  Qed.

  (* ...and the ONE byte the argument contributes: the file name `f`. *)
  Lemma cat_dg_lit_arg :
    alt_catopen !! UkCatMain.cm_msg_q
    = Some (alt_catopen !!! UkCatMain.cm_msg_q).
  Proof using . vm_compute. reflexivity. Qed.

  (* ---- (d) THE ARM ITSELF: [UkCatMain.kcat_dg_open] AT THE CURSOR ---- *)
  (*                                                                     *)
  (*  Three runs of (b), spliced at [cm_msg_q]: the literal up to the     *)
  (*  directive, the argument's own bytes, and the literal after it.      *)
  (*  The cursor enters at [p] and leaves at [p + 17 + |arg| + 1]; the    *)
  (*  chain's OWN input is [emp] ([UkCatMain.kcat_dg_open] is stated that *)
  (*  way), so the ledger and the cursor are FRAMED IN at the head        *)
  (*  ([UkCat.kcat_pay_seq_frame]).                                       *)
  Lemma cat_dg_open_of_link (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (a P p : nat)
      (l : list fdstate) (rb : bool) (ga : uarg) :
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    ralt_ok LCat (ralt_dec a) ->
    ralt_panic (ralt_dec a) = false ->
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    (forall d : nat, (d < UkCatMain.cm_msg_q)%nat ->
       cont (cat_st cs0 s0 I0) LCat (ralt_dec a) !! (p + d)%nat
       = Some (UkCatMain.cm_lit d)) ->
    (forall d : nat, (d < UserHeap.ua_len ga)%nat ->
       cont (cat_st cs0 s0 I0) LCat (ralt_dec a)
         !! (p + UkCatMain.cm_msg_q + d)%nat
       = Some (UserHeap.ua_bytes ga d)) ->
    (forall d : nat,
       (d < UkCatMain.cm_msg_len - S (S UkCatMain.cm_msg_q))%nat ->
       cont (cat_st cs0 s0 I0) LCat (ralt_dec a)
         !! (p + UkCatMain.cm_msg_q + UserHeap.ua_len ga + d)%nat
       = Some (UkCatMain.cm_lit (S (S UkCatMain.cm_msg_q) + d)%nat)) ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (UserFd.ustd γfd l
     ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P
         (p + UkCatMain.cm_msg_q + UserHeap.ua_len ga
          + (UkCatMain.cm_msg_len - S (S UkCatMain.cm_msg_q)))%nat
     -∗ ukn_pay N (-1)) -∗
    UserFd.ustd γfd l -∗
    UCatOut.cch g v vf ps0 cs0 s0 I0 a P p -∗
    UkCatMain.kcat_dg_open N ga.
  Proof using Hcons.
    intros Hst Hok Hnp Hl2 H1 H2 H3.
    iIntros "#Hpin #Hfp Hend Hstd Hc".
    rewrite /UkCatMain.kcat_dg_open.
    iExists (UserFd.ustd γfd l
             ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P
                 (p + UkCatMain.cm_msg_q)%nat)%I,
            (UserFd.ustd γfd l
             ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P
                 (p + UkCatMain.cm_msg_q + UserHeap.ua_len ga)%nat)%I.
    iSplitL "Hstd Hc"; [| iSplitR "Hend" ].
    - (* the literal up to the directive, with the cursor FRAMED IN *)
      iPoseProof (kcat_pay_seq_of_link v vf ps0 cs0 s0 I0 a P l rb
                    UkCatMain.cm_lit Hst Hok Hnp Hl2
                    UkCatMain.cm_msg_q 0%nat p H1 with "Hpin Hfp") as "Hseq".
      iApply (UkCat.kcat_pay_seq_frame N (mword_of_int 2) UkCatMain.cm_lit
                UkCatMain.cm_msg_q 0%nat emp%I
                (UserFd.ustd γfd l
                 ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P
                     (p + UkCatMain.cm_msg_q)%nat)%I
                (UserFd.ustd γfd l
                 ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P p)%I
                with "[Hstd Hc] [Hseq]").
      { iFrame "Hstd Hc". }
      iApply (UkCat.kcat_pay_seq_in N (mword_of_int 2) UkCatMain.cm_lit
                UkCatMain.cm_msg_q 0%nat
                (UserFd.ustd γfd l
                 ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P p)%I
                (emp ∗ (UserFd.ustd γfd l
                        ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P p))%I
                (UserFd.ustd γfd l
                 ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 a P
                     (p + UkCatMain.cm_msg_q)%nat)%I
                with "[] Hseq").
      iIntros "[_ $]".
    - (* the argument's own bytes *)
      assert (H2' : forall d : nat, (d < UserHeap.ua_len ga)%nat ->
                cont (cat_st cs0 s0 I0) LCat (ralt_dec a)
                  !! ((p + UkCatMain.cm_msg_q) + d)%nat
                = Some (UserHeap.ua_bytes ga (0 + d)%nat))
        by (intros d Hd; exact (H2 d Hd)).
      iApply (kcat_pay_seq_of_link v vf ps0 cs0 s0 I0 a P l rb
                (UserHeap.ua_bytes ga) Hst Hok Hnp Hl2
                (UserHeap.ua_len ga) 0%nat (p + UkCatMain.cm_msg_q)%nat
                H2' with "Hpin Hfp").
    - (* the literal after it, and then the exit's payload *)
      iApply (UkCat.kcat_pay_seq_mono N (mword_of_int 2) UkCatMain.cm_lit
                (UkCatMain.cm_msg_len - S (S UkCatMain.cm_msg_q))%nat
                (S (S UkCatMain.cm_msg_q)) _ _ _ with "Hend").
      iApply (kcat_pay_seq_of_link v vf ps0 cs0 s0 I0 a P l rb
                UkCatMain.cm_lit Hst Hok Hnp Hl2
                (UkCatMain.cm_msg_len - S (S UkCatMain.cm_msg_q))%nat
                (S (S UkCatMain.cm_msg_q))
                (p + UkCatMain.cm_msg_q + UserHeap.ua_len ga)%nat
                H3 with "Hpin Hfp").
  Qed.

  (* ...AND AT AN ABSENT DEED, where the three pure premises are closed.
     [UCatOut.cat_cont_ran_none]: at [s = None] the round's continuation IS
     [FileDisc.alt_catopen] -- CAT-ENTRY's ruling that an ABSENT deed files
     [RCRan] and not [RCNoOpen].  cat's run is the first NINETEEN of its
     twenty-one bytes; the last two are the SHELL's prompt. *)
  Lemma cat_dg_open_absent (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (l : list fdstate) (rb : bool) (ga : uarg) (s : dst) :
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 s -> s = None ->
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserHeap.ua_len ga = 1%nat ->
    UserHeap.ua_bytes ga 0%nat = alt_catopen !!! UkCatMain.cm_msg_q ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (UserFd.ustd γfd l
     ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 19%nat
     -∗ ukn_pay N (-1)) -∗
    UserFd.ustd γfd l -∗
    UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat -∗
    UkCatMain.kcat_dg_open N ga.
  Proof using Hcons.
    intros Hst Htie Hs Hl2 Hlen Hb0.
    assert (Hcont : cont (cat_st cs0 s0 I0) LCat (ralt_dec (ralt_enc RCRan))
                    = alt_catopen)
      by (rewrite ralt_dec_enc;
          exact (cat_out_of_tie_none cs0 s0 I0 s Htie Hs)).
    iIntros "#Hpin #Hfp Hend Hstd Hc".
    iApply (cat_dg_open_of_link v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat
              l rb ga Hst UCatOut.cat_ralt_ok_ran
              UCatOut.cat_ralt_panic_ran Hl2
              ltac:(intros d Hd; rewrite Hcont; cbn [Nat.add];
                    exact (cat_dg_lit_low d Hd))
              ltac:(intros d Hd; rewrite Hcont Hlen in Hd |- *;
                    assert (Hd0 : d = 0%nat) by lia; subst d;
                    cbn [Nat.add]; rewrite Hb0;
                    exact cat_dg_lit_arg)
              ltac:(intros d Hd; rewrite Hcont Hlen; cbn [Nat.add];
                    exact (cat_dg_lit_high d Hd))
              with "Hpin Hfp [Hend] Hstd Hc").
    rewrite Hlen. iExact "Hend".
  Qed.

  (* ---- [Hw] ITSELF, FROM [cat_w_of_link] (lane CAT-GEOM-2). ----
     CAT-ENTRY-2 left this as its one open kernel row: [cat_w_of_link]
     takes the 512-byte cap as a Coq premise and [cat_round_at]'s [Hw]
     used to carry it only on the CONTENT arm, so the TAINT arm was
     unsuppliable.  Lane OFF-LINK's count bound -- "a read of [cnt] bytes
     reports at most [cnt]" -- now rides in [cat_held_read]'s post on
     BOTH arms, [cat_round_at] hands it to [Hw] on both, and [Hw] is
     [cat_w_of_link] outright. *)
  Lemma cat_hw_of_link (c : file_fixed) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (l : list fdstate) (rb : bool) :
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    □ (∀ (p nb : nat) (rv : mword 64) (fbb : nat -> bv 8),
         ⌜rv = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
         (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
           /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                cont (cat_st cs0 s0 I0) LCat (ralt_dec (ralt_enc RCRan))
                  !! (p + j)%nat = Some (fbb j)⌝
          ∨ (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat⌝ ∗ file_taint c)) -∗
         UserFd.ustd γfd l -∗
         UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P p -∗
         UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
           (ubytes γd CatSyms.buf 512 fbb)
           (fun wret : mword 64 =>
              (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
               ∗ UserFd.ustd γfd l
               ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P
                   (p + Z.to_nat (bv_unsigned rv))%nat
               ∗ ubytes γd CatSyms.buf 512 fbb))).
  Proof using Hcons.
    intros Hgc Hst Hl1.
    iIntros "#Hpin #Hfp !>" (p nb rv fbb) "%Hrv Hjust Hstd Hc".
    iDestruct "Hjust" as "[%Hleft | [%Hcap #HT]]".
    - iApply (cat_w_of_link c v vf ps0 cs0 s0 I0 P l rb p nb rv fbb
                Hgc Hst Hl1 Hrv (proj1 Hleft) with "Hpin Hfp [] Hstd Hc").
      iLeft. iPureIntro. exact Hleft.
    - iApply (cat_w_of_link c v vf ps0 cs0 s0 I0 P l rb p nb rv fbb
                Hgc Hst Hl1 Hrv Hcap with "Hpin Hfp [] Hstd Hc").
      iRight. iExact "HT".
  Qed.

  (* ...AND THE SAME DIAGNOSTIC AT A PRESENT-BUT-UNOPENABLE FILE.
     CAT-ENTRY's ruling in full: an ABSENT deed files [RCRan] (above) and
     a PRESENT one whose open returned [-1] files [RCNoOpen], and the two
     print the SAME bytes ([UCatOut.cat_cont_noopen]).  The alternative is
     not decided before the first byte ([UCatOut.cch_0_alt]), so a payer
     holding the cursor at ZERO may re-index it to whichever the deed
     turns out to name. *)
  Lemma cat_dg_open_noopen (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (l : list fdstate) (rb : bool) (ga : uarg) :
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserHeap.ua_len ga = 1%nat ->
    UserHeap.ua_bytes ga 0%nat = alt_catopen !!! UkCatMain.cm_msg_q ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (UserFd.ustd γfd l
     ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCNoOpen) P 19%nat
     -∗ ukn_pay N (-1)) -∗
    UserFd.ustd γfd l -∗
    UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCNoOpen) P 0%nat -∗
    UkCatMain.kcat_dg_open N ga.
  Proof using Hcons.
    intros Hst Hl2 Hlen Hb0.
    assert (Hcont : cont (cat_st cs0 s0 I0) LCat
                      (ralt_dec (ralt_enc RCNoOpen)) = alt_catopen)
      by (rewrite ralt_dec_enc; exact (cat_cont_noopen (cat_st cs0 s0 I0))).
    iIntros "#Hpin #Hfp Hend Hstd Hc".
    iApply (cat_dg_open_of_link v vf ps0 cs0 s0 I0 (ralt_enc RCNoOpen) P
              0%nat l rb ga Hst UCatOut.cat_ralt_ok_noopen
              UCatOut.cat_ralt_panic_noopen Hl2
              ltac:(intros d Hd; rewrite Hcont; cbn [Nat.add];
                    exact (cat_dg_lit_low d Hd))
              ltac:(intros d Hd; rewrite Hcont Hlen in Hd |- *;
                    assert (Hd0 : d = 0%nat) by lia; subst d;
                    cbn [Nat.add]; rewrite Hb0;
                    exact cat_dg_lit_arg)
              ltac:(intros d Hd; rewrite Hcont Hlen; cbn [Nat.add];
                    exact (cat_dg_lit_high d Hd))
              with "Hpin Hfp [Hend] Hstd Hc").
    rewrite Hlen. iExact "Hend".
  Qed.

  (* ...and the CLOSE, at a descriptor the caller's own INPUT carries.
     [UkCat.kcat_cl_of_dep] wants [UserFd.ufd] in hand when the
     obligation is BUILT; cat's descriptor is inside the round's
     invariant until the loop stops, so the close reads it out of [Ci]
     instead. *)
  Lemma cat_cl_of_in (fd : nat) (st : fdstate) (Ci Co : iProp Σ) :
    fdst_nopipe st ->
    (Ci -∗ UserFd.ufd γfd fd st ∗ Co) -∗ UkCat.kcat_cl N fd Ci Co.
  Proof using .
    intros Hnp. iIntros "Hm" (h m avail) "%Ha0 #Hcode HCi Hrun Hcont".
    iDestruct ("Hm" with "HCi") as "[Hfdh HCo]".
    iApply (UkCat.wp_kcat_close N h m fd st avail Ha0
              with "[] Hcode Hrun Hfdh").
    { iApply (UkCat.kcat_cldep_nopipe N st Hnp). }
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "HCo Hrun").
  Qed.

End UCatKernel.

(* ===================================================================== *)
(*  THE ENTRY TIER: THE RECORD IS NOT FIXED (lane CAT-GEOM-2).            *)
(*                                                                       *)
(*  Everything above is stated at ONE [uk_names] record -- the section's  *)
(*  [N] -- because a walk runs at the record its own [UkRun.urun] was     *)
(*  minted with.  An ENTRY does not: it ALLOCATES the record, so its      *)
(*  payment is owed at whatever [UkRun.uslot_of_urun_all] hands out, and  *)
(*  the obligation has to be quantified over it.  Applying a             *)
(*  section-[N] lemma under that ∀ is the trap durable-notes names: the   *)
(*  two records print identically and do not unify, and the [iApply]      *)
(*  never terminates (2.5 GB of stable RSS and no error).  So the entry   *)
(*  tier is its own section, and every result above is used at an         *)
(*  EXPLICIT record.                                                     *)
(* ===================================================================== *)
Section UCatEntry.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  (* =================================================================== *)
  (*  7.  cat's ENTRY (lane CAT-GEOM, M3).                                *)
  (*                                                                     *)
  (*  [UShEchoPay.echo_slot_of_kexec_at]'s mould at cat, over             *)
  (*  [ExecEntry.image_entry] as [ExecBundle.exec_bundle_of]'s third      *)
  (*  premise takes it, and it is [UShRound.v]'s [Hchild_cat] with the    *)
  (*  node premises added -- sh BUILT the node, so sh can supply them.    *)
  (*                                                                     *)
  (*  THE PAYMENT IS A PARAMETER ([cat_pay_at] below), for the reason the *)
  (*  notes give: a block lemma that names its own postcondition cannot   *)
  (*  be reused by a parallel proof.  The GEOMETRY -- everything between  *)
  (*  the exec channel's image fact and [UkCatMain.wp_kcat_start] --      *)
  (*  is discharged here once, and what remains is a payment stated at    *)
  (*  the record the entry allocates.                                    *)
  (*                                                                     *)
  (*  [cw], [cs] and [pidv] are FREE: cat reads no identity row, so the   *)
  (*  entry holds at whatever the caller's are.  ([UkCatDeed.             *)
  (*  kcat_o_of_deed] does read the cwd, and its [um_start_of cw pl =     *)
  (*  ROOTINO] premise is where [cw] is pinned -- inside the PAYMENT,     *)
  (*  not here.)                                                         *)
  (* =================================================================== *)
  (* the file name, as the three closed facts the open's deed corollary
     and the path reading want of it *)
  Lemma cat_fname_shape : arg_path_shape FsImgCheck.fname_f.
  Proof using .
    split; [ vm_compute; reflexivity | ].
    intros j b Hb.
    destruct j as [| j]; cbn in Hb; [ | discriminate Hb ].
    injection Hb as <-.
    intro Hc. apply (f_equal bv_unsigned) in Hc.
    vm_compute in Hc. discriminate Hc.
  Qed.

  Lemma cat_fname_elems : path_elems FsImgCheck.fname_f = [FsImgCheck.fname_f].
  Proof using . vm_compute. reflexivity. Qed.

  Lemma cat_fname_start (cwv : Z) :
    um_start_of cwv FsImgCheck.fname_f = cwv.
  Proof using .
    unfold FsAbsEra.um_start_of.
    destruct (decide (FsImgCheck.fname_f !! 0%nat = Some PathElems.SLASH))
      as [He | _]; [ | reflexivity ].
    exfalso. vm_compute in He. discriminate He.
  Qed.

  Definition cat_pay_at (W : uvis) (Q : Z -> iProp Σ) (Pay : iProp Σ)
    : iProp Σ :=
    (∀ N : uk_names Σ,
       ⌜ ukn_pay N = Q ⌝ -∗
       (* WHAT THE PAYER MAY ASSUME ABOUT THE KEY IT IS PAYING AT.  The
          entry derives all three from the CALLER's reading of the node it
          built ([UShCat.cat_args_det_holds]) through the key's own
          ([UShCat.cat_key_args_holds]): the line is `cat f`, so argv has
          two words and the second is the one-byte file name the claim is
          about.  Without them a payer cannot run the open's deed
          corollary at all -- [UkCatDeed.kcat_o_of_deed] resolves
          [fname_f] and nothing else. *)
       ⌜ Z.to_nat (uvis_argc W) = 2%nat ⌝ -∗
       ⌜ forall ga : uarg, UShCat.cat_args W !! 1%nat = Some ga ->
           UserHeap.ua_len ga = 1%nat
           /\ forall j : nat, (j < 1)%nat ->
                UserHeap.ua_bytes ga j = FsImgCheck.fname_f !!! j ⌝ -∗
       (* ...AND THE PATH argv[1] NAMES, as the open's deed corollary
          takes it: a PURE implication over every image the persisted
          area is contained in ([UShCat.cat_kexec_argpath]).  A resource
          cannot serve here -- [UkCatDeed.kcat_o_of_deed_miss]'s premise
          is quantified over the image the KERNEL will read. *)
       ⌜ forall M : gmap Z (bv 8),
           uimg_sub (base.filter
                       (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W)))
                       (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W))) M ->
           forall ga : uarg, UShCat.cat_args W !! 1%nat = Some ga ->
             arg_path_of M (mword_of_int (UserHeap.ua_ptr ga))
               FsImgCheck.fname_f ⌝ -∗
       UserFd.ustd (ukn_fd N) (take NSTD (uvis_fd W)) -∗
       UserCwd.ucwd (ukn_cwd N) (uvis_cwd W) -∗
       UCodeCat.cat_code (ukn_t N) -∗
       UCodeCat.cat_rodata (ukn_t N) -∗
       UserHeap.uargv (ukn_d N) (uvis_av W) (UShCat.cat_args W) -∗
       (* ...and the PERSISTED argument area, which the open's deed
          corollary resolves its path out of *)
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq (ukn_d N) DfracDiscarded k b) -∗
       Pay -∗
       ∃ Ci : iProp Σ,
         UkCatMain.kcat_pay_all N (UShCat.cat_args W) Ci (ukn_pay N (-1))
         ∗ Ci)%I.

  Lemma cat_image_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    (* THE LINE IS `cat f`: two words, the second one byte, and that byte
       is the name of the file the claim is about. *)
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = 1%nat ->
    (forall j : nat, (j < 1)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    (* ...AND THE PAYMENT, at the key the entry is about to allocate the
       record for.  It is handed the key's TABLE and its CWD (lane
       CAT-GEOM-3): a payer at the claim states its fd rows and its
       [fd_lowest_closed] about [sts], which is what the exec channel
       carries ([SpecKexec.kexec_image_ok_fd]), and the deed open
       resolves a relative path at [cw]. *)
    □ (∀ W' : uvis, ⌜uvis_fd W' = sts⌝ -∗ ⌜uvis_cwd W' = cw⌝ -∗
         cat_pay_at W' Q Pay) -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using xv6G0 ufdG0.
    intros HQc Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname.
    iIntros "#Hpay #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShCat.cat_args_det_holds ws Hok Mn sv t gn na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    pose proof (UShCat.cat_room_of_det_x ws na alen Hok Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf _ _ Hmp HPay".
    destruct (UShCat.cat_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hbufb & Hwr & Hrp).
    destruct (UShCat.cat_kexec_entry_rows na alen afun sts W' Hokk Hroom
                Hfdl Hwr Hrp)
      as (Hroom336 & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (UShCat.cat_kexec_bufrow na alen afun sts W' Hokk Hroom
                  Hdw Hbufb) as Hbuf.
    pose proof (UShCat.cat_kexec_argnz na alen afun sts W' Hokk Hroom)
      as Hnz.
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hokk) as Hfd.
    assert (Hargc0 : 0 <= uvis_argc W')
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargsrow)).
    assert (Hptr : forall (j : nat) (ga : uarg),
              UShCat.cat_args W' !! j = Some ga -> UserHeap.ua_ptr ga <> 0).
    { intros j ga Hj.
      assert (Hlt : (j < Z.to_nat (uvis_argc W'))%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hl.
        rewrite /UShCat.cat_args echo_args_length in Hl. exact Hl. }
      rewrite /UShCat.cat_args (echo_args_lookup (uvis_M W') (uvis_av W')
                                  (Z.to_nat (uvis_argc W')) j Hlt) in Hj.
      injection Hj as <-. cbn [UserHeap.ua_ptr echo_arg].
      exact (Hnz j Hlt). }
    (* ---- THE KEY'S OWN READING OF `cat f` ---- *)
    assert (Hno : forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
              afun i j <> ubyte0).
    { intros i j Hi Hj.
      rewrite (Hafun i j ltac:(lia)
                 ltac:(rewrite <- (Halen i ltac:(lia)); exact Hj)).
      apply (UShEcho.line_nonul_x ws _ Hok).
      exact (UkShEcho.echo_off_lt_x ws i j Hok ltac:(lia)
               ltac:(rewrite <- (Halen i ltac:(lia)); lia)). }
    destruct (UShCat.cat_key_args_holds na alen afun sts W' Hokk Hno)
      as [Hargcna Hkey].
    assert (Hargc2 : Z.to_nat (uvis_argc W') = 2%nat)
      by (rewrite Hargcna Hna; exact Hws2).
    destruct (Hkey 1%nat ltac:(lia)) as [Hkl Hkb].
    assert (Halenv1 : alen 1%nat = 1%nat)
      by (rewrite (Halen 1%nat ltac:(lia)); exact Halen1).
    assert (Harg1f : forall ga : uarg,
              UShCat.cat_args W' !! 1%nat = Some ga ->
              UserHeap.ua_len ga = 1%nat
              /\ forall j : nat, (j < 1)%nat ->
                   UserHeap.ua_bytes ga j = FsImgCheck.fname_f !!! j).
    { intros ga Hga.
      rewrite /UShCat.cat_args
              (echo_args_lookup (uvis_M W') (uvis_av W')
                 (Z.to_nat (uvis_argc W')) 1%nat ltac:(lia)) in Hga.
      injection Hga as <-. split; [ rewrite Hkl; exact Halenv1 | ].
      intros j Hj.
      rewrite (Hkb j ltac:(lia)).
      rewrite (Hafun 1%nat j ltac:(lia) ltac:(lia)).
      exact (Hfname j Hj). }
    (* ...and the path argv[1] names, out of the persisted area *)
    assert (Hargpath : forall M : gmap Z (bv 8),
              uimg_sub (base.filter
                          (fun kv : Z * bv 8 =>
                             ~ (kv.1 < uint (uvis_sp W')))
                          (udata_lo (uvis_M W') (uvis_perm W')
                             (uvis_sz W'))) M ->
              forall ga : uarg, UShCat.cat_args W' !! 1%nat = Some ga ->
                arg_path_of M (mword_of_int (UserHeap.ua_ptr ga))
                  FsImgCheck.fname_f).
    { intros M Hsubm ga Hga.
      rewrite /UShCat.cat_args
              (echo_args_lookup (uvis_M W') (uvis_av W')
                 (Z.to_nat (uvis_argc W')) 1%nat ltac:(lia)) in Hga.
      injection Hga as <-. cbn [UserHeap.ua_ptr echo_arg].
      apply (UShCat.cat_kexec_argpath na alen afun sts W' 1%nat
               FsImgCheck.fname_f Hokk Hroom Hwr ltac:(lia)
               ltac:(rewrite Halenv1; reflexivity)
               ltac:(intros j b Hb;
                     assert (Hj : (j < 1)%nat)
                       by exact (lookup_lt_Some _ _ _ Hb);
                     assert (Hj0 : j = 0%nat) by lia; subst j;
                     injection Hb as <-;
                     rewrite (Hafun 1%nat 0%nat ltac:(lia) ltac:(lia));
                     symmetry; exact (Hfname 0%nat ltac:(lia)))
               cat_fname_shape M Hsubm). }
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (UShCat.cat_entry_run W' Q Hpc Hsub Hsub2 Hx Hroom336 Hal8
              Hstkrow Hbuf Hargsrow Havd Havs Hfdlen Hstop Hlzf
              with "Hdep Hnpw' Hmp").
    iIntros (N' h) "%Hpayeq Hstd Hcwf #Hcode #Hro #Hargv #HA Hbuf' Hrun".
    pose proof (ukn_const_of_eq N' Q Hpayeq HQc) as Htc.
    iDestruct ("Hpay" $! W' with "[%] [%]") as "Hpay'";
      [ exact Hfd | exact Hcwv | ].
    iDestruct ("Hpay'" $! N'
                 with "[%] [%] [%] [%] Hstd Hcwf Hcode Hro Hargv HA HPay")
      as (Ci) "[Hp HCi]";
      [ exact Hpayeq | exact Hargc2 | exact Harg1f | exact Hargpath | ].
    iApply (wp_kcat_start N' h (tf_resume_gpr0 (uvis_tf W')) (uvis_av W')
              (UShCat.cat_args W') (fun _ : nat => ubyte0) 0%nat Ci
              Hptr
              ltac:(rewrite /UShCat.cat_args echo_args_length;
                    rewrite (Z2Nat.id (uvis_argc W') Hargc0);
                    unfold uvis_argc; symmetry; apply moi_of_uint)
              ltac:(unfold uvis_av; symmetry; apply moi_of_uint)
              with "Hp Hcode Hro Hargv HCi Hbuf' Hrun").
  Qed.

  (* ...AND THE PAYMENT IS INHABITED, which is the ANTI-VACUITY WITNESS of
     the entry above: the four free laws pay [kcat_pay_all] at the trivial
     payload ([UkCatMain.kcat_pay_all_of_law]), so [cat_image_entry]'s one
     obligation is not a premise nobody can supply.  (The free open law can
     only fund an open that FAILS, which is what [fd_lowest_closed] says;
     the CLAIM-side payment is the one lane OFF-LINK's rows complete.) *)
  Lemma cat_pay_at_of_law (W : uvis) :
    fd_lowest_closed (take NSTD (uvis_fd W)) = None ->
    (* NO [udepw_law 21] (lane SUP-ONE): the close is free at the
       descriptor the open's own leaf exports [FdSlots.fdst_nopipe] for *)
    UkRun.udepw_law 5 -∗ UkRun.udepw_law 15 -∗ UkRun.udepw_law 16 -∗
    cat_pay_at W (fun _ => True)%I emp%I.
  Proof using .
    intros Hnone. iIntros "#Hrd #Hop #Hwr".
    rewrite /cat_pay_at. iIntros (N') "%Hpayeq %H2 %H3 %H4 Hstd _ _ _ _ _ _".
    pose proof (Hpayeq : UkRun.ukn_triv N') as Hti.
    iExists (UserFd.ustd (ukn_fd N') (take NSTD (uvis_fd W))).
    iFrame "Hstd".
    iApply (UkCatMain.kcat_pay_all_of_law N' (UShCat.cat_args W)
              (take NSTD (uvis_fd W)) Hnone with "[] Hrd Hop Hwr").
    iModIntro. iApply (ukn_pay_free_of_triv N' Hti).
  Qed.

  (* =================================================================== *)
  (*  8.  cat's PAYMENT AT THE CLAIM: THE ABSENT ARM (lane CAT-GEOM-2).   *)
  (* =================================================================== *)

  (* ---- the frame across the open.  [UkCat.kcat_o] has no frame law of
     its own and cat's console cursor has to cross the call: the payer
     holds it and the continuation gets it back beside the open's own
     answer. ---- *)
  Lemma kcat_o_frame (N' : uk_names Σ) (pv : mword 64) (Oi : iProp Σ)
      (Oo : mword 64 -> iProp Σ) (C : iProp Σ) :
    C -∗ UkCat.kcat_o N' pv Oi Oo -∗
    UkCat.kcat_o N' pv Oi (fun ret : mword 64 => Oo ret ∗ C).
  Proof using .
    iIntros "HC Ho" (h m avail) "%Ha0 %Ha1 #Hcode HOi Hrun Hcont".
    iApply ("Ho" $! h m avail with "[%] [%] Hcode HOi Hrun");
      [ exact Ha0 | exact Ha1 | ].
    iIntros (h' ret) "HOo Hrun".
    iApply ("Hcont" $! h' ret with "[HOo HC] Hrun"). iFrame "HOo HC".
  Qed.

  (* ---- NAMED: THE TAINT'S DESCRIPTOR SUB-ARM. ----
     At a TAINTED era the open may still return a handle -- the leaf's
     [UkFileOpen.uk_open_taint_fd] says so and the deed says nothing --
     and what cat does next is READ, which the taint does NOT buy back:
     [UexecExecMint.udepw_law_of_sup] mints 15 and 17 off [AppInv.app_sup]
     and [_write]/[_close]/[_exit] mint 16, 21 and 93, but FIVE is
     excluded by construction.  So a tainted cat's LOOP is an obligation
     of its own; it is named here rather than assumed away, and it is
     EXACTLY the right conjunct of [UkCatMain.kcat_file]'s output, so a
     supplier plugs in by [iApply]. *)
  Definition cat_taint_open (N' : uk_names Σ) (c : file_fixed)
      (l : list fdstate) (Co : iProp Σ) : iProp Σ :=
    (□ (∀ ret : mword 64,
          file_taint c -∗
          UkFileOpen.uk_open_taint_fd (ukn_fd N') l ret -∗
          ⌜(0 <= bv_signed ret)%Z⌝ -∗
          ∃ (fd : nat) (Cm : iProp Σ),
            ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)⌝
            ∗ ⌜(fd < NOFILE)%nat⌝
            ∗ UkCatMain.kcat_run0 N' (mword_of_int (Z.of_nat fd)) Cm
            ∗ UkCat.kcat_cl N' fd Cm Co))%I.

  (* THE APPLICATION'S SUPPLY, OUT OF ITS OWN TAINT.
     [AppFile.file_sup_of_taint] at the era's record: once the file
     application's discipline is broken the generic supply is available,
     and with [RiscvPtsto.app_taint] beside it that is what mints rows 5
     and 16 ([UexecExecMint.udepw_law_of_sup_read] / [_write]). *)
  Lemma cat_app_sup_of_taint (c : file_fixed) (r : file_names) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    file_taint c -∗ app_sup.
  Proof using .
    intros Heq. iIntros "#HT". rewrite /AppInv.app_sup.
    rewrite Heq. cbn [app_pred app_run].
    iApply (AppFile.file_sup_of_taint c r with "HT").
  Qed.

  (* ---- ...AND IT IS DISCHARGED (lane CAT-GEOM-4).  With
     [UkCatCat.kcat_round_of_law] and [UkCat.kcat_pay_seq_of_law] taking
     their exit payload as a PERSISTENT RESOURCE rather than a Coq
     entailment, a tainted cat can keep walking: the round is the free
     one, the close is free at the [FdSlots.fdst_nopipe] the open's own
     leaf exports, and the payload is the one the taint itself gives
     ([UCatOut.cch]'s right disjunct).  WHERE THE TWO LAWS COME FROM at a
     tainted era: [UexecExecMint.udepw_law_of_sup_read] (lane CAT-GEOM-3)
     and [udepw_law_of_sup_write], both out of [AppInv.app_sup ∗
     app_taint], and [AppFile.file_sup_of_taint] turns the application's
     own [file_taint] into the first of those. ---- *)
  Lemma cat_taint_open_of_law (N' : uk_names Σ) (c : file_fixed)
      (l : list fdstate) (Co : iProp Σ) :
    fd_lowest_closed l = None ->
    □ (file_taint c -∗ Co) -∗
    □ (file_taint c -∗ ukn_pay N' (-1)) -∗
    □ (file_taint c -∗ UkRun.udepw_law 5) -∗
    □ (file_taint c -∗ UkRun.udepw_law 16) -∗
    cat_taint_open N' c l Co.
  Proof using .
    intros Hnone. iIntros "#HCow #HCw #Hrdw #Hwrw".
    rewrite /cat_taint_open. iIntros "!>" (ret) "#HT Hf %Hpos".
    iAssert (□ Co)%I as "#HCo"; [ iModIntro; iApply ("HCow" with "HT") | ].
    iAssert (□ (ukn_pay N' (-1)))%I as "#HC";
      [ iModIntro; iApply ("HCw" with "HT") | ].
    iPoseProof ("Hrdw" with "HT") as "#Hrd".
    iPoseProof ("Hwrw" with "HT") as "#Hwr".
    iDestruct "Hf" as "[Hal | [%Hm1 _]]"; last first.
    { exfalso. rewrite Hm1 in Hpos. vm_compute in Hpos. lia. }
    iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]".
    destruct Hb as (Hr1 & Hlt1 & Hnp).
    iDestruct (ualloc_hi (ukn_fd N') l fd (FdOpen rd wr t) Hnone with "Hal")
      as "(_ & _ & Hufdh)".
    iExists fd,
      (UserFd.ufd (ukn_fd N') fd (FdOpen rd wr t) ∗ Co)%I.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitL "Hufdh".
    - rewrite /UkCatMain.kcat_run0.
      iExists emp%I, emp%I.
      iSplitR "Hufdh";
        [ iApply (UkCatCat.kcat_round_of_law N'
                    (mword_of_int (Z.of_nat fd)) with "HC Hrd Hwr") | ].
      iSplitR "Hufdh"; [ done | ].
      iIntros "_". iFrame "Hufdh". iExact "HCo".
    - iApply (cat_cl_of_in N' fd (FdOpen rd wr t) _ _ Hnp).
      by iIntros "[$ $]".
  Qed.

  (* ...AND AT THE APPLICATION'S OWN TAINT, WITH NO LAW PREMISE LEFT.
     [AppFile.file_sup_of_taint] gives the generic supply, [app_taint] is
     the machine's credential the boot threads down, and the two rows
     are [UexecExecMint.udepw_law_of_sup_read] (lane CAT-GEOM-3) and
     [udepw_law_of_sup_write].  THIS IS WHAT CAT-GEOM-2 NAMED AS A GAP
     AND CAT-GEOM-3 REDUCED TO TWO [(⊢ _)] PREMISES; with those two
     generalised to [□ _] (item 1) there is nothing left to name. *)
  Lemma cat_taint_open_of_taint (N' : uk_names Σ) (c : file_fixed)
      (r : file_names) (l : list fdstate) (Co : iProp Σ) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    fd_lowest_closed l = None ->
    □ (file_taint c -∗ Co) -∗
    □ (file_taint c -∗ ukn_pay N' (-1)) -∗
    (* THE MACHINE'S CREDENTIAL COMES FROM THE APPLICATION'S FLAG, under
       the flag.  This premise used to be [app_taint] OUTRIGHT, which made
       every consumer -- [cat_child_of_entry], hence the round's cat child
       -- a statement about an out-of-spec run only.  The sub-arm is
       entered WITH [file_taint c] in hand, so the conversion is all it
       needs ([cat_held_read_of_deed] takes the same box). *)
    □ (file_taint c -∗ app_taint) -∗
    cat_taint_open N' c l Co.
  Proof using .
    intros Heq Hnone. iIntros "#HCow #HCw #Hkc".
    iApply (cat_taint_open_of_law N' c l Co Hnone with "HCow HCw [] []").
    - iIntros "!> #HT". iDestruct ("Hkc" with "HT") as "#Hk".
      iApply (UexecExecMint.udepw_law_of_sup_read with "[HT] Hk").
      iApply (cat_app_sup_of_taint c r Heq with "HT").
    - iIntros "!> #HT". iDestruct ("Hkc" with "HT") as "#Hk".
      iApply (UexecExecMint.udepw_law_of_sup_write with "[HT] Hk").
      iApply (cat_app_sup_of_taint c r Heq with "HT").
  Qed.

  (* ---- THE ABSENT ARM, WHOLE.  [UkCatDeed.kcat_o_of_deed_miss] then
     [cat_dg_open_absent]: the open at an ABSENT deed returns [-1] and
     cat's whole turn is the `cat: cannot open f` run, at the cursor its
     round opens ([UCatOut.cch … 0]) and leaving it at NINETEEN. ---- *)
  Lemma cat_pay_absent (W : uvis) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (rb : bool)
      (Q : Z -> iProp Σ) (s : dst) (F : iProp Σ) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 s -> s = None ->
    uvis_cwd W = FsImg.ROOTINO ->
    take NSTD (uvis_fd W) !! 2%nat
      = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    fd_lowest_closed (take NSTD (uvis_fd W)) = None ->
    app_inv fsc_fs -∗
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (* the exit payload, at CAT'S OWN end cursor
       ([UCatOut.cat_out_len_ran_none]) *)
    (* ...WHICH RETURNS WHAT WAS LENT (RULING CAT-DEED, amended): the
       fraction goes into the open and comes back on its [-1] arm, so the
       exit hands the payload the SAME [fdq r q None]; out of spec there
       is none to hand, and the payload is built from the flag. *)
    □ (UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 19%nat
       -∗ fdq r q None -∗ F -∗ Q (-1)) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    (* ...AND THE TAINT'S DESCRIPTOR SUB-ARM, at the record the entry
       allocates AND at its payload equation -- a supplier needs to know
       what [ukn_pay N'] IS before it can produce anything at [Q (-1)]
       ([cat_taint_open_of_taint] discharges it). *)
    (∀ N' : uk_names Σ, ⌜ukn_pay N' = Q⌝ -∗
       cat_taint_open N' c (take NSTD (uvis_fd W)) (Q (-1))) -∗
    (* [F] is the frame ([cat_pay_present]'s note) *)
    cat_pay_at W Q
      (fdq r q None
       ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat ∗ F).
  Proof using Hcons.
    intros Heq Hgc Hst Htie Hs Hcw Hl2 Hnone.
    iIntros "#Hinv #Hpin #Hfp #Hend #Hqt #Htaint".
    rewrite /cat_pay_at.
    iIntros (N') "%Hpayeq %Hargc2 %Harg1 %Hpath Hstd Hcwf #Hcode #Hro
                  #Hargv #HA (Hd & Hc & HF)".
    iCombine "Hc HF" as "Hc".
    (* cat's argument vector has two words, and word 1 is `f` *)
    destruct (lookup_lt_is_Some_2 (UShCat.cat_args W) 1%nat
                ltac:(rewrite /UShCat.cat_args echo_args_length; lia))
      as [ga Hga].
    destruct (Harg1 ga Hga) as [Hglen Hgb].
    iExists (UkCatDeed.kcat_open_hold N' (take NSTD (uvis_fd W))
               (uvis_cwd W) ∗ fdq r q None)%I.
    iSplitR "Hstd Hcwf Hd"; last first.
    { rewrite /UkCatDeed.kcat_open_hold. iFrame "Hstd Hcwf Hd". }
    rewrite /UkCatMain.kcat_pay_all. iSplit.
    { (* argc <= 1 is refuted: the line is `cat f` *)
      iIntros "%Hle". exfalso.
      rewrite /UShCat.cat_args echo_args_length in Hle. lia. }
    iIntros "_".
    replace (length (UShCat.cat_args W) - 1)%nat with 1%nat
      by (rewrite /UShCat.cat_args echo_args_length; lia).
    cbn [UkCatMain.kcat_pay].
    iExists ga, (ukn_pay N' (-1)). iSplitR; [ by iPureIntro | ].
    iSplitL "Hc"; last first.
    { cbn [UkCatMain.kcat_pay]. by iIntros "$". }
    (* ---- THE OPEN, AT THE ABSENT DEED, WITH THE CURSOR FRAMED ---- *)
    rewrite /UkCatMain.kcat_file.
    iApply (UkCat.kcat_o_mono N' (mword_of_int (UserHeap.ua_ptr ga)) _ _ _
              with "[] [Hc]"); last first.
    { iApply (kcat_o_frame N' (mword_of_int (UserHeap.ua_ptr ga)) _ _ _
                with "Hc").
      iApply (UkCatDeed.kcat_o_of_deed_miss N'
                (take NSTD (uvis_fd W)) c r q (uvis_cwd W)
                (base.filter
                   (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W)))
                   (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)))
                (mword_of_int (UserHeap.ua_ptr ga)) FsImgCheck.fname_f
                Heq
                ltac:(intros M Hsubm; exact (Hpath M Hsubm ga Hga))
                cat_fname_elems
                ltac:(rewrite cat_fname_start; exact Hcw)
                with "Hcode HA Hinv"). }
    iIntros (ret) "[[Hcwf Harm] [Hc HF]]".
    iSplit.
    - (* ---- THE DIAGNOSTIC ---- *)
      iIntros "_".
      iAssert (UserFd.ustd (ukn_fd N') (take NSTD (uvis_fd W))
               ∗ (fdq r q None ∨ file_taint c))%I
        with "[Harm]" as "[Hstd HD]".
      { iDestruct "Harm" as "[(_ & Hs & Hd) | [Hf #HT]]".
        - iFrame "Hs". by iLeft.
        - iSplitL; [ | by iRight ].
          iApply (UkFileOpen.uk_open_taint_fd_std (ukn_fd N')
                    (take NSTD (uvis_fd W)) ret Hnone with "Hf"). }
      iApply (cat_dg_open_absent g Hcons N' v vf ps0 cs0 s0 I0 P
                (take NSTD (uvis_fd W)) rb ga s Hst Htie Hs Hl2 Hglen
                ltac:(rewrite (Hgb 0%nat ltac:(lia)); vm_compute; reflexivity)
                with "Hpin Hfp [HD HF] Hstd Hc").
      iIntros "[_ Hc]". rewrite Hpayeq.
      iDestruct "HD" as "[Hd | #HT]";
        [ iApply ("Hend" with "Hc Hd HF") | iApply ("Hqt" with "HT") ].
    - (* ---- THE OPEN SUCCEEDED: only the taint can say so ---- *)
      iIntros "%Hpos".
      iDestruct "Harm" as "[(%Hm1 & _ & _) | [Hf #HT]]".
      { exfalso. rewrite Hm1 in Hpos. vm_compute in Hpos. lia. }
      iDestruct ("Htaint" $! N' with "[%]") as "Ht'"; [ exact Hpayeq | ].
      rewrite Hpayeq.
      iApply ("Ht'" $! ret with "HT Hf [%]"). exact Hpos.
  Qed.

  (* =================================================================== *)
  (*  9.  cat's PAYMENT AT THE CLAIM: THE PRESENT ARM (CAT-GEOM-2, 4).    *)
  (* =================================================================== *)

  (* the handle cat holds between turns -- [UShRound.cat_hold]'s shape,
     AT A MODE THE CALLER DOES NOT FIX.  [om] is a parameter here and
     everywhere below: never [OffParked], never [OffHeld] literally, so
     whatever shape lane OFF-LINK's publish lands on plugs in. *)
  Definition cat_hold_at (N' : uk_names Σ) (r : file_names) (q : Qp)
      (i : Z) (bs : list (bv 8)) (om : offmode)
      (fd : nat) (gamo : gname) (p : nat) : iProp Σ :=
    (UserFd.ufd (ukn_fd N') fd (FdOpen true false (FdInode i gamo om))
     ∗ UserOff.uoff gamo p ∗ fdq r q (Some (i, bs)))%I.

  (* ---- NAMED (lane OFF-LINK; SKELETON's [Hopen_hand]): THE OPEN'S fd
     ARM HANDS THE HELD ROW AND THE PROGRAM'S OWN HALF OF THE OFFSET AT
     ZERO.  [UkCatDeed.kcat_o_of_deed] hands [ualloc … (FdInode i γo
     OffParked)] and NO [UserOff.uoff]; [UserOff.off_pub_hand_0] (in
     [ProofSysOpenPub]) is the publish that splits the ghost and gives
     the program its half.  Everything else in this arm -- the ledger,
     the two fractions, the [-1] arm, the taint arm -- is
     [kcat_o_of_deed]'s post verbatim. ---- *)
  Definition cat_open_hand (N' : uk_names Σ) (c : file_fixed)
      (r : file_names) (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (l : list fdstate) (cwv : Z) (om : offmode) : iProp Σ :=
    (∀ (Img : gmap Z (bv 8)) (pv : mword 64),
       (* the path argument, as [UkCatDeed.kcat_o_of_deed] takes it: a
          PURE implication over every image the caller's own area is
          contained in ([UShCat.cat_kexec_argpath] supplies it) *)
       ⌜forall M : gmap Z (bv 8), uimg_sub Img M ->
          arg_path_of M pv FsImgCheck.fname_f⌝ -∗
       ⌜um_start_of cwv FsImgCheck.fname_f = FsImg.ROOTINO⌝ -∗
       ([∗ map] a ↦ b ∈ Img, ubyteq (ukn_d N') DfracDiscarded a b) -∗
       UkCat.kcat_o N' pv
      (UserFd.ustd (ukn_fd N') l
       ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
      (fun ret : mword 64 =>
         ((⌜ret = (mword_of_int (-1) : mword 64)⌝
           ∗ UserFd.ustd (ukn_fd N') l
           (* the failed open REFUNDS the deed (PROGRAM-STREAM stretch 9,
              item 3 (i)) *)
           ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
          ∨ (∃ (fd : nat) (gamo : gname),
               ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
                /\ (fd < NOFILE)%nat⌝
               ∗ UserFd.ustd (ukn_fd N') l
               ∗ cat_hold_at N' r q1 i bs om fd gamo 0%nat
               ∗ fdq r q2 (Some (i, bs)))
          ∨ (UkFileOpen.uk_open_taint_fd (ukn_fd N') l ret
             ∗ file_taint c))%I))%I.

  (* ---- DISCHARGED (kernel stream, item 1): the open's hand-mode deed
     corollary IS [cat_open_hand], at [UkCatDeed.kcat_o_of_deed]'s own
     statement with [omo := OffHeld].  Two things bridge, and both are
     arithmetic rather than content:

       * [UserFd.ualloc] at a ledger with NO free slot is
         [ustd l ∗ ⌜NSTD <= fd⌝ ∗ ufd fd st] ([ualloc_hi]), which is
         [cat_hold_at]'s first conjunct beside the ledger the arm hands
         back;
       * the publish's handed half at mode HAND is [UserOff.uoff γo 0]
         ([UserOff.foff_pub_of_held]), which is [cat_hold_at]'s second.

     The working directory is the ONE resource [cat_open_hand] does not
     name and the deed leaf does: it goes in here and is not reported,
     because cat never reads it again. ---- *)
  Lemma cat_open_hand_of_deed (N' : uk_names Σ) (c : file_fixed)
      (r : file_names) (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (l : list fdstate) (cwv : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    path_elems FsImgCheck.fname_f = [FsImgCheck.fname_f] ->
    fd_lowest_closed l = None ->
    UCodeCat.cat_code (ukn_t N') -∗
    app_inv fsc_fs -∗
    UserCwd.ucwd (ukn_cwd N') cwv -∗
    cat_open_hand N' c r q1 q2 i bs l cwv OffHeld.
  Proof using .
    intros Heq Hel Hno. iIntros "#Hcode #Hinv Hcwd".
    rewrite /cat_open_hand. iIntros (Img pv) "%Hpath %Hst #Hdi".
    iPoseProof (UkCatDeed.kcat_o_of_deed N' OffHeld l c r q1 q2 i bs cwv Img pv
                  FsImgCheck.fname_f Heq Hpath Hel Hst
                  with "Hcode Hdi Hinv") as "Hleaf".
    rewrite /UkCat.kcat_o.
    iIntros (h m avail) "%Ha0 %Ha1 #Hcode2 (Hstd & Hq1 & Hq2) Hrun Hcont".
    iApply ("Hleaf" $! h m avail with "[%] [%] Hcode2 [Hstd Hcwd Hq1 Hq2] Hrun");
      [ exact Ha0 | exact Ha1 | | ].
    { rewrite /UkCatDeed.kcat_open_hold. iFrame "Hstd Hcwd Hq1 Hq2". }
    iIntros (h' ret) "Hans Hrun".
    iApply ("Hcont" $! h' ret with "[Hans] Hrun").
    iDestruct "Hans" as "[_ [Hm1 | [Hfd | Ht]]]".
    - iLeft. iExact "Hm1".
    - iRight. iLeft.
      iDestruct "Hfd" as (fd γo) "(%Hb & Hal & Hpub & Hqa & Hqb)".
      iExists fd, γo. iSplitR; [by iPureIntro |].
      iDestruct (UserFd.ualloc_hi (ukn_fd N') l fd _ Hno with "Hal")
        as "(_ & Hstd & Hufd)".
      iFrame "Hstd Hqb". rewrite /cat_hold_at. iFrame "Hufd Hqa".
      iApply (UserOff.foff_pub_of_held with "Hpub").
    - iRight. iRight. iExact "Ht".
  Qed.

  (* ---- DISCHARGED (kernel stream, item 2): the held read IS
     [UkCatDeed.kcat_r_of_deed_held] at [cat_hold_at]'s own three conjuncts,
     which are [kcat_deed_hold_held]'s letter for letter at [wb := false].
     Everything the leaf needs is persistent, so the [□] costs nothing. ---- *)
  Lemma cat_held_read_of_deed (N' : uk_names Σ) (c : file_fixed)
      (r : file_names) (q1 : Qp) (i : Z) (bs : list (bv 8))
      (fd : nat) (gamo : gname) (jc : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (fd < NOFILE)%nat ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    UCodeCat.cat_code (ukn_t N') -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    cat_held_read N' (cat_hold_at N' r q1 i bs OffHeld fd gamo) c fd bs.
  Proof using .
    intros Heq Hfdlt. iIntros "#Hbr #Hrb #Hcode #Hm #Hinv".
    rewrite /cat_held_read. iModIntro. iIntros (p) "%Hple".
    iApply (UkCat.kcat_r_mono_out with "[] [-]"); last first.
    { iApply (UkCatDeed.kcat_r_of_deed_held N' CatSyms.buf 512%nat fd false i
                gamo c r q1 jc bs p Heq
                ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                Hfdlt with "Hbr Hrb Hcode Hm Hinv"). }
    iIntros (ret gb) "[%Hbnd [(%Hc & %Hby & Hh) | [Hh #HT]]]".
    - iSplitR; [ by iPureIntro | ]. iLeft.
      iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      rewrite /UkCatDeed.kcat_deed_hold_held /cat_hold_at.
      iDestruct "Hh" as "(H1 & H2 & H3)". iFrame "H1 H2 H3".
    - iSplitR; [ by iPureIntro | ]. iRight.
      iSplitL "Hh"; [| iExact "HT" ]. iExists p.
      iSplitR; [ by iPureIntro | ].
      rewrite /UkCatDeed.kcat_deed_hold_held /cat_hold_at.
      iDestruct "Hh" as "(H1 & H2 & H3)". iFrame "H1 H2 H3".
  Qed.

  Lemma cat_pay_present (W : uvis) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (c : file_fixed) (r : file_names) (q1 q2 : Qp) (i : Z)
      (bs : list (bv 8)) (om : offmode) (rb rb2 : bool) (Q : Z -> iProp Σ)
      (F : iProp Σ) :
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 (Some (i, bs)) ->
    uvis_cwd W = FsImg.ROOTINO ->
    take NSTD (uvis_fd W) !! 1%nat
      = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    take NSTD (uvis_fd W) !! 2%nat
      = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed (take NSTD (uvis_fd W)) = None ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (* ---- OFF-LINK item 1.  THE ROW IS OWED AT CAT'S OWN CWD: the deed
       open resolves a relative path, [cat_open_hand_of_deed] spends the
       process's [ucwd], and that resource is the PAYER's (it arrives
       inside [cat_pay_at]) -- a lender cannot hold it for every record. *)
    (∀ N' : uk_names Σ,
       UCodeCat.cat_code (ukn_t N') -∗
       UserCwd.ucwd (ukn_cwd N') (uvis_cwd W) -∗
       cat_open_hand N' c r q1 q2 i bs (take NSTD (uvis_fd W))
         (uvis_cwd W) om) -∗
    (* ---- OFF-LINK item 2: the HELD read at the pinned offset.  Its
       count bound is already in [cat_held_read]'s post (landed above),
       which is what makes [cat_hw_of_link] discharge [Hw] outright. ---- *)
    (∀ (N' : uk_names Σ) (fd : nat) (gamo : gname),
       UCodeCat.cat_code (ukn_t N') -∗
       ⌜(fd < NOFILE)%nat⌝ -∗
       cat_held_read N' (cat_hold_at N' r q1 i bs om fd gamo) c fd bs) -∗
    (* THE EXIT PAYLOAD, AT CAT'S OWN END CURSOR (lane CAT-GEOM-3).  It
       used to be [∀ p ≤ length bs], because [cat_round_at]'s [Cend] wand
       did not pin where the loop stopped; it does now, so this is
       [length bs] -- which is [UCatOut.cat_out_len] at a present deed
       ([UCatOut.cat_out_len_ran_some]) and hence exactly what
       [UCatOut.catq_filed] is.  The disjunct is the TAINT, where the
       cursor's own right arm funds the payload. *)
    □ (UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P (length bs)
       -∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)) -∗ F -∗
       Q (-1)) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    (* ...and at a PRESENT file the open may still fail: that arm files
       [RCNoOpen] and prints the same nineteen bytes. *)
    □ (UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCNoOpen) P 19%nat
       -∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)) -∗ F -∗
       Q (-1)) -∗
    (* ...AND THE TAINT'S DESCRIPTOR SUB-ARM, at the record the entry
       allocates AND at its payload equation -- a supplier needs to know
       what [ukn_pay N'] IS before it can produce anything at [Q (-1)]
       ([cat_taint_open_of_taint] discharges it). *)
    (∀ N' : uk_names Σ, ⌜ukn_pay N' = Q⌝ -∗
       cat_taint_open N' c (take NSTD (uvis_fd W)) (Q (-1))) -∗
    (* [F] IS A FRAME: whatever else the payer's parent is owed at the
       exit.  It rides beside the cursor across the open and inside the
       hold across the read loop, and the in-spec exits hand it to the
       payload wands; out of spec the payload needs none of it. *)
    cat_pay_at W Q
      (fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs))
       ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat ∗ F).
  Proof using Hcons.
    intros Hgc Hst Htie Hcw Hl1 Hl2 Hnone.
    iIntros "#Hpin #Hfp Hopen Hheld #Hqp #Hqt #Hqn #Htaint".
    rewrite /cat_pay_at.
    iIntros (N') "%Hpayeq %Hargc2 %Harg1 %Hpath Hstd Hcwf #Hcode #Hro
                  #Hargv #HA (Hd1 & Hd2 & Hc & HF)".
    destruct (lookup_lt_is_Some_2 (UShCat.cat_args W) 1%nat
                ltac:(rewrite /UShCat.cat_args echo_args_length; lia))
      as [ga Hga].
    destruct (Harg1 ga Hga) as [Hglen Hgb].
    assert (Hfb : UserHeap.ua_bytes ga 0%nat
                  = alt_catopen !!! UkCatMain.cm_msg_q)
      by (rewrite (Hgb 0%nat ltac:(lia)); vm_compute; reflexivity).
    iExists (UserFd.ustd (ukn_fd N') (take NSTD (uvis_fd W))
             ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))%I.
    iSplitR "Hstd Hd1 Hd2"; last first.
    { iFrame "Hstd Hd1 Hd2". }
    rewrite /UkCatMain.kcat_pay_all. iSplit.
    { iIntros "%Hle". exfalso.
      rewrite /UShCat.cat_args echo_args_length in Hle. lia. }
    iIntros "_".
    replace (length (UShCat.cat_args W) - 1)%nat with 1%nat
      by (rewrite /UShCat.cat_args echo_args_length; lia).
    cbn [UkCatMain.kcat_pay].
    iExists ga, (ukn_pay N' (-1)). iSplitR; [ by iPureIntro | ].
    iSplitL "Hopen Hheld Hc HF Hcwf"; last first.
    { cbn [UkCatMain.kcat_pay]. by iIntros "$". }
    rewrite /UkCatMain.kcat_file.
    iDestruct ("Hopen" $! N' with "Hcode Hcwf") as "Hopen".
    iCombine "Hc HF" as "Hc".
    iApply (UkCat.kcat_o_mono N' (mword_of_int (UserHeap.ua_ptr ga)) _ _ _
              with "[Hheld] [Hopen Hc]"); last first.
    { iApply (kcat_o_frame N' (mword_of_int (UserHeap.ua_ptr ga)) _ _ _
                with "Hc").
      iApply ("Hopen" $!
                (base.filter
                   (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W)))
                   (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)))
                (mword_of_int (UserHeap.ua_ptr ga))
                with "[%] [%] HA").
      - intros M Hsubm. exact (Hpath M Hsubm ga Hga).
      - rewrite cat_fname_start. exact Hcw. }
    iIntros (ret) "[Harm [Hc HF]]".
    iSplit.
    - (* ---- THE DIAGNOSTIC, AT [RCNoOpen] ---- *)
      iIntros "%Hneg".
      iAssert (UserFd.ustd (ukn_fd N') (take NSTD (uvis_fd W))
               ∗ ((fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
                  ∨ file_taint c))%I
        with "[Harm]" as "[Hstd HD]".
      { iDestruct "Harm" as "[(_ & Hs & Hd1 & Hd2) | [Hok | [Hf #HT]]]".
        - iFrame "Hs". iLeft. iFrame "Hd1 Hd2".
        - iDestruct "Hok" as (fd gamo) "(_ & Hs & Hh & Hd2)".
          iFrame "Hs". iLeft. rewrite /cat_hold_at.
          iDestruct "Hh" as "(_ & _ & Hd1)". iFrame "Hd1 Hd2".
        - iSplitL; [ | by iRight ].
          iApply (UkFileOpen.uk_open_taint_fd_std (ukn_fd N')
                    (take NSTD (uvis_fd W)) ret Hnone with "Hf"). }
      iApply (cat_dg_open_noopen g Hcons N' v vf ps0 cs0 s0 I0 P
                (take NSTD (uvis_fd W)) rb2 ga Hst Hl2 Hglen Hfb
                with "Hpin Hfp [HD HF] Hstd [Hc]").
      + iIntros "[_ Hc]". rewrite Hpayeq.
        iDestruct "HD" as "[Hd | #HT]";
          [ iApply ("Hqn" with "Hc Hd HF") | iApply ("Hqt" with "HT") ].
      + iApply (UCatOut.cch_0_alt g v vf ps0 cs0 s0 I0
                  (ralt_enc RCRan) (ralt_enc RCNoOpen) P). iExact "Hc".
    - (* ---- THE OPEN SUCCEEDED ---- *)
      iIntros "%Hpos".
      iDestruct "Harm" as "[[%Hm1 _] | [Hok | [Hf #HT]]]".
      { exfalso. rewrite Hm1 in Hpos. vm_compute in Hpos. lia. }
      + (* the fd arm: the ROUND, then the CLOSE *)
        iDestruct "Hok" as (fd gamo) "([%Hr1 %Hlt1] & Hstd & Hhold & Hd2)".
        iExists fd,
          (UserFd.ufd (ukn_fd N') fd (FdOpen true false (FdInode i gamo om))
           ∗ ukn_pay N' (-1))%I.
        iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
        iSplitR "".
        * rewrite /UkCatMain.kcat_run0.
          iExists (cat_round_inv g N'
                     (fun p : nat =>
                        (cat_hold_at N' r q1 i bs om fd gamo p ∗ F)%I)
                     (take NSTD (uvis_fd W)) bs v vf ps0 cs0 s0 I0 P),
                  (((UCatOut.cch g v vf ps0 cs0 s0 I0
                       (ralt_enc RCRan) P (length bs))
                    ∨ file_taint c)
                   ∗ (∃ p' : nat,
                        cat_hold_at N' r q1 i bs om fd gamo p' ∗ F))%I.
          iSplitR "Hstd Hhold Hc HF Hd2"; last iSplitL "Hstd Hhold Hc HF".
          -- iApply (cat_round_at g N' c i bs fd
                       (fun p : nat =>
                          (cat_hold_at N' r q1 i bs om fd gamo p ∗ F)%I)
                       (take NSTD (uvis_fd W)) v vf ps0 cs0 s0 I0 P _
                       Hgc Htie
                       with "[Hheld] [] [] Hcode").
             ++ iApply cat_held_read_frame.
                iApply ("Hheld" $! N' fd gamo with "Hcode [%]"). exact Hlt1.
             ++ iApply (cat_hw_of_link g Hcons N' c v vf ps0 cs0 s0 I0 P
                          (take NSTD (uvis_fd W)) rb Hgc Hst Hl1
                          with "Hpin Hfp").
             ++ iIntros "!>" (p p') "%Hp %Hp' Hex _ Hhold' Hc'".
                iSplitL "Hc' Hex"; last (iExists p'; iExact "Hhold'").
                iDestruct "Hex" as "[%Hpe | #HTc]"; last (by iRight).
                iLeft. rewrite <- (proj1 Hpe). iExact "Hc'".
          -- rewrite /cat_round_inv. iFrame "Hstd".
             iExists 0%nat. iSplitR; [ iPureIntro; lia | ].
             iFrame "Hhold Hc HF".
          -- iIntros "[Hcp Hhp]".
             iDestruct "Hcp" as "[Hc' | #HTc]"; last first.
             { iDestruct "Hhp" as (p') "[(Hufdh & _ & _) _]".
               iFrame "Hufdh". rewrite Hpayeq.
               iApply ("Hqt" with "HTc"). }
             iDestruct "Hhp" as (p') "[(Hufdh & _ & Hd1) HF]".
             iFrame "Hufdh". rewrite Hpayeq.
             iApply ("Hqp" with "Hc' [Hd1 Hd2] HF"). iFrame "Hd1 Hd2".
        * iApply (cat_cl_of_in N' fd
                    (FdOpen true false (FdInode i gamo om)) _ _
                    (fdst_nopipe_inode true false i gamo om)).
          by iIntros "[$ $]".
      + (* the taint's descriptor sub-arm, named *)
        iDestruct ("Htaint" $! N' with "[%]") as "Ht'"; [ exact Hpayeq | ].
        rewrite Hpayeq.
        iApply ("Ht'" $! ret with "HT Hf [%]"). exact Hpos.
  Qed.

  (* =================================================================== *)
  (*  10.  WHAT SH-ROUND APPLIES FOR THE cat CHILD (lane CAT-GEOM-3).     *)
  (*                                                                     *)
  (*  The payload is [UCatOut.catq_filed] AT CAT'S OWN END CURSOR, which  *)
  (*  is what item (1) made instantiable: [UCatOut.cat_out_len] is        *)
  (*  [length bs] at a PRESENT deed and NINETEEN at an ABSENT one, and    *)
  (*  those are exactly the two payload wands [cat_pay_present] and       *)
  (*  [cat_pay_absent] ask for now that [cat_round_at]'s [Cend] pins      *)
  (*  where the loop stopped.  Both wands are DISCHARGED here, so what    *)
  (*  is left of cat's payment is the two rows lane OFF-LINK-4 owes and   *)
  (*  the taint's descriptor sub-arm.                                     *)
  (* =================================================================== *)
  (* THE PAYLOAD SH IS OWED, as a DISJUNCTION of the two alternatives
     cat's round can file.  [UCatOut]'s header says it in words already:
     an ABSENT deed and a CONTENT round file [RCRan], a PRESENT file
     whose open returned [-1] files [RCNoOpen], and WHICH ONE is read off
     the deed -- which the entry cannot know, because the open's own
     return decides it.  So what crosses the exit is "one of the two",
     and both disjuncts are [UCatOut.catq_filed] at CAT'S OWN END CURSOR
     ([UCatOut.cat_out_len]: [length bs] at [RCRan] with a present deed,
     NINETEEN at [RCRan] with an absent one and at [RCNoOpen] always). *)
  (* ...AND IT RETURNS WHAT SH LENT (RULING CAT-DEED, amended 2026-09-21):
     ONE fraction of `f`'s ghost state goes in ([cat_lend]) and THE SAME
     fraction, at the same value, comes out -- cat only reads -- or the
     application is out of spec.  The split the open needs (one piece on
     the path walk, one on the final observation) is cat's own business
     and does not show here. *)
  Definition catq_cat (c : file_fixed) (r : file_names) (q : Qp) (s : dst)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
    : Z -> iProp Σ :=
    fun _ =>
      ((UCatOut.catq_filed g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P (-1)
        ∨ UCatOut.catq_filed g v vf ps0 cs0 s0 I0 (ralt_enc RCNoOpen) P (-1))
       ∗ (fdq r q s ∨ file_taint c))%I.

  Lemma catq_cat_const (c : file_fixed) (r : file_names) (q : Qp) (s : dst)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (x y : Z) :
    catq_cat c r q s v vf ps0 cs0 s0 I0 P x
    = catq_cat c r q s v vf ps0 cs0 s0 I0 P y.
  Proof using . reflexivity. Qed.

  (* a payer at a smaller payment pays a larger one that contains it *)
  Lemma cat_pay_at_mono (W : uvis) (Q : Z -> iProp Σ) (Pay Pay' : iProp Σ) :
    (Pay' -∗ Pay) -∗ cat_pay_at W Q Pay -∗ cat_pay_at W Q Pay'.
  Proof using .
    iIntros "Hw Hf". rewrite /cat_pay_at.
    iIntros (N) "%H1 %H2 %H3 %H4 Hstd Hcwf #Hcode #Hro #Hargv #HA HPay".
    iApply ("Hf" $! N with "[%] [%] [%] [%] Hstd Hcwf Hcode Hro Hargv
                           HA [Hw HPay]");
      [ exact H1 | exact H2 | exact H3 | exact H4 | ].
    iApply ("Hw" with "HPay").
  Qed.

  Lemma cat_pay_filed_some (W : uvis) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (i : Z)
      (bs : list (bv 8)) (rb rb2 : bool) (jc : Z) (Q : Z -> iProp Σ)
      (F : iProp Σ) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 (Some (i, bs)) ->
    uvis_cwd W = FsImg.ROOTINO ->
    take NSTD (uvis_fd W) !! 1%nat
      = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    take NSTD (uvis_fd W) !! 2%nat
      = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed (take NSTD (uvis_fd W)) = None ->
    (* THE PAYLOAD IS THE FORK'S, not cat's: a generation's payload is
       what its parent chose ([ChildTok.my_pay_agree] makes the entry's
       [Q] slot rigid), so cat states what it produces ([catq_cat]) and the
       caller says how that pays [Q]. *)
    □ (catq_cat c r q (Some (i, bs)) v vf ps0 cs0 s0 I0 P (-1) -∗ F -∗
       Q (-1)) -∗
    (* ...and out of spec the payload is built from the flag alone: the
       frame has crossed the entry, but an out-of-spec exit does not hold
       it (it went into a syscall whose out-of-spec disjunct returns
       nothing), so this cannot be the wand above at [F]. *)
    □ (file_taint c -∗ Q (-1)) -∗
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (∀ N' : uk_names Σ, ⌜ukn_pay N' = Q⌝ -∗
       cat_taint_open N' c (take NSTD (uvis_fd W)) (Q (-1))) -∗
    (* WHAT IS LENT IS ONE FRACTION AND THE CURSOR.  The open's and the
       read's laws are cat's OWN ([cat_open_hand_of_deed] at the process's
       cwd, [cat_held_read_of_deed]), at the two halves the fraction is
       split into. *)
    cat_pay_at W Q
      (fdq r q (Some (i, bs))
       ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat ∗ F).
  Proof using Hcons.
    intros Heq Hgc Hst Htie Hcw Hl1 Hl2 Hnone.
    iIntros "#HQ #HQt #Hbr #Hrb #Hmade #Hinv #Hpin #Hfp #Htaint".
    iApply (cat_pay_at_mono W _
              (fdq r (q / 2) (Some (i, bs)) ∗ fdq r (q / 2) (Some (i, bs))
               ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat
               ∗ F)%I
              with "[]").
    { (* THE SPLIT: the open's two pieces each carry a half *)
      iIntros "[Hd Hc]". iFrame "Hc".
      iApply (fdq_split r (q / 2) (q / 2) (Some (i, bs))).
      rewrite Qp.div_2. iExact "Hd". }
    iAssert (□ (fdq r (q / 2) (Some (i, bs)) ∗ fdq r (q / 2) (Some (i, bs))
                -∗ fdq r q (Some (i, bs))))%I as "#Hjoin".
    { iIntros "!> [Hd1 Hd2]".
      iDestruct (fdq_join r (q / 2) (q / 2) with "Hd1 Hd2") as "Hd".
      rewrite Qp.div_2. iExact "Hd". }
    iApply (cat_pay_present W v vf ps0 cs0 s0 I0 P c r (q / 2)%Qp (q / 2)%Qp
              i bs OffHeld rb rb2 _ F
              Hgc Hst Htie Hcw Hl1 Hl2 Hnone
              with "Hpin Hfp [] [] [] [] [] Htaint").
    - (* the open's law, at cat's own cwd *)
      iIntros (N') "#Hcode Hcwf".
      iApply (cat_open_hand_of_deed N' c r (q / 2)%Qp (q / 2)%Qp i bs
                (take NSTD (uvis_fd W)) (uvis_cwd W) Heq cat_fname_elems
                Hnone with "Hcode Hinv Hcwf").
    - (* the held read's law *)
      iIntros (N' fd gamo) "#Hcode %Hlt".
      iApply (cat_held_read_of_deed N' c r (q / 2)%Qp i bs fd gamo jc Heq
                Hlt with "Hbr Hrb Hcode Hmade Hinv").
    - (* the content arm: [cat_out_len] IS [length bs] *)
      iIntros "!> Hc Hd HF". iApply ("HQ" with "[Hc Hd] HF").
      rewrite /catq_cat /UCatOut.catq_filed
              (UCatOut.cat_out_len_ran_some cs0 s0 I0 (Some (i, bs)) i bs
                 Htie eq_refl).
      iSplitL "Hc"; [ by iLeft | ].
      iLeft. iApply ("Hjoin" with "Hd").
    - (* out of spec *)
      iExact "HQt".
    - (* a PRESENT file whose open FAILED files [RCNoOpen], nineteen bytes *)
      iIntros "!> Hc Hd HF". iApply ("HQ" with "[Hc Hd] HF").
      rewrite /catq_cat /UCatOut.catq_filed.
      rewrite (UCatOut.cat_out_len_noopen cs0 s0 I0).
      iSplitL "Hc"; [ by iRight | ].
      iLeft. iApply ("Hjoin" with "Hd").
  Qed.

  Lemma cat_pay_filed_none (W : uvis) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (rb : bool)
      (Q : Z -> iProp Σ) (F : iProp Σ) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 None ->
    uvis_cwd W = FsImg.ROOTINO ->
    take NSTD (uvis_fd W) !! 2%nat
      = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    fd_lowest_closed (take NSTD (uvis_fd W)) = None ->
    □ (catq_cat c r q None v vf ps0 cs0 s0 I0 P (-1) -∗ F -∗ Q (-1)) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    (∀ N' : uk_names Σ, ⌜ukn_pay N' = Q⌝ -∗
       cat_taint_open N' c (take NSTD (uvis_fd W)) (Q (-1))) -∗
    cat_pay_at W Q
      (fdq r q None
       ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat ∗ F).
  Proof using Hcons.
    intros Heq Hgc Hst Htie Hcw Hl2 Hnone.
    iIntros "#HQ #HQt #Hinv #Hpin #Hfp #Htaint".
    iApply (cat_pay_absent W v vf ps0 cs0 s0 I0 P c r q rb _ None F
              Heq Hgc Hst Htie eq_refl Hcw Hl2 Hnone
              with "Hinv Hpin Hfp [] HQt Htaint").
    iIntros "!> Hc Hd HF". iApply ("HQ" with "[Hc Hd] HF").
    rewrite /catq_cat /UCatOut.catq_filed
            (UCatOut.cat_out_len_ran_none cs0 s0 I0 None Htie eq_refl).
    iSplitL "Hc"; [ by iLeft | by iLeft ].
  Qed.

  (* =================================================================== *)
  (*  11.  THE ONE NAME SH-ROUND APPLIES (lane CAT-GEOM-4).               *)
  (*                                                                     *)
  (*  [ExecEntry.image_entry] is [□]-quantified over the key, so a        *)
  (*  payment premise cannot HOLD linear resources.  They travel in       *)
  (*  [Pay], which [image_entry_at] hands over per invocation -- exactly  *)
  (*  the way echo's credential travels ([UShEchoPay]).  [cat_lend] is    *)
  (*  cat's: the two rows lane OFF-LINK-4 owes, the deed's two fractions  *)
  (*  and the era's cursor at the round's own start.                      *)
  (* =================================================================== *)
  (* WHAT SH LENDS cat (RULING CAT-DEED, amended 2026-09-21): ONE fraction
     of `f`'s ghost state, at whatever state `f` is in, and the era's
     console cursor at the round's own start.  Nothing else: the laws cat's
     open and read run on are cat's own. *)
  Definition cat_lend (r : file_names) (q : Qp) (s : dst)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
    : iProp Σ :=
    (fdq r q s
     ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat)%I.

  (* ...and the payment FRAMES its lend: a payer that needs a resource
     only inside the walk takes it off [Pay] when the entry hands it
     over. *)
  Lemma cat_pay_at_lend (W : uvis) (Q : Z -> iProp Σ) (R Pay : iProp Σ) :
    (R -∗ cat_pay_at W Q Pay) -∗ cat_pay_at W Q (R ∗ Pay).
  Proof using .
    iIntros "Hf". rewrite /cat_pay_at.
    iIntros (N) "%H1 %H2 %H3 %H4 Hstd Hcwf #Hcode #Hro #Hargv #HA [HR HPay]".
    iDestruct ("Hf" with "HR") as "Hf'".
    iApply ("Hf'" $! N with "[%] [%] [%] [%] Hstd Hcwf Hcode Hro Hargv
                              HA HPay");
      [ exact H1 | exact H2 | exact H3 | exact H4 ].
  Qed.

  (* THE ONE NAME SH APPLIES, at either state of `f`. *)
  Lemma cat_child_of_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (v : era_pins) (vf : file_era) (ps0 cs0 : list nat) (s0 : fstate)
      (I0 : list (bv 8)) (P : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (s : dst)
      (rb rb2 : bool) (jc : Z) (Q : Z -> iProp Σ) (F : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 s ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = 1%nat ->
    (forall j : nat, (j < 1)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed (take NSTD sts) = None ->
    (* the machine's credential and the application's flag are one fact --
       as a CONVERSION, not the flag itself, which had made this entry an
       out-of-spec statement only *)
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    (* what cat produces, AND THE FRAME, pay the payload the fork chose
       (the fork's payload is the parent's whole credential; cat is lent,
       and returns, one fraction of it -- the rest is [F]) *)
    □ (catq_cat c r q s v vf ps0 cs0 s0 I0 P (-1) -∗ F -∗ Q (-1)) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q
      (cat_lend r q s v vf ps0 cs0 s0 I0 P ∗ F) uslot.
  Proof using Hcons ufdG0.
    intros HQc Heq Hgc Hst Htie Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname
           Hcw Hl1 Hl2 Hnone.
    iIntros "#Hbr #Hkc #HQ #HQt #Hmade #Hinv #Hpin #Hfp #Hnpw #Hdep".
    iApply (cat_image_entry ws Mn sv t gn sts cw cs pidv _ _ HQc
              Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname
              with "[] Hnpw Hdep").
    iIntros "!>" (W') "%Hfdw %Hcww".
    iAssert (∀ N' : uk_names Σ, ⌜ukn_pay N' = Q⌝ -∗
               cat_taint_open N' c (take NSTD (uvis_fd W')) (Q (-1)))%I
      as "#Htaint".
    { iIntros (N') "%Hpq". rewrite Hfdw.
      iApply (cat_taint_open_of_taint N' c r (take NSTD sts) (Q (-1))
                Heq Hnone with "HQt [] Hkc").
      rewrite Hpq. iExact "HQt". }
    rewrite /cat_lend.
    iApply (cat_pay_at_mono W' Q
              (fdq r q s
               ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat
               ∗ F)%I _ with "[]").
    { iIntros "[[Hd Hc] HF]". iFrame "Hd Hc HF". }
    destruct s as [[i bs] |].
    - iApply (cat_pay_filed_some W' v vf ps0 cs0 s0 I0 P c r q i bs rb rb2 jc Q F
                Heq Hgc Hst Htie
                ltac:(rewrite Hcww; exact Hcw)
                ltac:(rewrite Hfdw; exact Hl1)
                ltac:(rewrite Hfdw; exact Hl2)
                ltac:(rewrite Hfdw; exact Hnone)
                with "HQ HQt Hbr Hkc Hmade Hinv Hpin Hfp Htaint").
    - iApply (cat_pay_filed_none W' v vf ps0 cs0 s0 I0 P c r q rb2 Q F
                Heq Hgc Hst Htie
                ltac:(rewrite Hcww; exact Hcw)
                ltac:(rewrite Hfdw; exact Hl2)
                ltac:(rewrite Hfdw; exact Hnone)
                with "HQ HQt Hinv Hpin Hfp Htaint").
  Qed.

End UCatEntry.
