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
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UCodeCat.
Require User.CatSyms User.CatInstrs.
Require Import ChildTok.
Require Import FdSlots PipeNames ProcGeom UserFd UserCwd.
Require Import UexecSG UexecSlot UexecRet UsysMemOk.
Require Import UexecExecInst.  (* THE INSTANCES: [uexecSG_xv6], [uprogSG_gen] *)
Require Import UkCat.
Require Import UkCatCat.
Require Import UkFileOpen.
Require Import UkCatDeed.
Require Import AppCfg AppInv AppFile FileOpen FsCfg FsImgCheck.
Require Import ConsoleInv.
Require Import SysReadDefs.     (* [ard_count] *)
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs BioDefs.
Require Import LineWords EchoDisc ConsLog EchoOutPure.
Require Import FileState FileDisc FileOutPure FileOut FileLinks.
Require Import EchoOut AppEcho.
Require Import UCatOut.
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
Lemma cat_round_line (cs0 : list nat) (s0 : fst) (I0 : list (bv 8))
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
      (ps0 cs0 : list nat) (s0 : fst) (I0 : list (bv 8)) (P : nat) : iProp Σ :=
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
         ((⌜Z.to_nat (bv_unsigned rv) = ard_count 512 off0 (length bs)⌝
           ∗ ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                gb j = bs !!! (off0 + j)%nat⌝
           ∗ UkCatDeed.kcat_deed_hold N fd wb i γo r q bs)
          ∨ ((∃ p' : nat, ⌜(p' <= length bs)%nat⌝
                          ∗ UkCatDeed.kcat_deed_hold N fd wb i γo r q bs)
             ∗ file_taint c))%I).
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
    iIntros (rv gb) "[Hhold [[%Hc1 %Hc2] | #HT]]".
    - iLeft. iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hhold".
    - iRight. iFrame "HT". iExists off0.
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
  Lemma cat_round_at (c : file_fixed) (i : Z) (bs : list (bv 8)) (fd : nat)
      (Hold : nat -> iProp Σ) (l : list fdstate)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fst) (I0 : list (bv 8)) (P : nat)
      (Cend : iProp Σ) :
    c = fgn_cl g ->
    cat_tie cs0 s0 I0 (Some (i, bs)) ->
    (* [Hpin]: the offset-pinned read, at a handle that is itself at [p] *)
    □ (∀ p : nat, ⌜(p <= length bs)%nat⌝ -∗
         UkCat.kcat_r N (mword_of_int (Z.of_nat fd)) CatSyms.buf 512%nat
           (Hold p)
           (fun (rv : mword 64) (gb : nat -> bv 8) =>
              ((⌜Z.to_nat (bv_unsigned rv) = ard_count 512 p (length bs)⌝
                ∗ ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                     gb j = bs !!! (p + j)%nat⌝
                ∗ Hold (p + Z.to_nat (bv_unsigned rv))%nat)
               ∨ ((∃ p' : nat, ⌜(p' <= length bs)%nat⌝ ∗ Hold p')
                  ∗ file_taint c))%I)) -∗
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
               ∗ ubytes γd CatSyms.buf 512 fbb))) -∗
    (* the read-error tail, and the loop's normal exit.  [Cend]'s wand
       takes the cursor and the handle's position SEPARATELY: the loop
       exits on [read] returning zero, and it is the ENTRY -- which owns
       the arithmetic of [ard_count] -- that reads off that the two are
       then the same. *)
    □ UkCatCat.kcat_dg_cr N -∗
    □ (∀ p p' : nat, ⌜(p <= length bs)%nat⌝ -∗ ⌜(p' <= length bs)%nat⌝ -∗
         UserFd.ustd γfd l -∗ Hold p' -∗
         UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P p -∗ Cend) -∗
    cat_code γt -∗
    UkCatCat.kcat_round N (mword_of_int (Z.of_nat fd))
      (cat_round_inv Hold l bs v vf ps0 cs0 s0 I0 P) Cend.
  Proof using .
    intros Hgc Htie.
    iIntros "#Hpin #Hw #Hdcr #Hend #Hcode".
    rewrite /UkCatCat.kcat_round. iModIntro.
    iIntros (h m avail f) "%Ha0 %Ha1 %Ha2 _ HI Hbuf Hrun Hcont".
    iDestruct "HI" as "[Hstd Hcur]".
    iDestruct "Hcur" as (p) "(%Hple & Hhold & Hc)".
    (* THE READ, at the cursor's OWN offset *)
    iDestruct ("Hpin" $! p with "[%]") as "Hr"; [ exact Hple | ].
    iApply ("Hr" $! h m avail f with "[%] [%] [%] Hcode Hhold Hbuf Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret gb) "Hro Hbuf Hrun".
    iApply ("Hcont" $! h' ret gb with "[Hstd Hc Hro] Hbuf Hrun").
    iDestruct "Hro" as "[(%Hcnt & %Hbyt & Hhold) | [Hhold #HT]]"; last first.
    { (* THE TAINT: the cursor's own right disjunct funds every arm *)
      iDestruct "Hhold" as (p2) "[%Hp2 Hhold]".
      iSplit; [| iSplit ].
      - iIntros "_". iExact "Hdcr".
      - iIntros "_".
        iApply ("Hend" $! p p2 with "[%] [%] Hstd Hhold Hc");
          [ exact Hple | exact Hp2 ].
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
        iRight. iExact "HT". }
    (* THE CONTENT ARM *)
    assert (Hnble : (Z.to_nat (bv_unsigned ret) <= 512)%nat)
      by (rewrite Hcnt; apply ard_count_le).
    assert (Hnext : (p + Z.to_nat (bv_unsigned ret) <= length bs)%nat)
      by exact (cat_round_cursor bs p (Z.to_nat (bv_unsigned ret))
                  Hple Hcnt).
    iSplit; [| iSplit ].
    - (* [cat: read error] is VACUOUS at a deed: the count that came back
         is an [ard_count], which is not negative (lane READ-RELAY) *)
      iIntros "_". iExact "Hdcr".
    - iIntros "_".
      iApply ("Hend" $! p (p + Z.to_nat (bv_unsigned ret))%nat
                with "[%] [%] Hstd Hhold Hc");
        [ exact Hple | exact Hnext ].
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

End UCatKernel.
