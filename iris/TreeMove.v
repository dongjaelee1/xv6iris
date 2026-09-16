(* ===================================================================== *)
(* TreeMove.v -- THE OWNER'S MOVE AT THE FIRE (lane TL-3W).               *)
(*                                                                       *)
(* design/user-tree.md section 7.2, at the write-kind fires.  [AppTree.v] *)
(* landed the two halves of the move -- the update-free STEP              *)
(* ([tree_step_move_*]) and the RESYNC ([tree_resync]) -- as facts about  *)
(* the claim alone; this file joins them into the shape a two-phase       *)
(* commit takes, so that an OWNER can supply a write-kind AU out of its   *)
(* DEED and get the MOVED DEED back inside the commit's own receipt.      *)
(*                                                                       *)
(*   phase 1   opens [AppInv.app_inv], agrees the map the kernel lent,    *)
(*             reads its own subtree off the claim, DECIDES whether the   *)
(*             move is visible in its tree, and hands the fire an         *)
(*             [AppInv.app_step] -- the free one if not, the parking one  *)
(*             if so (the deed and a fresh token go in);                  *)
(*   phase 2   runs after the mover with [I'] and                         *)
(*             [abs_view I' = δ (abs_view I)] in hand, opens the claim    *)
(*             again, REFUTES the exact arm by TL-1's INSIDE lemma, and   *)
(*             resyncs the entry -- returning the deed AT THE MOVED TREE. *)
(*                                                                       *)
(* WHAT IS HERE: the WRITE chain ([tree_awrite_chain]), which is the one  *)
(* write-kind member whose U-tier leaf can carry the receipt home         *)
(* ([UkTreeWrite.v]).  WHAT IS NOT, AND EXACTLY WHY: section 4.           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.       (* [bioslotG] *)
Require Import Xv6G.             (* [xv6G] *)
Require Import FdSlots.          (* [fdslotG] *)
Require Import IrefSlots.        (* [irefslotG] *)
Require Import ProcAvail.        (* [pavG] *)
Require Import FileInvDefs.      (* [fileG], and its [appcfg] field [file_app] *)
Require Import FsTree.           (* [fname] *)
Require Import FsBlocks.         (* [fs_names], [blk_splice] *)
Require Import FsBytesGamma.     (* [fs_gamma_L] *)
Require Import OffGv.            (* [off_gv] *)
Require Import AppCfg.           (* [app_pred] / [app_run] / [MkAppcfg] *)
Require Import AppInv.           (* [app_inv], [app_body], [app_step], [appE] *)
Require Import SysWriteDefs.     (* [wri_pre], [wchunks] *)
Require Import FsAbsWriteFire.   (* [awrite_full_at] / [awrite_part_at] / chain *)
Require Import TreeView.         (* TL-1 *)
Require Import AppTree.          (* TL-2 + TL-3W: the claim, the deed, the move *)
Require Import TreeObs.          (* the claim law at the era's record *)
Require Import FsAbs.            (* [γtop] (FsAbs's own rule: LAST but one) *)
Require Import FsAbsDefs.        (* [aview] / [anode] / [arow_at] *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  WHAT A RUN OF WRITES DOES TO AN OWNER'S TREE (pure)               *)
(*                                                                       *)
(*  The kernel picks the offset and the bytes of every chunk, so an owner *)
(*  cannot name the tree it will end with.  What it CAN name, and what    *)
(*  the chain's cursor carries, is the RELATION: the same subtree, the    *)
(*  same nodes, and only the file it is writing has moved.                *)
(* ===================================================================== *)

Definition twrote (i : Z) (t t' : ttree) : Prop :=
  tv_root t' = tv_root t
  /\ (forall j : Z, j <> i -> tv_nodes t' !! j = tv_nodes t !! j)
  /\ (exists bs bs' : list (bv 8),
        tv_nodes t !! i = Some (AFile bs) /\ tv_nodes t' !! i = Some (AFile bs')).

Lemma twrote_refl (i : Z) (t : ttree) (bs : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs) -> twrote i t t.
Proof. intros H. split_and!; [done | done |]. by exists bs, bs. Qed.

Lemma twrote_trans (i : Z) (t t' t'' : ttree) :
  twrote i t t' -> twrote i t' t'' -> twrote i t t''.
Proof.
  intros (H1 & H2 & (b1 & b1' & Hb1 & Hb1')) (K1 & K2 & (b2 & b2' & Hb2 & Hb2')).
  split_and!.
  - by rewrite K1 H1.
  - intros j Hj. by rewrite (K2 j Hj) (H2 j Hj).
  - exists b1, b2'. split; [exact Hb1 | exact Hb2'].
Qed.

Lemma twrote_file (i : Z) (t t' : ttree) :
  twrote i t t' -> exists bs' : list (bv 8), tv_nodes t' !! i = Some (AFile bs').
Proof. intros (_ & _ & (b & b' & _ & H')). by exists b'. Qed.

(* ...and the step of the relation the write leg makes *)
Lemma twrote_write (i : Z) (t : ttree) (off : nat) (new bs : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs) -> twrote i t (top_write i off new t).
Proof.
  intros H. split_and!.
  - by rewrite /top_write /=.
  - intros j Hj. rewrite /top_write /= H.
    apply lookup_insert_ne. congruence.
  - exists bs, (blk_splice off new bs). split; [exact H |].
    rewrite /top_write /= H lookup_insert //.
Qed.

Section TreeMove.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Context `{!treeG Σ}.

  (* =================================================================== *)
  (*  2.  THE TWO MOVES ON THE CLAIM, AT THE ERA'S RECORD                 *)
  (* =================================================================== *)

  (* THE STEP, WRAPPED: [AppInv.app_step]'s shape at the tree claim.  The
     record equation is rewritten FIRST, as [TreeObs]'s laws do. *)
  Lemma tree_app_step_of (c : tree_fixed) (r : tree_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (tree_pred c r (abs_view I) -∗ tree_pred c r av') -∗ app_step i I av'.
  Proof.
    intros Heq. rewrite /app_step Heq. cbn [app_pred app_run app_names].
    iIntros "Hw" (n') "%Hav Hp". rewrite Hav. iNext. iApply ("Hw" with "Hp").
  Qed.

  (* ...and the one a TAINTED owner hands over: a tainted claim holds of
     every view, which is [AppInv.app_step_acc] without the supply. *)
  Lemma tree_app_step_taint (c : tree_fixed) (r : tree_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tree_taint c -∗ app_step i I av'.
  Proof.
    intros Heq. iIntros "#HT".
    iApply (tree_app_step_of c r i I av' Heq). iIntros "_".
    rewrite /tree_pred. iLeft. iExact "HT".
  Qed.

  (* PHASE 1's READ: the owner agrees the map the kernel lent it against
     the application's own half and reads its subtree off the claim.
     [UkTreeRead.tree_read_piece]'s three lines, at a LINEAR deed. *)
  Lemma tree_claim_read (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root : Z) (t : ttree) (I : gmap Z fs_node) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗ tree_own r g root t -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗ tree_own r g root t
      ∗ (⌜subtree (abs_view I) root = Some t⌝ ∨ tree_taint c).
  Proof.
    intros Heq. iIntros "#Hinv Hown Hka".
    iDestruct (tree_own_claim_law c r Heq) as "#Hlaw".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iAssert (▷ (app_pred app_run (abs_view I)
                ∗ (tree_own r g root t
                   ∗ (⌜subtree (abs_view I) root = Some t⌝ ∨ tree_taint c))))%I
      with "[Hp Hown]" as "[Hp Hrest]".
    { iNext.
      iDestruct ("Hlaw" $! (abs_view I) g root t with "Hown Hp") as "(A & B & C)".
      iFrame "A B C". }
    iMod "Hrest" as "[Hown Hfact]".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka Hown Hfact".
  Qed.

  (* PHASE 2's RESYNC, at the era's record: the ticket buys the entry back
     at the tree the POST view actually has. *)
  Lemma tree_claim_resync (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root : Z) (t t' : ttree) (I' : gmap Z fs_node) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    subtree (abs_view I') root = Some t' -> t' <> t ->
    app_inv γfs -∗ tree_tkt r g root t -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I'
      ∗ (tree_own r g root t' ∨ tree_taint c).
  Proof.
    intros Heq Hsub Hne. iIntros "#Hinv Htk Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iMod (tree_resync c r g root t t' (abs_view I') Hsub Hne with "Htk Hp")
      as "[Hp Hout]".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I'. iFrame "Hh Hx".
      iSplitL "Hp".
      - rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp".
      - iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka Hout".
  Qed.

  (* =================================================================== *)
  (*  3.  THE WRITE CHAIN, PAID OUT OF A DEED                             *)
  (* =================================================================== *)

  (* THE CURSOR: the deed, at a tree that differs from the one the caller
     started with only at the file it is writing. *)
  Definition tree_wq (c : tree_fixed) (r : tree_names) (g : gname)
      (root i : Z) (t : ttree) : iProp Σ :=
    ((∃ t' : ttree, tree_own r g root t' ∗ ⌜twrote i t t'⌝) ∨ tree_taint c)%I.

  (* ONE CHUNK, BOTH PHASES.  Common to the FULL and the PARTIAL arm: they
     differ only in the bytes they claim, never in the delta. *)
  Lemma tree_awrite_phases (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root i : Z) (t : ttree) (I : gmap Z fs_node)
      (off : nat) (bs bs0 : list (bv 8)) (nl : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    arow_at (abs_view I) i (MkAnode (AFile bs0) nl) ->
    app_inv γfs -∗ tree_wq c r g root i t -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step i I (delta_write i off bs (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
         ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         tree_wq c r g root i t).
  Proof.
    intros Heq Hrow. iIntros "#Hinv Hq Hka".
    rewrite /tree_wq.
    iDestruct "Hq" as "[Hd | #HT]"; last first.
    { (* THE TAINT: the step is free and the cursor comes back tainted *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    iDestruct "Hd" as (t') "[Hown %Hw]".
    iMod (tree_claim_read γfs c r g root t' I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { (* the claim is tainted: keep the deed, pay the step off the taint *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". iLeft.
      iExists t'. iFrame "Hown". by iPureIntro. }
    (* THE EXACT ARM: the owner's tree records the file the fire is at, so
       the fire's [arow_at] row is pinned to the tree's own bytes. *)
    destruct (twrote_file i t t' Hw) as (bst & Hti).
    destruct (tree_file_row (abs_view I) root i t' bst Hsub Hti) as (nl0 & Hav).
    pose proof (arow_at_pinned (abs_view I) i _ _ Hrow Hav) as Hab.
    injection Hab as Hbs Hnl. subst bs0. clear Hnl.
    assert (Hdom : i ∈ dom (tv_nodes t')) by exact (tree_file_dom root i t' bst Hti).
    destruct (decide (blk_splice off bs bst = bst)) as [Hinv0 | Hvis].
    - (* INVISIBLE: the delta is the identity on the view (AppTree 1j), so
         the free step pays it and the deed never moves. *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_of c r i I _ Heq).
        iApply (tree_step_write_free c r i off bs bst nl0 (abs_view I) Hav Hinv0). }
      iIntros (I') "%Hav' Hka'". iModIntro. iFrame "Hka'". iLeft.
      iExists t'. iFrame "Hown". by iPureIntro.
    - (* VISIBLE: park the deed and a fresh token, resync at phase 2 *)
      iMod tok_alloc as (γi) "Htok".
      rewrite tree_own_split. iDestruct "Hown" as "[Hdeed Htk]".
      assert (Hne : top_write i off bs t' <> t').
      { intros Hc. exact (Hvis (top_write_id_inv t' i off bs bst Hti Hc)). }
      assert (Hpost : subtree (delta_write i off bs (abs_view I)) root
                      = Some (top_write i off bs t'))
        by exact (subtree_delta_write (abs_view I) root i t' off bs bst nl0
                    Hsub Hav Hdom).
      iModIntro. iFrame "Hka". iSplitL "Hdeed Htok".
      { iApply (tree_app_step_of c r i I _ Heq).
        iApply (tree_step_move_write c r g root i t' off bs bst nl0
                  (abs_view I) γi Hav Hdom with "Hdeed Htok"). }
      iIntros (I') "%Hav' Hka'".
      iMod (tree_claim_resync γfs c r g root t' (top_write i off bs t') I'
              Heq ltac:(rewrite Hav'; exact Hpost) Hne with "Hinv Htk Hka'")
        as "[Hka' Hout]".
      iModIntro. iFrame "Hka'".
      iDestruct "Hout" as "[Hown | #HT]"; [| by iRight].
      iLeft. iExists (top_write i off bs t'). iFrame "Hown". iPureIntro.
      exact (twrote_trans i t t' _ Hw (twrote_write i t' off bs bst Hti)).
  Qed.

  (* THE CHAIN.  Every node offers the CURSOR and both arms; the kernel
     picks, and whichever arm fires builds the next node out of phase 2's
     own result.  This is [FsAbsWriteFire.awrite_chain_unit] with the
     application's SUPPLY replaced by the owner's DEED. *)
  Lemma tree_awrite_chain (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root i : Z) (t : ttree) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (cnt k : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗ tree_wq c r g root i t -∗
    awrite_chain (fs_gamma_L γfs) appE i γo M ua
      (fun _ : nat => tree_wq c r g root i t) k cnt.
  Proof.
    intros Heq. revert k. induction cnt as [| cnt IH]; intros k.
    { iIntros "#Hinv Hq". rewrite awrite_chain_0. iExact "Hq". }
    iIntros "#Hinv Hq". rewrite awrite_chain_S. iSplit; [iExact "Hq" |].
    iSplit.
    - rewrite /awrite_full_at.
      iIntros (I off bs bs0 nl) "%Hpre %Hby Hka Hoff".
      destruct Hpre as (Hrow & _ & _ & _).
      iMod (tree_awrite_phases γfs c r g root i t I off bs bs0 nl Heq Hrow
              with "Hinv Hq Hka") as "(Hka & Hstep & Hph2)".
      iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
      iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hq']".
      iModIntro. iFrame "Hka' Hoff". iApply (IH (S k) with "Hinv Hq'").
    - rewrite /awrite_part_at.
      iIntros (I off n bs bs0 nl) "%Hpre %Hn %Hgap %Hby Hka Hoff".
      destruct Hpre as (Hrow & _ & _ & _).
      iMod (tree_awrite_phases γfs c r g root i t I off bs bs0 nl Heq Hrow
              with "Hinv Hq Hka") as "(Hka & Hstep & Hph2)".
      iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
      iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hq']".
      iModIntro. iFrame "Hka' Hoff". iApply (IH (S k) with "Hinv Hq'").
  Qed.

End TreeMove.

(* ===================================================================== *)
(*  4.  WHAT AN OWNER CANNOT PAY AT THE LANDED FIRES, AND EXACTLY WHY     *)
(*      (the lane's STOP rule -- a precise wall beats a forced proof)     *)
(*                                                                       *)
(*  CREATE / MKNOD / MKDIR -- NOT PAYABLE, and the wall is TL-1's, not    *)
(*  this lane's.  [FsAbsCreateFire.acre_commit_at_gen]'s premise is       *)
(*  [FsAbsDelta.cre_pre], whose third conjunct is                         *)
(*  [av !! i = Some (MkAnode c 1)] -- THE CHILD IS ALREADY ARMED at the   *)
(*  parent leg's instant.  So the delta an owner would have to pay is     *)
(*  create's PARENT LEG ALONE ([FsAbsDelta.delta_ent], which at an armed  *)
(*  child is what [delta_create] collapses to), and the [own_wf]          *)
(*  preservation for that leg -- [own_wf_ent] -- is exactly what          *)
(*  design/user-tree.md section 6 records as PRICED AND NOT TAKEN: its    *)
(*  [aview_tree_wf] twin wants "nothing else names the armed inum"        *)
(*  ([aview_no_edge_to av i]), which needs an induction of its own and    *)
(*  which no party holds at the fire.  [AppTree.tree_step_move_create] is *)
(*  landed at the FUSED delta, i.e. at a view where the child is ABSENT;  *)
(*  that is the shape a fire would have if the two legs were one, and it  *)
(*  is not the shape the kernel has.                                      *)
(*                                                                       *)
(*  ...AND EVEN AT A LANDED [own_wf_ent] the create-family BUNDLE has two *)
(*  more walls, both worth recording because they are independent:        *)
(*    (a) THE CHILD'S FAILURE LEG.  [FsAbsCreateFire.cre_child_unfired]   *)
(*        asks the caller for the UNARM ([delta_unarm i], the row at [i]  *)
(*        DISAPPEARS).  An owner cannot pay it: the row is invisible to   *)
(*        every subtree only if NOTHING NAMES [i], and the claim's own    *)
(*        [own_wf] does not say so -- [TreeView.nreach_fresh] wants the   *)
(*        row ABSENT, which is false by then.  The generic supplier pays  *)
(*        it off [AppInv.app_sup], which a constraining application does  *)
(*        not have.  The honest fix is a credential threaded from the ARM *)
(*        to the UNARM ([aview_no_edge_to] at the unarm's own view), i.e. *)
(*        a change to [aarm_commit_at]'s receipt -- a kernel-tier lane.   *)
(*    (b) THE PARENT-PREFIX WALK.  [SysOpenDefs.open_au_create_at] owes   *)
(*        [FsAbsEra.ep_start] -- the walk to the PARENT of the path --    *)
(*        and [PinnedObs] offers a pinned supplier for [ex_start] only    *)
(*        ([pinned_obs] / [pinned_obs_abs]).  A parent-prefix twin is     *)
(*        additive and is what a mkdir/mknod/open-O_CREATE corollary      *)
(*        needs first.                                                    *)
(*                                                                       *)
(*  UNLINK -- the ENTRY leg IS payable in principle                       *)
(*  ([AppTree.tree_step_move_unl_ent] + [tree_resync], with               *)
(*  [SysUnlinkDefs.uent_commit_at] as the shape), but the commit          *)
(*  quantifies the PARENT [d] inside, so the supplier owes an answer at   *)
(*  every directory -- free outside the owner's subtree                   *)
(*  ([AppTree.tree_not_in_own]), the move inside -- and the TARGET leg at *)
(*  the LAST LINK is TL-2's own recorded wall ("the row is nobody's root" *)
(*  is a fact about the ownership map that no mover holds).  Its U-tier   *)
(*  leaf is blocked anyway: [UkTreeRead]'s section 5 records that unlink, *)
(*  like chdir, still carries the [∀ pl] walk form that a pin cannot      *)
(*  answer.  Recorded, not taken.                                         *)
(*                                                                       *)
(*  TRUNCATE -- [AppTree.tree_step_move_trunc] is landed and              *)
(*  [SysOpenDefs.open_trunc_piece] is its fire, but O_TRUNC arrives only  *)
(*  inside an open bundle, whose walk is the same pinned-walk question    *)
(*  as above at [om_trunc = true].  The tree-layer half is done.          *)
(* ===================================================================== *)
