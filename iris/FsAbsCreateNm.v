(* ===================================================================== *)
(*  FsAbsCreateNm.v -- THE CREATE COMMIT AT A NAME PREDICATE              *)
(*  (lane INIT-FILE, the §3.4 ruling's bottom layer).                     *)
(*                                                                       *)
(*  [FsAbsCreateFire.acre_commit_at_gen] quantifies the created NAME and  *)
(*  says only that it is neither dot name:                                *)
(*                                                                       *)
(*    forall I d i nm ents nl, pure(cre_pre ...) -* pure(nm <> DOT /\ nm <> DOTDOT) -* ... *)
(*                                                                       *)
(*  so a caller's claim is asked to absorb the create AT EVERY NAME.  The *)
(*  echo application absorbs it -- it tracks only `console`, and a create *)
(*  at another name does not touch that row -- but the FILE application   *)
(*  tracks `f` as well, and a create of a DEVICE called `f` in the root    *)
(*  is a view its claim has no arm for ([AppFile.f_ok] at an absent deed   *)
(*  is [f_absent], and the create makes it present).                      *)
(*                                                                       *)
(*  THE NAME PREDICATE is the commit at one more pure premise, and every  *)
(*  landed site is its instance at [fun _ => True]: the two bridges below  *)
(*  are that reading, in both directions.  A PROVIDER always has the      *)
(*  weaker obligation (it answers for fewer names), so the interesting    *)
(*  direction is [acre_commit_at -* acre_commit_at_nm Nm], which holds at *)
(*  EVERY [Nm] and is what keeps the landed dischargers one line.         *)
(*                                                                       *)
(*  A FILE OF ITS OWN, and additive: [FsAbsCreateFire.v] is at the bottom *)
(*  of the kernel tier and every one of its ~160 mention sites would      *)
(*  rebuild for a statement none of them uses.  What still has to move    *)
(*  for the file application to profit is recorded in the lane's          *)
(*  findings: the thread from here up to [SpecSysMknod.mknod_au_at] runs  *)
(*  through [SpecCreate]'s SHARED create bundle, which mkdir and          *)
(*  open(O_CREATE) also take.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import BlkmapDefs.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcAvail.
Require Import FsStateEra.
Require Import InodeRegion.
Require Import Xv6G.
Require FsImg.
Require Import FsAbsDelta.
Require Import AppInv.
Require Import PieceFam.
Require Import FsAbs.
Require Import PathElems.
Require Import ArgPath.
Require Import FsAbsCreateFire.

Local Open Scope Z_scope.

Section CreateNm.
  (* [FsAbsCreateFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* [acre_commit_at_gen] with the NAME PREDICATE beside the dot-name
     credential, in the position the ruling names. *)
  Definition acre_commit_at_gen_nm Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop)
      (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜cre_pre (abs_view I) d nm ents nl i (cf d i)⌝ -∗
       ⌜nm <> DOT /\ nm <> DOTDOT⌝ -∗
       ⌜Nm nm⌝ -∗
       cre_arm_fired Farm i -∗
       Pd d -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗ Pd d ∗
         app_step d I (delta_create d nm i (cf d i) (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_create d nm i (cf d i) (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) d nm i))%I.

  Definition acre_commit_at_nm Γ (E : coPset) (c : absnode)
      (Nm : fname -> Prop)
      (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    acre_commit_at_gen_nm Γ E (fun _ _ => c) Nm Pd Farm Φ.

  (* ---- THE TWO BRIDGES ---- *)

  (* A provider that answers at EVERY name answers a fortiori at the ones
     [Nm] admits.  This is the one line every landed discharger takes, and
     it is why none of them moves. *)
  Lemma acre_commit_at_gen_nm_of Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    acre_commit_at_gen Γ E cf Pd Farm Φ -∗
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ.
  Proof using .
    rewrite /acre_commit_at_gen /acre_commit_at_gen_nm. iIntros "H".
    iIntros (I d i nm ents nl) "%Hpre %Hnm _ Harm HPd Ha".
    iApply ("H" with "[//] [//] Harm HPd Ha").
  Qed.

  Lemma acre_commit_at_nm_of Γ (E : coPset) (c : absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    acre_commit_at Γ E c Pd Farm Φ -∗
    acre_commit_at_nm Γ E c Nm Pd Farm Φ.
  Proof using .
    rewrite /acre_commit_at /acre_commit_at_nm.
    iApply (acre_commit_at_gen_nm_of Γ E (fun _ _ => c) Nm Pd Farm Φ).
  Qed.

  (* ...and back, at the predicate every landed site is at. *)
  Lemma acre_commit_at_gen_of_nm Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    (forall nm : fname, Nm nm) ->
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ -∗
    acre_commit_at_gen Γ E cf Pd Farm Φ.
  Proof using .
    intros HNm. rewrite /acre_commit_at_gen /acre_commit_at_gen_nm.
    iIntros "H". iIntros (I d i nm ents nl) "%Hpre %Hnm Harm HPd Ha".
    iApply ("H" with "[//] [//] [%] Harm HPd Ha"). exact (HNm nm).
  Qed.

  Lemma acre_commit_at_of_nm Γ (E : coPset) (c : absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    (forall nm : fname, Nm nm) ->
    acre_commit_at_nm Γ E c Nm Pd Farm Φ -∗
    acre_commit_at Γ E c Pd Farm Φ.
  Proof using .
    intros HNm. rewrite /acre_commit_at /acre_commit_at_nm.
    iApply (acre_commit_at_gen_of_nm Γ E (fun _ _ => c) Nm Pd Farm Φ HNm).
  Qed.

  (* ...and the predicate NARROWS freely: a provider at a wider [Nm]
     provides at a narrower one. *)
  Lemma acre_commit_at_gen_nm_mono Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm Nm' : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    (forall nm : fname, Nm' nm -> Nm nm) ->
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ -∗
    acre_commit_at_gen_nm Γ E cf Nm' Pd Farm Φ.
  Proof using .
    intros Hle. rewrite /acre_commit_at_gen_nm. iIntros "H".
    iIntros (I d i nm ents nl) "%Hpre %Hnm %HNm' Harm HPd Ha".
    iApply ("H" with "[//] [//] [%] Harm HPd Ha"). exact (Hle nm HNm').
  Qed.

  (* THE SYSCALL-TIER READING, as [SysMknodDefs.npar_cur] is for the
     cursor: the created name at WHATEVER path argument 0 reads.  It is
     PURE, so the failure fold keeps its shape, and
     [ArgPath.arg_path_of_uniq] makes the guarded and the read forms
     interchangeable exactly as [SpecSysMknod.mknod_acre_inst] does for
     the cursor. *)
  Definition nlast_elem (pl : list (bv 8)) : option fname :=
    list_basics.last (path_elems pl).

  Definition npar_nm (M : gmap Z (bv 8)) (pv : mword 64) (nm : fname) : Prop :=
    forall pl : list (bv 8),
      arg_path_of M pv pl -> nlast_elem pl = Some nm.

  Lemma npar_nm_intro (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (nm : fname) :
    arg_path_of M pv pl -> nlast_elem pl = Some nm -> npar_nm M pv nm.
  Proof using .
    intros Hpl Hlast. rewrite /npar_nm. intros pl' Hpl'.
    by rewrite (arg_path_of_uniq M pv pl' pl Hpl' Hpl).
  Qed.

  Lemma npar_nm_elim (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (nm : fname) :
    arg_path_of M pv pl -> npar_nm M pv nm -> nlast_elem pl = Some nm.
  Proof using . intros Hpl Hnm. exact (Hnm pl Hpl). Qed.

End CreateNm.
