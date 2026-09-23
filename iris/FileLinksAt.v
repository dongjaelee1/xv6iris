(* ===================================================================== *)
(*  FileLinksAt.v -- THE CREDENTIAL FAMILIES AT A NAMED BOOT STATE        *)
(*  (lane INIT-FILE, RULING H).                                          *)
(*                                                                       *)
(*  Every family of [FileLinksLine.v] is                                  *)
(*                                                                       *)
(*    (exists ps cs s0 P, pure(...) * fcur v ps cs s0 I P k)  \/  head  \/  T *)
(*                                                                       *)
(*  and the era's BOOT STATE [s0] sits under that existential.  So a      *)
(*  holder of a credential knows the state is SOME value and can never    *)
(*  say WHICH -- which is what stops /init: it puts its deed's content    *)
(*  into [FileLinksLine.f0pre] when it hands the turn over, gets a lower  *)
(*  bound at a fresh existential back out of the banner, and cannot tie   *)
(*  the two.  sh's round needs exactly that tie ([UCatOut.cat_tie] is     *)
(*  [dst_content s = cat_st cs0 s0 I]).                                   *)
(*                                                                       *)
(*  THE FIX IS A SHARED INDEX, and it costs no ghost and no change to     *)
(*  [FileOut]'s stage: the families are instantiated a second time with   *)
(*  [s0] HOISTED out of the existential -- [GenLinksLine] at              *)
(*  [FileLinkGen.file_params_at], whose witness is [f0w] with the state   *)
(*  pinned -- the old form is that one's existential closure              *)
(*  ([FileLinkGen] section 6), and the taint arm is at EVERY [s0].  /init *)
(*  then names its deed's content once, at [f0pre_at], and reads the      *)
(*  same name back off the banner's own credential.  THIS FILE holds the  *)
(*  file's own pieces at the index: the head, the reader's residue, the   *)
(*  turn.                                                                *)
(*                                                                       *)
(*  WHY A FILE OF ITS OWN and not the bottom of [FileLinksLine.v]: the    *)
(*  program stream is live in [UShRound.v] and in everything that reads   *)
(*  [fhead] / [fab] / [fwc_*].  Appending there would rebuild that cone   *)
(*  under them for no statement they use; here the layer is a leaf and    *)
(*  nothing below it moves.                                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinksLine.
Require Import FileHooks.         (* S0 of [FileLinksLine], moved *)
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section file_links_at.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FPIN := (era_pin (fgn_echo g)).

  (* =================================================================== *)
  (*  1.  THE ERA'S HEAD, AT A NAMED STATE                                *)
  (* =================================================================== *)
  Definition f0pre_at (s0 : fstate) : iProp Σ :=
    (⌜fstate_ok s0⌝ ∗ (f0_typed g s0 ∨ FT) ∗ f0bw g (S gen_id) s0)%I.

  Global Instance f0pre_at_timeless s0 : Timeless (f0pre_at s0).
  Proof using . rewrite /f0pre_at. apply _. Qed.
  Global Instance f0pre_at_persistent s0 : Persistent (f0pre_at s0).
  Proof using . rewrite /f0pre_at. apply _. Qed.

  (* THE DISPATCH, NOT [apply _].  The tree carries 455 [Timeless]
     instances, and because most of the definitions under them are
     transparent the hint net cannot discriminate: a search tries nearly
     all of them, measured ~1.3s per GOAL at this altitude -- which is
     what made the twelve-instance block below 78s of this 86s file.
     Descend through the CONNECTIVES and name the leaf instance, so no
     search runs at all.  The dispatch must be SYNTACTIC: a [first [...]]
     spelling unifies up to delta and peels straight through a name that
     has its own instance.  [tl_leaf] is what a body bottoms out in;
     [tl_at] adds the head and the families below can reach it. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (f0pre_at _) => apply f0pre_at_timeless
    | |- Timeless (fcur _ _ _ _ _ _ _ _) => apply fcur_timeless
    | |- Timeless (f0w _ _ _) => apply f0w_timeless
    | |- Timeless (f0bw _ _ _) => apply f0bw_timeless
    | |- Timeless (f0_typed _ _) => apply f0_typed_timeless
    | |- Timeless (file_taint _) => apply file_taint_timeless
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (file_era_pin _ _ _) => apply file_era_pin_timeless
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; tl_leaf
    | |- Persistent (bi_sep _ _) => apply bi.sep_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_or _ _) => apply bi.or_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- Persistent (inp_lb _ _) => apply inp_lb_persistent
    | |- Persistent (f0w _ _ _) => apply f0w_persistent
    | |- Persistent (f0bw _ _ _) => apply f0bw_persistent
    | |- Persistent (f0_typed _ _) => apply f0_typed_persistent
    | |- Persistent (file_taint _) => apply file_taint_persistent
    | |- Persistent (file_era_pin _ _ _) => apply file_era_pin_persistent
    | |- _ => apply _
    end.


  Lemma f0pre_at_pack (s0 : fstate) : f0pre_at s0 -∗ f0pre g.
  Proof using . iIntros "H". rewrite /FileLinksLine.f0pre. by iExists s0. Qed.

  Lemma f0pre_unpack : f0pre g -∗ ∃ s0 : fstate, f0pre_at s0.
  Proof using .
    rewrite /FileLinksLine.f0pre. iIntros "H". iDestruct "H" as (s0) "H".
    iExists s0. iExact "H".
  Qed.

  Definition fhead_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    (⌜I = []⌝ ∗ ⌜k = S gen_id⌝ ∗ turn v 0%nat ∗ ps_lb v [] ∗ cs_lb v []
     ∗ inp_lb v [] ∗ (∃ vf : file_era, file_era_pin g k vf)
     ∗ f0pre_at s0)%I.

  Global Instance fhead_at_timeless s0 k v I : Timeless (fhead_at s0 k v I).
  Proof using . rewrite /fhead_at. tl_leaf. Qed.

  Lemma fhead_at_pack (s0 : fstate) k v I : fhead_at s0 k v I -∗ fhead g k v I.
  Proof using .
    rewrite /fhead_at /FileLinksLine.fhead.
    iIntros "(%HI & %Hk & Ht & Hps & Hcs & HE & Hvf & Hpre)".
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iFrame "Ht Hps Hcs HE Hvf". iApply (f0pre_at_pack s0 with "Hpre").
  Qed.

  Lemma fhead_unpack k v I : fhead g k v I -∗ ∃ s0 : fstate, fhead_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fhead /fhead_at.
    iIntros "(%HI & %Hk & Ht & Hps & Hcs & HE & Hvf & Hpre)".
    iDestruct (f0pre_unpack with "Hpre") as (s0) "Hpre".
    iExists s0. iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iFrame "Ht Hps Hcs HE Hvf Hpre".
  Qed.

  (* =================================================================== *)
  (*  2.  THE READER'S RESIDUE, AT A NAMED STATE                          *)
  (* =================================================================== *)
  Definition fwc_rres_at (s0 : fstate) (v : era_pins) (I : list (bv 8))
    : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage_f ps0 cs0 I⌝
       ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0) I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ f0bw g (S gen_id) s0)%I.

  Global Instance fwc_rres_at_persistent s0 v I :
    Persistent (fwc_rres_at s0 v I).
  Proof using . rewrite /fwc_rres_at. tl_leaf. Qed.
  Global Instance fwc_rres_at_timeless s0 v I : Timeless (fwc_rres_at s0 v I).
  Proof using . rewrite /fwc_rres_at. tl_leaf. Qed.

  (* =================================================================== *)
  (*  3.  THE PACKING LEMMAS, BOTH WAYS                                   *)
  (* =================================================================== *)
  Lemma fwc_rres_at_pack s0 v I : fwc_rres_at s0 v I -∗ fwc_rres g v I.
  Proof using .
    rewrite /fwc_rres_at /FileLinksLine.fwc_rres.
    iIntros "H". iDestruct "H" as (ps0 cs0) "(%Hr & Ht & Hps & Hcs & Hf)".
    iExists ps0, cs0, s0. iFrame "Ht Hps Hcs Hf". by iPureIntro.
  Qed.

  Lemma fwc_rres_unpack v I :
    fwc_rres g v I -∗ ∃ s0 : fstate, fwc_rres_at s0 v I.
  Proof using .
    rewrite /FileLinksLine.fwc_rres /fwc_rres_at.
    iIntros "H". iDestruct "H" as (ps0 cs0 s0) "(%Hr & Ht & Hps & Hcs & Hf)".
    iExists s0, ps0, cs0. iFrame "Ht Hps Hcs Hf". by iPureIntro.
  Qed.

  (* ...and the record's residue WITH THE TYPED LINES' WITNESS
     ([FileLinksLine.fwc_rresw]), at the index *)
  Definition fwc_rresw_at (s0 : fstate) (v : era_pins) (I : list (bv 8))
    : iProp Σ := (fwc_rres_at s0 v I ∗ FileLinksLine.flw g I)%I.

  Global Instance fwc_rresw_at_persistent s0 v I :
    Persistent (fwc_rresw_at s0 v I).
  Proof using . rewrite /fwc_rresw_at. apply _. Qed.
  Global Instance fwc_rresw_at_timeless s0 v I :
    Timeless (fwc_rresw_at s0 v I).
  Proof using . rewrite /fwc_rresw_at. apply _. Qed.

  Lemma fwc_rresw_at_pack s0 v I :
    fwc_rresw_at s0 v I -∗ FileLinksLine.fwc_rresw g v I.
  Proof using .
    rewrite /fwc_rresw_at /FileLinksLine.fwc_rresw. iIntros "[H $]".
    iApply (fwc_rres_at_pack with "H").
  Qed.

  Lemma fwc_rresw_unpack v I :
    FileLinksLine.fwc_rresw g v I -∗ ∃ s0 : fstate, fwc_rresw_at s0 v I.
  Proof using .
    rewrite /fwc_rresw_at /FileLinksLine.fwc_rresw. iIntros "[H #Hw]".
    iDestruct (fwc_rres_unpack with "H") as (s0) "H".
    iExists s0. iFrame "H Hw".
  Qed.

  (* =================================================================== *)
  (*  4.  THE ERA'S TURN, AT THE NAMED STATE ([GenLinksLine.gen_link_inst]'s *)
  (*      TURN at [FileLinkGen.file_link_gen_at]; [fturn0_gen_at] takes   *)
  (*      it apart)                                                       *)
  (* =================================================================== *)
  Definition fturn_pre_at (s0 : fstate) (k : nat) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ FileOut.fturn_core g k ∗ f0pre_at s0)%I.

End file_links_at.
