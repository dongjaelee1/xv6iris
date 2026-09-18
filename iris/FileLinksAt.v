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
(*  [FileOut]'s stage: each family gets an [_at s0] twin with [s0]        *)
(*  HOISTED out of the existential, the old form is its existential       *)
(*  closure (packing lemmas both ways, below), and the taint arm is at    *)
(*  EVERY [s0].  /init then names its deed's content once, at             *)
(*  [f0pre_at], and reads the same name back off the banner's own         *)
(*  credential.                                                          *)
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
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import EchoLinks.
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
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
    (⌜fstate_ok s0⌝ ∗ (f0_typed g s0 ∨ FT))%I.

  Global Instance f0pre_at_timeless s0 : Timeless (f0pre_at s0).
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

  (* the head, now that it has its own instance, is a leaf for the
     families below *)
  Local Ltac tl_at :=
    lazymatch goal with
    | |- Timeless (fhead_at _ _ _ _) => apply fhead_at_timeless
    | |- _ => tl_leaf
    end.

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
  (*  2.  THE TWELVE FAMILIES, AT A NAMED STATE                           *)
  (* =================================================================== *)
  Definition fwc_pro_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_pro_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k)
     ∨ fhead_at s0 k v I ∨ FT)%I.

  Definition fwc_owed_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_owed_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k)
     ∨ fhead_at s0 k v I ∨ FT)%I.

  Definition fwc_sp_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_sp_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_open_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_open_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_sp_t_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_sp_t_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_open_t_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_open_t_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_lend_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_blk_t_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_blk_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a i : nat) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_blk_t_f ps cs s0 I P⌝
        ∗ turn v (P + i)%nat ∗ ps_lb v ps ∗ cs_lb v (blkcs_f cs a i)
        ∗ inp_lb v I ∗ f0w g k s0)
     ∨ FT)%I.

  Definition fwc_ban_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (i : nat) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_banp_f ps cs s0 I P i⌝
        ∗ turn v (P + i)%nat ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I
        ∗ f0w g k s0)
     ∨ (⌜i = 0%nat⌝ ∗ fhead_at s0 k v I) ∨ FT)%I.

  Definition fwc_line_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    (fwc_pro_at s0 k v I
     ∨ ∃ a : nat, ⌜fapr I a⌝
         ∗ fwc_blk_at s0 k v I a (length (fab I a) - 2)%nat)%I.

  Definition fwc_pr_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => fwc_owed_at s0 k v I
    | S O => fwc_sp_at s0 k v I
    | _ => fwc_open_at s0 k v I
    end.

  Definition fwc_lpr_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => fwc_line_at s0 k v I
    | S O => fwc_sp_t_at s0 k v I
    | S (S O) => fwc_open_t_at s0 k v I
    | _ => fwc_blk_at s0 k v I 0%nat 0%nat
    end.

  Definition fwc_rres_at (s0 : fstate) (v : era_pins) (I : list (bv 8))
    : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage_f ps0 cs0 I⌝
       ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0) I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ f0w g (S gen_id) s0)%I.

  (* ---- timelessness, which is what the record's fields need ---- *)
  Global Instance fwc_pro_at_timeless s0 k v I : Timeless (fwc_pro_at s0 k v I).
  Proof using . rewrite /fwc_pro_at. tl_at. Qed.
  Global Instance fwc_owed_at_timeless s0 k v I : Timeless (fwc_owed_at s0 k v I).
  Proof using . rewrite /fwc_owed_at. tl_at. Qed.
  Global Instance fwc_sp_at_timeless s0 k v I : Timeless (fwc_sp_at s0 k v I).
  Proof using . rewrite /fwc_sp_at. tl_at. Qed.
  Global Instance fwc_open_at_timeless s0 k v I : Timeless (fwc_open_at s0 k v I).
  Proof using . rewrite /fwc_open_at. tl_at. Qed.
  Global Instance fwc_sp_t_at_timeless s0 k v I : Timeless (fwc_sp_t_at s0 k v I).
  Proof using . rewrite /fwc_sp_t_at. tl_at. Qed.
  Global Instance fwc_open_t_at_timeless s0 k v I :
    Timeless (fwc_open_t_at s0 k v I).
  Proof using . rewrite /fwc_open_t_at. tl_at. Qed.
  Global Instance fwc_lend_at_timeless s0 k v I : Timeless (fwc_lend_at s0 k v I).
  Proof using . rewrite /fwc_lend_at. tl_at. Qed.
  Global Instance fwc_blk_at_timeless s0 k v I a i :
    Timeless (fwc_blk_at s0 k v I a i).
  Proof using . rewrite /fwc_blk_at. tl_at. Qed.
  Global Instance fwc_ban_at_timeless s0 k v I i :
    Timeless (fwc_ban_at s0 k v I i).
  Proof using . rewrite /fwc_ban_at. tl_at. Qed.
  Global Instance fwc_line_at_timeless s0 k v I : Timeless (fwc_line_at s0 k v I).
  Proof using .
    rewrite /fwc_line_at.
    apply bi.or_timeless; [apply fwc_pro_at_timeless |].
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply fwc_blk_at_timeless].
  Qed.
  Global Instance fwc_pr_at_timeless s0 k v I p : Timeless (fwc_pr_at s0 k v I p).
  Proof using .
    rewrite /fwc_pr_at. destruct p as [| [| p]];
      [apply fwc_owed_at_timeless | apply fwc_sp_at_timeless
      | apply fwc_open_at_timeless].
  Qed.
  Global Instance fwc_lpr_at_timeless s0 k v I p :
    Timeless (fwc_lpr_at s0 k v I p).
  Proof using .
    rewrite /fwc_lpr_at. destruct p as [| [| [| p]]];
      [apply fwc_line_at_timeless | apply fwc_sp_t_at_timeless
      | apply fwc_open_t_at_timeless | apply fwc_blk_at_timeless].
  Qed.
  Global Instance fwc_rres_at_persistent s0 v I :
    Persistent (fwc_rres_at s0 v I).
  Proof using . rewrite /fwc_rres_at. tl_leaf. Qed.
  Global Instance fwc_rres_at_timeless s0 v I : Timeless (fwc_rres_at s0 v I).
  Proof using . rewrite /fwc_rres_at. tl_leaf. Qed.

  (* ---- the taint is at EVERY state ---- *)
  Lemma fwc_pro_at_taint s0 k v I : FT -∗ fwc_pro_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_pro_at. iRight. by iRight. Qed.
  Lemma fwc_owed_at_taint s0 k v I : FT -∗ fwc_owed_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_owed_at. iRight. by iRight. Qed.
  Lemma fwc_sp_at_taint s0 k v I : FT -∗ fwc_sp_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_sp_at. by iRight. Qed.
  Lemma fwc_open_at_taint s0 k v I : FT -∗ fwc_open_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_open_at. by iRight. Qed.
  Lemma fwc_sp_t_at_taint s0 k v I : FT -∗ fwc_sp_t_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_sp_t_at. by iRight. Qed.
  Lemma fwc_open_t_at_taint s0 k v I : FT -∗ fwc_open_t_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_open_t_at. by iRight. Qed.
  Lemma fwc_lend_at_taint s0 k v I : FT -∗ fwc_lend_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_lend_at. by iRight. Qed.
  Lemma fwc_blk_at_taint s0 k v I a i : FT -∗ fwc_blk_at s0 k v I a i.
  Proof using . iIntros "H". rewrite /fwc_blk_at. by iRight. Qed.
  Lemma fwc_ban_at_taint s0 k v I i : FT -∗ fwc_ban_at s0 k v I i.
  Proof using . iIntros "H". rewrite /fwc_ban_at. iRight. by iRight. Qed.
  Lemma fwc_line_at_taint s0 k v I : FT -∗ fwc_line_at s0 k v I.
  Proof using .
    iIntros "H". rewrite /fwc_line_at. iLeft.
    iApply (fwc_pro_at_taint with "H").
  Qed.
  Lemma fwc_lpr_at_taint s0 k v I p : FT -∗ fwc_lpr_at s0 k v I p.
  Proof using .
    iIntros "H". rewrite /fwc_lpr_at. destruct p as [| [| [| p]]].
    - iApply (fwc_line_at_taint with "H").
    - iApply (fwc_sp_t_at_taint with "H").
    - iApply (fwc_open_t_at_taint with "H").
    - iApply (fwc_blk_at_taint with "H").
  Qed.

  (* =================================================================== *)
  (*  3.  THE PACKING LEMMAS, BOTH WAYS                                   *)
  (* =================================================================== *)
  Lemma fwc_pro_at_pack s0 k v I : fwc_pro_at s0 k v I -∗ fwc_pro g k v I.
  Proof using .
    rewrite /fwc_pro_at /FileLinksLine.fwc_pro.
    iIntros "[H | [H | #HT]]"; [| iRight; iLeft | iRight; by iRight].
    - iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
      iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
    - iApply (fhead_at_pack with "H").
  Qed.

  Lemma fwc_pro_unpack k v I :
    fwc_pro g k v I -∗ ∃ s0 : fstate, fwc_pro_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_pro /fwc_pro_at.
    iIntros "[H | [H | #HT]]".
    - iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
      iExists ps, cs, P. iFrame "Hc". by iPureIntro.
    - iDestruct (fhead_unpack with "H") as (s0) "H". iExists s0.
      iRight. by iLeft.
    - iExists None. iRight. iRight. iExact "HT".
  Qed.

  Lemma fwc_owed_at_pack s0 k v I : fwc_owed_at s0 k v I -∗ fwc_owed g k v I.
  Proof using .
    rewrite /fwc_owed_at /FileLinksLine.fwc_owed.
    iIntros "[H | [H | #HT]]"; [| iRight; iLeft | iRight; by iRight].
    - iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
      iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
    - iApply (fhead_at_pack with "H").
  Qed.

  Lemma fwc_owed_unpack k v I :
    fwc_owed g k v I -∗ ∃ s0 : fstate, fwc_owed_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_owed /fwc_owed_at.
    iIntros "[H | [H | #HT]]".
    - iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
      iExists ps, cs, P. iFrame "Hc". by iPureIntro.
    - iDestruct (fhead_unpack with "H") as (s0) "H". iExists s0.
      iRight. by iLeft.
    - iExists None. iRight. iRight. iExact "HT".
  Qed.

  Lemma fwc_sp_at_pack s0 k v I : fwc_sp_at s0 k v I -∗ fwc_sp g k v I.
  Proof using .
    rewrite /fwc_sp_at /FileLinksLine.fwc_sp.
    iIntros "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
    iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_sp_unpack k v I :
    fwc_sp g k v I -∗ ∃ s0 : fstate, fwc_sp_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_sp /fwc_sp_at.
    iIntros "[H | #HT]"; last by (iExists None; iRight).
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
    iExists ps, cs, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_open_at_pack s0 k v I : fwc_open_at s0 k v I -∗ fwc_open g k v I.
  Proof using .
    rewrite /fwc_open_at /FileLinksLine.fwc_open.
    iIntros "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
    iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_open_unpack k v I :
    fwc_open g k v I -∗ ∃ s0 : fstate, fwc_open_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_open /fwc_open_at.
    iIntros "[H | #HT]"; last by (iExists None; iRight).
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
    iExists ps, cs, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_sp_t_at_pack s0 k v I : fwc_sp_t_at s0 k v I -∗ fwc_sp_t g k v I.
  Proof using .
    rewrite /fwc_sp_t_at /FileLinksLine.fwc_sp_t.
    iIntros "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
    iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_sp_t_unpack k v I :
    fwc_sp_t g k v I -∗ ∃ s0 : fstate, fwc_sp_t_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_sp_t /fwc_sp_t_at.
    iIntros "[H | #HT]"; last by (iExists None; iRight).
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
    iExists ps, cs, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_open_t_at_pack s0 k v I :
    fwc_open_t_at s0 k v I -∗ fwc_open_t g k v I.
  Proof using .
    rewrite /fwc_open_t_at /FileLinksLine.fwc_open_t.
    iIntros "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
    iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_open_t_unpack k v I :
    fwc_open_t g k v I -∗ ∃ s0 : fstate, fwc_open_t_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_open_t /fwc_open_t_at.
    iIntros "[H | #HT]"; last by (iExists None; iRight).
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
    iExists ps, cs, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_lend_at_pack s0 k v I : fwc_lend_at s0 k v I -∗ fwc_lend g k v I.
  Proof using .
    rewrite /fwc_lend_at /FileLinksLine.fwc_lend.
    iIntros "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]". iLeft.
    iExists ps, cs, s0, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_lend_unpack k v I :
    fwc_lend g k v I -∗ ∃ s0 : fstate, fwc_lend_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_lend /fwc_lend_at.
    iIntros "[H | #HT]"; last by (iExists None; iRight).
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]". iExists s0. iLeft.
    iExists ps, cs, P. iFrame "Hc". by iPureIntro.
  Qed.

  Lemma fwc_blk_at_pack s0 k v I a i :
    fwc_blk_at s0 k v I a i -∗ fwc_blk g k v I a i.
  Proof using .
    rewrite /fwc_blk_at /FileLinksLine.fwc_blk.
    iIntros "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Ht & Hps & Hcs & HE & Hf)". iLeft.
    iExists ps, cs, s0, P. iFrame "Ht Hps Hcs HE Hf". by iPureIntro.
  Qed.

  Lemma fwc_blk_unpack k v I a i :
    fwc_blk g k v I a i -∗ ∃ s0 : fstate, fwc_blk_at s0 k v I a i.
  Proof using .
    rewrite /FileLinksLine.fwc_blk /fwc_blk_at.
    iIntros "[H | #HT]"; last by (iExists None; iRight).
    iDestruct "H" as (ps cs s0 P) "(%Hw & Ht & Hps & Hcs & HE & Hf)".
    iExists s0. iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE Hf".
    by iPureIntro.
  Qed.

  Lemma fwc_ban_at_pack s0 k v I i :
    fwc_ban_at s0 k v I i -∗ fwc_ban g k v I i.
  Proof using .
    rewrite /fwc_ban_at /FileLinksLine.fwc_ban.
    iIntros "[H | [[%Hi0 H] | #HT]]"; [| | iRight; by iRight].
    - iDestruct "H" as (ps cs P) "(%Hw & Ht & Hps & Hcs & HE & Hf)". iLeft.
      iExists ps, cs, s0, P. iFrame "Ht Hps Hcs HE Hf". by iPureIntro.
    - iRight. iLeft. iSplitR; [ by iPureIntro | ].
      iApply (fhead_at_pack with "H").
  Qed.

  Lemma fwc_ban_unpack k v I i :
    fwc_ban g k v I i -∗ ∃ s0 : fstate, fwc_ban_at s0 k v I i.
  Proof using .
    rewrite /FileLinksLine.fwc_ban /fwc_ban_at.
    iIntros "[H | [[%Hi0 H] | #HT]]"; last by (iExists None; iRight; iRight).
    - iDestruct "H" as (ps cs s0 P) "(%Hw & Ht & Hps & Hcs & HE & Hf)".
      iExists s0. iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE Hf".
      by iPureIntro.
    - iDestruct (fhead_unpack with "H") as (s0) "H". iExists s0.
      iRight. iLeft. iSplitR; [ by iPureIntro | ]. iExact "H".
  Qed.

  Lemma fwc_line_at_pack s0 k v I : fwc_line_at s0 k v I -∗ fwc_line g k v I.
  Proof using .
    rewrite /fwc_line_at /FileLinksLine.fwc_line.
    iIntros "[H | H]".
    - iLeft. iApply (fwc_pro_at_pack with "H").
    - iRight. iDestruct "H" as (a) "[%Ha H]". iExists a.
      iSplitR; [ by iPureIntro | ]. iApply (fwc_blk_at_pack with "H").
  Qed.

  Lemma fwc_line_unpack k v I :
    fwc_line g k v I -∗ ∃ s0 : fstate, fwc_line_at s0 k v I.
  Proof using .
    rewrite /FileLinksLine.fwc_line /fwc_line_at.
    iIntros "[H | H]".
    - iDestruct (fwc_pro_unpack with "H") as (s0) "H". iExists s0. by iLeft.
    - iDestruct "H" as (a) "[%Ha H]".
      iDestruct (fwc_blk_unpack with "H") as (s0) "H". iExists s0.
      iRight. iExists a. iSplitR; [ by iPureIntro | ]. iExact "H".
  Qed.

  Lemma fwc_lpr_at_pack s0 k v I p :
    fwc_lpr_at s0 k v I p -∗ fwc_lpr g k v I p.
  Proof using .
    rewrite /fwc_lpr_at /FileLinksLine.fwc_lpr.
    destruct p as [| [| [| p]]]; iIntros "H".
    - iApply (fwc_line_at_pack with "H").
    - iApply (fwc_sp_t_at_pack with "H").
    - iApply (fwc_open_t_at_pack with "H").
    - iApply (fwc_blk_at_pack with "H").
  Qed.

  Lemma fwc_lpr_unpack k v I p :
    fwc_lpr g k v I p -∗ ∃ s0 : fstate, fwc_lpr_at s0 k v I p.
  Proof using .
    rewrite /FileLinksLine.fwc_lpr /fwc_lpr_at.
    destruct p as [| [| [| p]]]; iIntros "H".
    - iApply (fwc_line_unpack with "H").
    - iApply (fwc_sp_t_unpack with "H").
    - iApply (fwc_open_t_unpack with "H").
    - iApply (fwc_blk_unpack with "H").
  Qed.

  Lemma fwc_pr_at_pack s0 k v I p : fwc_pr_at s0 k v I p -∗ fwc_pr g k v I p.
  Proof using .
    rewrite /fwc_pr_at /FileLinksLine.fwc_pr.
    destruct p as [| [| p]]; iIntros "H".
    - iApply (fwc_owed_at_pack with "H").
    - iApply (fwc_sp_at_pack with "H").
    - iApply (fwc_open_at_pack with "H").
  Qed.

  Lemma fwc_pr_unpack k v I p :
    fwc_pr g k v I p -∗ ∃ s0 : fstate, fwc_pr_at s0 k v I p.
  Proof using .
    rewrite /FileLinksLine.fwc_pr /fwc_pr_at.
    destruct p as [| [| p]]; iIntros "H".
    - iApply (fwc_owed_unpack with "H").
    - iApply (fwc_sp_unpack with "H").
    - iApply (fwc_open_unpack with "H").
  Qed.

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

End file_links_at.
