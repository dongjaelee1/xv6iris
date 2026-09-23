(* ===================================================================== *)
(*  PipeLinkGen.v -- THE PIPELINE APPLICATION'S CONSOLE FAMILIES AS THE   *)
(*  GENERIC ONES (app-both milestone M2c).                               *)
(*                                                                       *)
(*  [GenLinksLine] at the pipeline model: the taint is the echo taint,   *)
(*  the pin the era's pin, no state witness ([emp]: no line touches the  *)
(*  file system), no head arm, and the two-writer terminal round         *)
(*  ([PipeBoth.pwc_blk2]) as the per-shape line arm [X], whose prompt    *)
(*  step is [PipeBoth.pblk2_exit_lk].  [PipeLinks.pipe_links] entails    *)
(*  the links interface, the read receipt exposes the reader's residue,  *)
(*  and the turn comes apart into the generic banner-owed credential     *)
(*  through the cursor arm.  [pipe_link_gen] is [gen_link_inst].         *)
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
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import LineModel.
Require Import LineModelLinks.
Require Import LineModelInst.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeBoth.
Require Import LinkRec.
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section pipe_link_gen.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  Local Notation PT := (echo_taint γ).

  (* =================================================================== *)
  (*  1.  THE PARAMETERS                                                  *)
  (* =================================================================== *)
  Definition pipe_W (k : nat) (s : unit) : iProp Σ := emp%I.
  Definition pipe_Wb (k : nat) (s : unit) : iProp Σ := emp%I.
  Definition pipe_H (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ := False%I.

  Lemma pipe_W_pers k s : Persistent (pipe_W k s).
  Proof using . rewrite /pipe_W. apply _. Qed.
  Lemma pipe_W_tl k s : Timeless (pipe_W k s).
  Proof using . rewrite /pipe_W. apply _. Qed.
  Lemma pipe_W_bw k s : pipe_W k s -∗ pipe_Wb k s.
  Proof using . by iIntros "$". Qed.
  Lemma pipe_W_bw0 k s : pipe_W k s -∗ pipe_Wb 0 s.
  Proof using . by iIntros "$". Qed.
  Lemma pipe_Wb_agree k (s s' : unit) : pipe_Wb k s -∗ pipe_Wb k s' -∗ ⌜s = s'⌝.
  Proof using . iIntros "_ _". iPureIntro. by destruct s, s'. Qed.
  Lemma pipe_H_tl k v I : Timeless (pipe_H k v I).
  Proof using . rewrite /pipe_H. apply _. Qed.
  Lemma pipe_H_cur k v I :
    pipe_H k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using . iIntros "[]". Qed.
  Lemma pipe_H_inp k v I : pipe_H k v I -∗ pipe_H k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using . iIntros "[]". Qed.

  Definition pipe_params : gen_params pipe_lm :=
    MkGP pipe_lm pipe_lm_laws pipe_hooks
      PT _ _
      (era_pin γ) _ _ (era_pin_agree γ)
      pipe_W pipe_W_pers pipe_W_tl
      pipe_Wb pipe_W_pers pipe_W_tl 0 pipe_W_bw pipe_W_bw0 pipe_Wb_agree
      pipe_H pipe_H_tl pipe_H_cur pipe_H_inp.

  (* the per-shape line arm: the terminal round's block, written by two
     processes at the two cursors and not yet filed *)
  Definition pipe_X (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ (R : list (bv 8)) (sel : list bool) (c1 c2 a : nat),
       ⌜pblk2_code I R sel a⌝ ∗ ⌜sel <> []⌝
       ∗ pwc_blk2 g k v I R sel c1 c2 false)%I.

  Lemma pipe_X_tl k v I : Timeless (pipe_X k v I).
  Proof using .
    rewrite /pipe_X.
    do 5 (apply bi.exist_timeless; intro).
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply bi.pure_timeless | apply pwc_blk2_timeless].
  Qed.

  (* =================================================================== *)
  (*  2.  THE LINKS ENTAIL THE INTERFACE                                  *)
  (* =================================================================== *)
  Lemma pipe_links_gl : pipe_links g -∗ glinks pipe_lm pipe_params.
  Proof using .
    iIntros "#Hlk".
    iDestruct (pipe_links_w with "Hlk") as "#Hw".
    iDestruct (pipe_links_blk with "Hlk") as "#Hblk".
    iDestruct (pipe_links_pro with "Hlk") as "#Hpro".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /glinks. iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
    - (* W *)
      rewrite /gl_w.
      iIntros "!>" (k v P b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      iApply ("Hw" $! k v P b ps0 cs0 I0 Φ with "[%] [%] [%] Hpin Htn Hps Hcs HE HΦ").
      { exact H1. }
      { exact (proj2 (pro_pin_p_lm _ _ _) H2). }
      { rewrite proc_stream_p_lm. destruct s0. exact H3. }
    - (* BLK *)
      rewrite /gl_blk.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      iApply ("Hblk" $! k v P a b ps0 cs0 I0 Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE HΦ").
      { exact H1. } { exact H2. } { exact H3. }
      { exact (proj2 (pro_pin_p_lm _ _ _) H4). }
      { rewrite proc_before_p_lm. destruct s0. exact H5. }
      { exact H6. } { exact H7. } { exact H8. }
    - (* PRO *)
      rewrite /gl_pro.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      iApply ("Hpro" $! k v P a b ps0 cs0 I0 Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE HΦ").
      { exact H1. } { exact H2. } { exact H3. }
      { exact (proj2 (pro_pin_p_lm _ _ _) H4). }
      { rewrite pro_idx_p_lm. exact H5. }
      { rewrite proc_stream_p_lm. destruct s0. exact H6. }
      { exact H7. } { exact H8. }
    - (* HEAD: absent *)
      rewrite /gl_head. iIntros "!>" (k v I a b Φ) "_ _ _ [] _".
    - (* TAINT *)
      rewrite /gl_taint. iIntros "!>" (k b Φ) "#HT HΦ".
      iApply ("Ht" $! k b Φ with "HT HΦ").
  Qed.

  (* the terminal round's prompt: [PipeBoth]'s exit law, its continuation
     read back at the generic tight shape *)
  Lemma pwc_sp_t_gen k v I : pwc_sp_t g k v I -∗ gwc_sp_t pipe_lm pipe_params k v I.
  Proof using .
    rewrite /pwc_sp_t /gwc_sp_t. iIntros "[Hl | #HT]"; [| by iRight].
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    rewrite wr_sp_t_p_lm in Hw.
    iLeft. iExists ps, cs, tt, P. rewrite /gcur /pipe_W. iFrame "Htn Hps Hcs HE".
    by iPureIntro.
  Qed.

  Lemma pipe_X_dollar (k : nat) (v : era_pins) (I : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pipe_X k v I -∗
    (gwc_sp_t pipe_lm pipe_params k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb. iIntros "#Hpin #Hlk Hx HΦ".
    iDestruct "Hx" as (R sel c1 c2 a) "(%Hcode & %Hnn & Hc)".
    iDestruct (PipeLinks.pipe_links_file with "Hlk") as "#HF".
    iDestruct (PipeLinks.pipe_links_taint with "Hlk") as "#Ht".
    iApply (pblk2_exit_lk g k v I R sel c1 c2 a b Φ Hcode Hnn Hb
              with "HF Ht Hpin Hc [HΦ]").
    iIntros "Hc". iApply "HΦ". iApply (pwc_sp_t_gen with "Hc").
  Qed.

  (* =================================================================== *)
  (*  3.  THE READ RECEIPT, THE TURN, THE RESIDUE                         *)
  (* =================================================================== *)
  Lemma pread_ret_res (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) :
    (0 < length ws)%nat ->
    pread_ret g k v n ws -∗
    PT ∨ (∃ (ps0 cs0 : list nat) (s0 : unit) (J : list (bv 8)),
            ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage pipe_lm ps0 cs0 J⌝
            ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before pipe_lm ps0 cs0 s0 J))
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ pipe_Wb k s0).
  Proof using .
    intros Hws. iIntros "Hr". rewrite /pread_ret.
    iDestruct "Hr" as "[[#HT _] | [_ Hfacts]]"; [by iLeft |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0) "(#Hcs0 & #Hps0 & %Hbd & #Htlb & %Hrs)".
    iRight. iExists ps0, cs0, tt, (snd <$> (dl ++ ws)).
    iFrame "Hinp Hps0 Hcs0".
    iSplitR; [iPureIntro; rewrite length_fmap length_app Hdl; reflexivity |].
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_p_lm _ _ _) Hrs) |].
    rewrite -proc_before_p_lm /pipe_Wb. iFrame "Htlb".
  Qed.

  Lemma pturn0_gen (k : nat) :
    pturn_pre g k -∗
    (∃ v : era_pins, era_pin γ k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, era_pin γ k v ∗ gwc_ban pipe_lm pipe_params k v [] 0%nat).
  Proof using .
    rewrite /pturn_pre /PipeOut.pturn /eturn. iIntros "Hturn".
    iDestruct "Hturn" as (v) "(#Hpin & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin".
    rewrite /gwc_ban. iLeft. iExists [], [], tt, 0%nat.
    rewrite Nat.add_0_r /pipe_W. iFrame "Htn Hps Hcs HE".
    iPureIntro. exact (lm_wr_ban_round0 pipe_lm tt).
  Qed.

  Lemma pwc_rres_res (v : era_pins) (I : list (bv 8)) :
    pwc_rres v I -∗ gwc_rres pipe_lm pipe_params v I.
  Proof using .
    rewrite /pwc_rres /gwc_rres. iIntros "Hr".
    iDestruct "Hr" as (ps0 cs0) "(%Hrs & #Htlb & #Hps0 & #Hcs0)".
    iExists ps0, cs0, tt. iFrame "Hps0 Hcs0".
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_p_lm _ _ _) Hrs) |].
    rewrite -proc_before_p_lm /pipe_Wb. iFrame "Htlb".
  Qed.

  (* =================================================================== *)
  (*  4.  THE RECORD                                                      *)
  (* =================================================================== *)
  Definition pipe_link_gen : LinkRec Σ :=
    gen_link_inst pipe_lm pipe_params pipe_X pipe_X_tl (pipe_links g)
      (pipe_links_persistent g) pipe_links_gl pipe_X_dollar (pread_ret g)
      pread_ret_res (pturn_pre g) pturn0_gen pwc_rres pwc_rres_persistent
      pwc_rres_timeless pwc_rres_res 2%nat.
End pipe_link_gen.
