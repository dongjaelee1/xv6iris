(* ===================================================================== *)
(*  FileLinkGen.v -- THE FILE APPLICATION'S CONSOLE FAMILIES AS THE       *)
(*  GENERIC ONES (app-both milestone M2c, first cut).                    *)
(*                                                                       *)
(*  [GenLinksLine] at the file model: the taint is [file_taint], the pin  *)
(*  the era's echo-side pin, the writer's witness [f0w] (the boot-ledger  *)
(*  entry beside the era's file pin, at the console era), the reader's   *)
(*  the entry alone at an era, the head [fhead].  [FileLinks.file_links] *)
(*  entails the links interface (its laws carry the witness's two halves *)
(*  by name; the interface carries the witness), the read receipt        *)
(*  exposes the reader's residue, and the turn comes apart into the      *)
(*  generic banner-owed credential.  [file_link_gen] is then             *)
(*  [gen_link_inst] -- the record's ~60 laws at the file, from the       *)
(*  generic proofs.                                                      *)
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
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import LineModel.
Require Import LineModelLinks.
Require Import LineModelInst.
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import LinkRec.
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section file_link_gen.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FPIN := (era_pin (fgn_echo g)).

  (* =================================================================== *)
  (*  1.  THE PARAMETERS                                                  *)
  (* =================================================================== *)

  (* the reader's witness at an era: the boot-ledger entry beside the
     era's file pin, with no index pin ([FileLinksLine.f0bw] is it at the
     console era with the pin) *)
  Definition f0bwk (k : nat) (s0 : fstate) : iProp Σ :=
    (∃ vf : file_era, file_era_pin g k vf ∗ f0_bl vf s0)%I.

  Global Instance f0bwk_persistent k s : Persistent (f0bwk k s).
  Proof using . rewrite /f0bwk. apply _. Qed.
  Global Instance f0bwk_timeless k s : Timeless (f0bwk k s).
  Proof using . rewrite /f0bwk. apply _. Qed.

  Lemma f0bwk_agree (k : nat) (s s' : fstate) :
    f0bwk k s -∗ f0bwk k s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "H H'".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_bl_agree with "Hl Hl'").
  Qed.

  Lemma f0w_bwk (k : nat) (s : fstate) : f0w g k s -∗ f0bwk k s.
  Proof using .
    iIntros "[_ H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iExists vf. iFrame "Hp". iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma f0w_bwk0 (k : nat) (s : fstate) : f0w g k s -∗ f0bwk (S gen_id) s.
  Proof using .
    iIntros "[-> H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iExists vf. iFrame "Hp". iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma f0bw_bwk (k : nat) (s : fstate) : f0bw g k s -∗ f0bwk k s.
  Proof using . iIntros "[_ H]". iExact "H". Qed.

  (* the head's two readings *)
  Lemma fhead_cur (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead g k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using .
    rewrite /fhead. iIntros "(%HI & _ & Htn & #Hps & #Hcs & #HE & _ & _)".
    iFrame "Htn Hps Hcs HE". by iPureIntro.
  Qed.

  Lemma fhead_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead g k v I -∗ fhead g k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using .
    rewrite /fhead. iIntros "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iSplitL "Htn Hvf Hpre".
    - iFrame "Htn Hps Hcs HE Hvf Hpre". iSplitR; by iPureIntro.
    - iSplitR; [by iPureIntro |]. subst I. iExact "HE".
  Qed.

  Definition file_params : gen_params file_lm :=
    MkGP file_lm file_lm_laws file_hooks
      FT _ _
      FPIN _ _ (era_pin_agree (fgn_echo g))
      (f0w g) _ _
      f0bwk _ _ (S gen_id) f0w_bwk f0w_bwk0 f0bwk_agree
      (fhead g) _ fhead_cur fhead_inp.

  (* =================================================================== *)
  (*  2.  THE LINKS ENTAIL THE INTERFACE                                  *)
  (* =================================================================== *)
  Lemma file_links_gl : file_links g -∗ glinks file_lm file_params.
  Proof using .
    iIntros "#Hlk".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_blk with "Hlk") as "#Hblk".
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite /glinks. iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
    - (* W *)
      rewrite /gl_w. iIntros "!>" (k v P b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 #Hpin #Hf Htn #Hps #Hcs #HE HΦ".
      iDestruct "Hf" as "[%Hk Hvf]". iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hw" $! k v vf P b ps0 cs0 s0 I0 Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact H1. }
      { exact (proj2 (pro_pin_f_lm _ _ _) H2). }
      { rewrite proc_stream_f_lm. exact H3. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & _) | #HT]"; [iLeft | by iRight].
      by iFrame "Htn' Hps' Hcs' HE'".
    - (* BLK *)
      rewrite /gl_blk.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hf Htn #Hps #Hcs #HE HΦ".
      iDestruct "Hf" as "[%Hk Hvf]". iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hblk" $! k v vf P a b ps0 cs0 s0 I0 Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact H1. } { exact H2. } { exact H3. }
      { exact (proj2 (pro_pin_f_lm _ _ _) H4). }
      { rewrite proc_before_f_lm. exact H5. }
      { exact H6. }
      { rewrite /lm_abs -fstate_upto_lm in H8. exact H8. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & _) | #HT]"; [iLeft | by iRight].
      by iFrame "Htn' Hps' Hcs' HE'".
    - (* PRO *)
      rewrite /gl_pro.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hf Htn #Hps #Hcs #HE HΦ".
      iDestruct "Hf" as "[%Hk Hvf]". iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hpro" $! k v vf P a b ps0 cs0 s0 I0 Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact H1. } { exact H2. } { exact H3. }
      { exact (proj2 (pro_pin_f_lm _ _ _) H4). }
      { rewrite pro_idx_f_lm. exact H5. }
      { rewrite proc_stream_f_lm. exact H6. }
      { exact H7. } { exact H8. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & _) | #HT]"; [iLeft | by iRight].
      by iFrame "Htn' Hps' Hcs' HE'".
    - (* HEAD *)
      rewrite /gl_head.
      iIntros "!>" (k v I a b Φ) "%H1 %H2 #Hpin Hh HΦ".
      rewrite /fhead.
      iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iDestruct "Hvf" as (vf) "#Hvf".
      iDestruct "Hpre" as (s0) "(%Hok & Hty & Hbw)".
      iDestruct "Hbw" as "[_ Hbw]". iDestruct "Hbw" as (vf') "[#Hvf' #Hbl]".
      iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
      iApply ("Hfst" $! (S gen_id) v vf a b s0 Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hbl Hty [HΦ]").
      { exact Hok. } { exact H1. } { exact H2. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]"; [iLeft | by iRight].
      iExists s0. iFrame "Htn' Hps' Hcs' HE'".
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0".
    - (* TAINT *)
      rewrite /gl_taint. iIntros "!>" (k b Φ) "#HT HΦ".
      iApply ("Ht" $! k b Φ with "HT HΦ").
  Qed.

  (* =================================================================== *)
  (*  3.  THE READ RECEIPT, THE TURN, THE RESIDUE                         *)
  (* =================================================================== *)
  Lemma fread_ret_res (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) :
    (0 < length ws)%nat ->
    fread_ret g k v n ws -∗
    FT ∨ (∃ (ps0 cs0 : list nat) (s0 : fstate) (J : list (bv 8)),
            ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage file_lm ps0 cs0 J⌝
            ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before file_lm ps0 cs0 s0 J))
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ f0bwk k s0).
  Proof using .
    intros Hws. iIntros "Hr". rewrite /fread_ret.
    iDestruct "Hr" as "[[#HT _] | [_ Hfacts]]"; [by iLeft |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & %Hboots & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0 vf s0)
      "(#Hcs0 & #Hps0 & #Hvf & #Hf0 & %Hbd & #Htlb & %Hrs)".
    iRight. iExists ps0, cs0, s0, (snd <$> (dl ++ ws)).
    iFrame "Hinp Hps0 Hcs0".
    iSplitR; [iPureIntro; rewrite length_fmap length_app Hdl; reflexivity |].
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_f_lm _ _ _) Hrs) |].
    iSplitR; [rewrite -proc_before_f_lm; iExact "Htlb" |].
    iExists vf. iFrame "Hvf". iApply (f0_lb_bl with "Hf0").
  Qed.

  Lemma fturn0_gen (k : nat) :
    fturn_pre g k -∗
    (∃ v : era_pins, FPIN k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, FPIN k v ∗ gwc_ban file_lm file_params k v [] 0%nat).
  Proof using .
    rewrite /fturn_pre /FileOut.fturn_core.
    iIntros "(%Hk & Ht & Hpre)".
    iDestruct "Ht" as (v vf) "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin". rewrite /gwc_ban. iRight. iLeft.
    iSplitR; [by iPureIntro |]. rewrite /gH /file_params /fhead.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE Hpre". iExists vf. iExact "Hvf".
  Qed.

  Lemma fwc_rresw_res (v : era_pins) (I : list (bv 8)) :
    fwc_rresw g v I -∗ gwc_rres file_lm file_params v I.
  Proof using .
    rewrite /fwc_rresw /fwc_rres /gwc_rres. iIntros "[Hr _]".
    iDestruct "Hr" as (ps0 cs0 s0) "(%Hrs & #Htlb & #Hps0 & #Hcs0 & #Hbw)".
    iExists ps0, cs0, s0. iFrame "Hps0 Hcs0".
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_f_lm _ _ _) Hrs) |].
    iSplitR; [rewrite -proc_before_f_lm; iExact "Htlb" |].
    iApply (f0bw_bwk with "Hbw").
  Qed.

  (* =================================================================== *)
  (*  4.  THE RECORD                                                      *)
  (* =================================================================== *)
  Definition file_link_gen : LinkRec Σ :=
    gen_link_inst file_lm file_params (file_links g) (file_links_persistent g)
      file_links_gl (fread_ret g) fread_ret_res (fturn_pre g) fturn0_gen
      (fwc_rresw g) (fwc_rresw_persistent g) (fwc_rresw_timeless g)
      fwc_rresw_res fnoc.
End file_link_gen.
