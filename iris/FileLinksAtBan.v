(* ===================================================================== *)
(*  FileLinksAtBan.v -- THE BANNER AND THE STRUCTURAL CONVERSIONS OF      *)
(*  [FileLinksLine.v], AT A NAMED BOOT STATE (lane INIT-FILE, RULING H'). *)
(*                                                                       *)
(*  [FileLinksAt.v] hoisted the era's boot state [s0] out of every        *)
(*  family's existential and proved the two packings.  THIS FILE PORTS    *)
(*  THE LAWS: the loose-to-tight conversions ([fwc_pro_owed_at],          *)
(*  [fwc_blk_owed_at], [fwc_sp_t_sp_at], [fwc_open_t_open_at]), the line  *)
(*  and lend readings of a block, the banner's readings                   *)
(*  ([fwc_ban_pro_at] ... [fwc_ban_inp_at]), /init's banner step          *)
(*  [fban_step_at], the era's turn [fturn0_at], and the refutation        *)
(*  [fban_read_taint_at].                                                 *)
(*                                                                       *)
(*  Each statement is its [FileLinksLine] original with [s0] moved from   *)
(*  under the existential to a PARAMETER, and each proof is the original  *)
(*  with the [s0] binder dropped from every destruct and every witness.   *)
(*  The taint arm is unchanged and lives at EVERY [s0].                   *)
(*                                                                       *)
(*  WHAT THE ROUND ACTUALLY NEEDS is at the bottom: [fban_step_at] keeps  *)
(*  the name that [FileLinksLine.fban_step] loses -- the head branch      *)
(*  fires [FileLinks.file_write_link_first] at the lemma's OWN [s0], so   *)
(*  the [f0_lb] it hands back is at that state -- and [fban_at_f0w]       *)
(*  reads it off again, the head arm having been refuted by its index.    *)
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
Require Import FileLinksAt.
Require Import EchoLinks.
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Local Open Scope list_scope.

Section file_links_at_ban.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FPIN := (era_pin (fgn_echo g)).

  (* =================================================================== *)
  (*  1.  THE LOOSE SHAPES AND THE TIGHT ONES                             *)
  (* =================================================================== *)
  Lemma fwc_pro_owed_at (s0 : fstate) k v I :
    fwc_pro_at g s0 k v I -∗ fwc_owed_at g s0 k v I.
  Proof using .
    rewrite /fwc_pro_at /fwc_owed_at.
    iIntros "[H | [H | H]]"; [| by iRight; iLeft | by iRight; iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]".
    iLeft. iExists ps, cs, P. iFrame "Hc". iPureIntro. by left.
  Qed.

  Lemma fwc_blk_owed_at (s0 : fstate) k v I a :
    fwc_blk_at g s0 k v I a 0%nat -∗ fwc_owed_at g s0 k v I.
  Proof using .
    rewrite /fwc_blk_at /fwc_owed_at.
    iIntros "[H | H]"; [| by iRight; iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [blkcs_f]. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. rewrite /fcur. iFrame "Htn Hps Hcs HE Hf".
    iPureIntro. right. exact (proj1 Hw).
  Qed.

  Lemma fwc_sp_t_sp_at (s0 : fstate) k v I :
    fwc_sp_t_at g s0 k v I -∗ fwc_sp_at g s0 k v I.
  Proof using .
    rewrite /fwc_sp_t_at /fwc_sp_at. iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]".
    iLeft. iExists ps, cs, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma fwc_open_t_open_at (s0 : fstate) k v I :
    fwc_open_t_at g s0 k v I -∗ fwc_open_at g s0 k v I.
  Proof using .
    rewrite /fwc_open_t_at /fwc_open_at. iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs P) "[%Hw Hc]".
    iLeft. iExists ps, cs, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma fwc_blk_0_at (s0 : fstate) k v I a a' :
    fwc_blk_at g s0 k v I a 0%nat -∗ fwc_blk_at g s0 k v I a' 0%nat.
  Proof using .
    rewrite /fwc_blk_at. cbn [blkcs_f]. iIntros "H". iExact "H".
  Qed.

  Lemma fwc_line_of_blk0_at (s0 : fstate) k v I a :
    fwc_blk_at g s0 k v I a 0%nat -∗ fwc_line_at g s0 k v I.
  Proof using .
    iIntros "Hc". rewrite /fwc_line_at. iRight.
    iExists (fnoc_of (fline I)). iSplitR; [iPureIntro; exact (fapr_noc I) |].
    rewrite (fab_noc I) EchoLinks.wr_prompt_len.
    cbn [Nat.sub]. iApply (fwc_blk_0_at with "Hc").
  Qed.

  Lemma fwc_line_of_post_at (s0 : fstate) k v I a :
    fapr I a ->
    fwc_blk_at g s0 k v I a (length (fab I a) - 2)%nat -∗
    fwc_line_at g s0 k v I.
  Proof using .
    intros Ha. iIntros "Hc". rewrite /fwc_line_at. iRight. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma fwc_line_of_pro_at (s0 : fstate) k v I :
    fwc_pro_at g s0 k v I -∗ fwc_line_at g s0 k v I.
  Proof using . iIntros "Hc". rewrite /fwc_line_at. by iLeft. Qed.

  Lemma fwc_lend_of_blk0_at (s0 : fstate) k v I a :
    fwc_blk_at g s0 k v I a 0%nat -∗ fwc_lend_at g s0 k v I.
  Proof using .
    rewrite /fwc_blk_at /fwc_lend_at. cbn [blkcs_f].
    iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    rewrite Nat.add_0_r. iLeft. iExists ps, cs, P.
    rewrite /fcur. by iFrame "Htn Hps Hcs HE Hf".
  Qed.

  Lemma fwc_blk_sp_at (s0 : fstate) k v I a :
    fapr I a ->
    fwc_blk_at g s0 k v I a (length (fab I a) - 1)%nat -∗
    fwc_sp_t_at g s0 k v I.
  Proof using .
    intros Ha. rewrite /fwc_blk_at /fwc_sp_t_at.
    iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    pose proof (fab_len_ge2 I a Ha) as Hlen.
    assert (Hbc : blkcs_f cs a (length (fab I a) - 1)%nat = cs ++ [a]).
    { destruct (length (fab I a) - 1)%nat as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]), (P + (length (fab I a) - 1))%nat.
    rewrite /fcur. iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (wr_blk_sp_f ps cs s0 I P a Hw Ha).
  Qed.

  (* =================================================================== *)
  (*  2.  THE BANNER'S READINGS                                           *)
  (* =================================================================== *)
  Lemma fwc_ban_pro_at (s0 : fstate) k v I :
    fwc_ban_at g s0 k v I 0%nat -∗ fwc_pro_at g s0 k v I.
  Proof using .
    rewrite /fwc_ban_at /fwc_pro_at.
    iIntros "[H | [[_ H] | H]]"; [| by iRight; iLeft | by iRight; iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [wr_banp_f] in Hw. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. rewrite /fcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (wr_ban_pro_f ps cs s0 I P Hw).
  Qed.

  Lemma fwc_ban_owed_at (s0 : fstate) k v I :
    fwc_ban_at g s0 k v I 0%nat -∗ fwc_owed_at g s0 k v I.
  Proof using .
    iIntros "Hc". iApply fwc_pro_owed_at. iApply (fwc_ban_pro_at with "Hc").
  Qed.

  Lemma fwc_ban_done_pro_at (s0 : fstate) k v I :
    fwc_ban_at g s0 k v I (length u_banner) -∗ fwc_pro_at g s0 k v I.
  Proof using .
    rewrite /fwc_ban_at /fwc_pro_at.
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18.
    iIntros "[H | [[%Hq _] | H]]"; [| discriminate Hq | by iRight; iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [wr_banp_f] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + 18)%nat. rewrite /fcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    pose proof (wr_ban_done_f ps' cs s0 I P Hw) as H. by rewrite H18 in H.
  Qed.

  Lemma fwc_ban_done_at (s0 : fstate) k v I :
    fwc_ban_at g s0 k v I (length u_banner) -∗ fwc_owed_at g s0 k v I.
  Proof using .
    iIntros "Hc". iApply fwc_pro_owed_at.
    iApply (fwc_ban_done_pro_at with "Hc").
  Qed.

  Lemma fwc_ban_done_line_at (s0 : fstate) k v I :
    fwc_ban_at g s0 k v I (length u_banner) -∗ fwc_line_at g s0 k v I.
  Proof using .
    iIntros "Hc". iApply fwc_line_of_pro_at.
    iApply (fwc_ban_done_pro_at with "Hc").
  Qed.

  Lemma fwc_ban_inp_at (s0 : fstate) k v I :
    fwc_ban_at g s0 k v I 0%nat -∗
    fwc_ban_at g s0 k v I 0%nat ∗ ((inp_lb v I ∗ ⌜rest_of I = []⌝) ∨ FT).
  Proof using .
    rewrite /fwc_ban_at.
    iIntros "[H | [[%Hi H] | #H]]"; last first.
    { iSplitR; [iRight; by iRight | iRight; iExact "H"]. }
    { iDestruct "H" as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iSplitR "".
      - iRight. iLeft. iSplitR; [by iPureIntro |].
        rewrite /fhead_at. by iFrame "Htn Hps Hcs HE Hvf Hpre".
      - iLeft. subst I. iFrame "HE". iPureIntro. exact rest_of_nil. }
    iDestruct "H" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    cbn [wr_banp_f] in Hw.
    iSplitL "Htn".
    - iLeft. iExists ps, cs, P. by iFrame "Htn Hps Hcs HE Hf".
    - iLeft. iFrame "HE". iPureIntro. exact (proj1 (proj2 Hw)).
  Qed.

  (* =================================================================== *)
  (*  3.  /init's BANNER STEP, AT THE NAMED STATE                         *)
  (* =================================================================== *)
  Lemma fban_step_at (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      (i : nat) (b : bv 8) (Φ : iProp Σ) :
    u_banner !! i = Some b ->
    FPIN k v -∗ file_links g -∗ fwc_ban_at g s0 k v I i -∗
    (fwc_ban_at g s0 k v I (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_ban_at.
    iDestruct "Hc" as "[Hl | [[%Hi0 Hh] | #HT]]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_ban_at_taint. }
    { (* THE ERA'S HEAD: the first byte FILES the boot state *)
      subst i. rewrite /fhead_at.
      iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iDestruct "Hvf" as (vf) "#Hvf".
      iDestruct "Hpre" as "[%Hok Hty]".
      iApply ("Hfst" $! (S gen_id) v vf 3%nat b s0 Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hty [HΦ]").
      { exact Hok. }
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_ban_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]";
        last by (iRight; iRight).
      iLeft. iExists [3%nat], [], 0%nat.
      rewrite Nat.add_0_l. iFrame "Htn' Hps' Hcs' HE'".
      iSplitR.
      { iPureIntro. cbn [wr_banp_f]. exists []. split; [reflexivity |].
        exact (wr_ban_round0_f s0). }
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0". }
    iDestruct "Hl" as (ps cs P)
      "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    destruct i as [| i'].
    - (* the first byte FILES the banner letter *)
      cbn [wr_banp_f] in Hw.
      pose proof (wr_ban_pro_f ps cs s0 I P Hw) as Hpr.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      destruct Hpr as (_ & _ & _ & _ & Hnd & HP).
      rewrite Nat.add_0_r.
      rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
      iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hpro" $! k v vf P 3%nat b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin0. }
      { exact Hnd. }
      { exact HP. }
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_ban_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by (iRight; iRight).
      iLeft. iExists (ps ++ [3%nat]), cs, P.
      replace (P + 1)%nat with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE'".
      iSplitR; [iPureIntro; cbn [wr_banp_f]; by exists ps |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* every later byte is an ordinary write of the filed letter *)
      cbn [wr_banp_f] in Hw. destruct Hw as (ps' & -> & Hw).
      pose proof (wr_ban_byte_f ps' cs s0 I P (S i') b Hw Hb) as Hby.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
      iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hw" $! k v vf (P + S i')%nat b (ps' ++ [3%nat]) cs s0 I Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { lia. }
      { exact (pro_pin_f_mono ps' (ps' ++ [3%nat]) cs I ltac:(by eexists)
                 Hpin0). }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_ban_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by (iRight; iRight).
      iLeft. iExists (ps' ++ [3%nat]), cs, P.
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'".
      iSplitR; [iPureIntro; cbn [wr_banp_f]; by exists ps' |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* ---- and the name the banner leaves behind ---- *)
  Lemma fban_at_f0w (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      (i : nat) :
    fwc_ban_at g s0 k v I (S i) -∗
    fwc_ban_at g s0 k v I (S i) ∗ (FileLinksLine.f0w g k s0 ∨ FT).
  Proof using .
    rewrite {1}/fwc_ban_at.
    iIntros "[H | [[%Hq _] | #HT]]"; [| discriminate Hq |].
    - iDestruct "H" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      iSplitL "Htn".
      + iLeft. iExists ps, cs, P. by iFrame "Htn Hps Hcs HE Hf".
      + iLeft. iExact "Hf".
    - iSplitR.
      + by iApply fwc_ban_at_taint.
      + iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  4.  THE ERA'S TURN, AT THE NAMED STATE                              *)
  (* =================================================================== *)
  Definition fturn_pre_at (s0 : fstate) (k : nat) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ FileOut.fturn g k ∗ f0pre_at g s0)%I.

  Lemma fturn0_at (s0 : fstate) (k : nat) :
    fturn_pre_at s0 k -∗
    (∃ v : era_pins, FPIN k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, FPIN k v ∗ fwc_ban_at g s0 k v [] 0%nat).
  Proof using .
    rewrite /fturn_pre_at /FileOut.fturn.
    iIntros "(%Hk & Ht & Hpre)".
    iDestruct "Ht" as (v vf)
      "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin". rewrite /fwc_ban_at. iRight. iLeft.
    iSplitR; [by iPureIntro |]. rewrite /fhead_at.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE Hpre". iExists vf. iExact "Hvf".
  Qed.

  (* =================================================================== *)
  (*  5.  A READ PAST THE BANNER IS THE TAINT                             *)
  (* =================================================================== *)
  Lemma fban_read_taint_at (s0 : fstate) (k : nat) (v : era_pins)
      (I l : list (bv 8)) :
    wl_nl ∉ l ->
    fwc_ban_at g s0 k v I 0%nat -∗ fwc_rres g v (I ++ l ++ [wl_nl]) -∗ FT.
  Proof using .
    intros Hnl. iIntros "Hc #Hres".
    rewrite /FileLinksLine.fwc_rres.
    iDestruct "Hres" as (ps0 cs0 sr) "(%Hrs & #Htlb & #Hps0 & #Hcs0 & #Hf0)".
    assert (Hpre : I `prefix_of` (I ++ l ++ [wl_nl])) by (by eexists).
    assert (Hne : I <> I ++ l ++ [wl_nl]).
    { intro Heq. apply (f_equal length) in Heq.
      rewrite !length_app length_cons in Heq. lia. }
    rewrite /fwc_ban_at.
    iDestruct "Hc" as "[Hl | [[_ Hh] | #HT]]"; last by iExact "HT".
    - iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      cbn [wr_banp_f] in Hw.
      iDestruct (f0w_agree with "Hf Hf0") as %<-.
      iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
      iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
      rewrite Nat.add_0_r.
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iExFalso. iPureIntro.
      exact (wr_owed_read_refute_f ps cs ps0 cs0 s0 I (I ++ l ++ [wl_nl]) P
               (or_introl (wr_ban_pro_f ps cs s0 I P Hw)) Hpre Hne Hrs
               Hpsc Hcsc Hle).
    - rewrite /fhead_at.
      iDestruct "Hh" as "(-> & %Hk & Htn & #Hps & #Hcs & #HE & _ & _)".
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      rewrite app_nil_l in Hle.
      iExFalso. iPureIntro.
      refine (wr_owed_read_refute_f [] [] ps0 cs0 sr [] (l ++ [wl_nl]) 0%nat
                _ ltac:(apply prefix_nil) _ Hrs
                ltac:(left; apply prefix_nil) ltac:(left; apply prefix_nil)
                ltac:(lia)).
      + left. rewrite /wr_pro_f. split_and!.
        * exact (pro_pin_f_nil _ _).
        * exact rest_of_nil.
        * by rewrite nlines_nil.
        * by left.
        * rewrite nlines_nil. cbn [pro_idx_f pro_from].
          rewrite -pro_fail_0. exact (pro_done_fail 0%nat).
        * rewrite /proc_stream_f proc_before_f_nil pending_at_f_nil.
          by cbn [app pro_of length].
      + intro Hq. apply (f_equal length) in Hq.
        rewrite length_app length_cons in Hq. cbn [length] in Hq. lia.
  Qed.

End file_links_at_ban.
