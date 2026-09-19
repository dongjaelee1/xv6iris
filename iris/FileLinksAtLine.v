(* ===================================================================== *)
(*  FileLinksAtLine.v -- THE BLOCK STEP, THE PROMPT BYTES AND THE READS   *)
(*  OF [FileLinksLine.v], AT A NAMED BOOT STATE                          *)
(*  (lane INIT-FILE, RULING H').                                         *)
(*                                                                       *)
(*  [FileLinksAt.v] hoists the era's boot state [s0] out of every         *)
(*  family's existential.  This file ports the laws that DRIVE those      *)
(*  families -- one byte of a block, the prompt's two bytes at the loose  *)
(*  and the tight shapes, the read of a completed line, the panic's exit  *)
(*  and the refutation of a read past an unwritten prompt -- to the       *)
(*  indexed twins.  The proofs are the ones of [FileLinksLine.v] with     *)
(*  [s0] read off the lemma's parameter instead of out of the            *)
(*  existential: the pure side conditions, the link applications and the  *)
(*  arithmetic are unchanged, and the taint arm is at EVERY [s0].         *)
(*                                                                       *)
(*  The point of the port is the head arm: where a law fires             *)
(*  [FileLinks.file_write_link_first], the witness it hands the link is   *)
(*  now the caller's OWN [s0], so the [f0_lb vf s0] that comes back --    *)
(*  and the family rebuilt around it -- is at the state the caller named. *)
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
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import EchoLinks.
Require Import FileLinksAt.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section file_links_at_line.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FPIN := (era_pin (fgn_echo g)).

  (* =================================================================== *)
  (*  1.  ONE BYTE OF A BLOCK                                             *)
  (* =================================================================== *)
  Lemma fblk_step_at (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) (b : bv 8) (Φ : iProp Σ) :
    fab I a !! i = Some b ->
    FPIN k v -∗ file_links g -∗ fwc_blk_at g s0 k v I a i -∗
    (fwc_blk_at g s0 k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_blk with "Hlk") as "#Hblk".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    destruct (fab_ok I a i b Hb) as [Hok Hfr].
    rewrite {1}/fwc_blk_at. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_blk_at_taint. }
    iDestruct "Hl" as (ps cs P)
      "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    pose proof (proj1 Hw) as Hwb.
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    pose proof (wr_blk_nonnil_f ps cs s0 I P Hwb) as Hne.
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct i as [| i'].
    - (* THE BLOCK-FIRST BYTE files the alternative *)
      cbn [blkcs_f]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v vf P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hne. }
      { exact Hr. }
      { rewrite Hn. lia. }
      { exact Hpin0. }
      { exact HP. }
      { rewrite -/(fline I). exact Hok. }
      { rewrite -/(fline I) -(fab_at I a _ Hok Hfr). exact Hb. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_blk_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs_f].
      replace (P + 1)%nat with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* every byte after it, at the choice list the first one extended *)
      cbn [blkcs_f].
      iApply ("Hw" $! k v vf (P + S i')%nat b ps (cs ++ [a]) s0 I Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { rewrite length_app Hn. cbn [length]. lia. }
      { exact (wr_blk_pin_snoc_f ps cs s0 I P a Hwb). }
      { pose proof (wr_blk_pending_pre_f ps cs s0 I P a Hwb Hok Hfr) as Hpre.
        rewrite /proc_stream_f (wr_blk_low_f ps cs s0 I P a Hwb)
                lookup_app_r; [| lia].
        replace (P + S i' - length (proc_before_f ps cs (Some s0) I))%nat
          with (S i') by lia.
        exact (prefix_lookup_Some _ _ _ _ Hb Hpre). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_blk_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs_f].
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* =================================================================== *)
  (*  2.  THE PROMPT'S TWO BYTES                                          *)
  (* =================================================================== *)
  (* the head arm's dollar: [file_write_link_first] at alternative 0, and
     the state it names is the caller's own *)
  Lemma fhead_dollar_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fhead_at g s0 k v I -∗
    (fwc_sp_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hh HΦ".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    rewrite /fhead_at.
    iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iDestruct "Hvf" as (vf) "#Hvf".
    iDestruct "Hpre" as "[%Hok Hty]".
    iApply ("Hfst" $! (S gen_id) v vf 0%nat b s0 Φ
              with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hty [HΦ]").
    { exact Hok. }
    { rewrite pro_alts_length. lia. }
    { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_at.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]";
      last by iRight.
    iLeft. iExists [0%nat], [], 1%nat.
    iFrame "Htn' Hps' Hcs' HE'".
    iSplitR; [iPureIntro; exact (wr_sp_f_head s0) |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0".
  Qed.

  (* ---- the prompt's dollar at the LOOSE boundary ---- *)
  Lemma fprompt_dollar_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_owed_at g s0 k v I -∗
    (fwc_sp_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_blk with "Hlk") as "#Hblk".
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_owed_at.
    iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_sp_at_taint. }
    { iApply (fhead_dollar_at s0 k v I b Φ Hb with "Hpin Hlk Hh HΦ"). }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct Hw as [Hw | Hw].
    - (* the round's prologue is open: the dollar files alternative 0 *)
      pose proof (wr_pro_dollar_f ps cs s0 I P Hw) as Hsp.
      destruct Hw as (Hpin0 & Hm & Hdv & Hr & Hnd & HP).
      iApply ("Hpro" $! k v vf P 0%nat b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
      { exact Hnd. } { exact HP. }
      { rewrite pro_alts_length. lia. }
      { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists (ps ++ [0%nat]), cs, (S P).
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* the round is settled: the dollar is the line's block-first byte *)
      pose proof (wr_blk_dollar_f ps cs s0 I P Hw) as Hsp.
      pose proof (wr_blk_nonnil_f ps cs s0 I P Hw) as Hne.
      pose proof Hw as (Hpin0 & Hm & Hdv & HP).
      iApply ("Hblk" $! k v vf P (fnoc_of (fline I)) b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hne. } { exact Hm. } { rewrite Hdv. lia. } { exact Hpin0. }
      { exact HP. }
      { rewrite -/(fline I). exact (fnoc_of_ok (fline I)). }
      { rewrite -/(fline I) (cont_fnoc _ (fline I)) Hb.
        exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, (cs ++ [fnoc_of (fline I)]), (S P).
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* ---- the space after it ---- *)
  Lemma fprompt_space_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    FPIN k v -∗ file_links g -∗ fwc_sp_at g s0 k v I -∗
    (fwc_open_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_sp_at. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_open_at_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct Hw as [Hop Hby].
    pose proof Hop as (Hpin0 & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v vf P b ps cs s0 I Φ
              with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
    { lia. } { exact Hpin0. } { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_open_at.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
      last by iRight.
    iLeft. iExists ps, cs, (S P).
    iFrame "Htn' Hps' Hcs' HE'".
    iSplitR; [iPureIntro; exact (wr_sp_open_f ps cs s0 I P (conj Hop Hby)) |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  Lemma fprompt_dollar_ban_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_ban_at g s0 k v I 0%nat -∗
    (fwc_sp_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (fprompt_dollar_at s0 k v I b Φ Hb with "Hpin Hlk [Hc] HΦ").
    (* the banner's credential read as the round's owing, at the same state *)
    rewrite /fwc_ban_at /fwc_owed_at.
    iDestruct "Hc" as "[H | [[_ H] | #HT]]";
      [| by iRight; iLeft | iRight; by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [wr_banp_f] in Hw. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. rewrite /fcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro. left.
    exact (wr_ban_pro_f ps cs s0 I P Hw).
  Qed.

  (* ---- the prompt at the TIGHT shapes ---- *)
  Lemma fprompt_dollar_post_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a : nat) (b : bv 8) (Φ : iProp Σ) :
    fapr I a -> b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗
    fwc_blk_at g s0 k v I a (length (fab I a) - 2)%nat -∗
    (fwc_sp_t_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Ha Hb. iIntros "#Hpin #Hlk Hc HΦ".
    pose proof (fab_len_ge2 I a Ha) as Hlen.
    assert (Hby : fab I a !! (length (fab I a) - 2)%nat = Some b)
      by (rewrite Hb; exact (fab_dollar I a Ha)).
    iApply (fblk_step_at s0 k v I a (length (fab I a) - 2)%nat b Φ Hby
              with "Hpin Hlk Hc [HΦ]").
    iIntros "Hc". iApply "HΦ".
    replace (S (length (fab I a) - 2))%nat
      with (length (fab I a) - 1)%nat by lia.
    (* the block's last byte closes the line at the same state *)
    rewrite /fwc_blk_at /fwc_sp_t_at.
    iDestruct "Hc" as "[H | #HT]"; [| by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    assert (Hbc : blkcs_f cs a (length (fab I a) - 1)%nat = cs ++ [a]).
    { destruct (length (fab I a) - 1)%nat as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]), (P + (length (fab I a) - 1))%nat.
    rewrite /fcur. iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (wr_blk_sp_f ps cs s0 I P a Hw Ha).
  Qed.

  Lemma fprompt_space_t_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    FPIN k v -∗ file_links g -∗ fwc_sp_t_at g s0 k v I -∗
    (fwc_open_t_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_sp_t_at. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_open_t_at_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct Hw as [[Hop Hby] Htl].
    pose proof Hop as (Hpin0 & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v vf P b ps cs s0 I Φ
              with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
    { lia. } { exact Hpin0. } { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_open_t_at.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
      last by iRight.
    iLeft. iExists ps, cs, (S P).
    iFrame "Htn' Hps' Hcs' HE'".
    iSplitR;
      [iPureIntro;
       exact (wr_sp_open_t_f ps cs s0 I P (conj (conj Hop Hby) Htl)) |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  Lemma fprompt_dollar_line_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_line_at g s0 k v I -∗
    (fwc_sp_t_at g s0 k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    rewrite {1}/fwc_line_at. iDestruct "Hc" as "[Hc | Hc]"; last first.
    { iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (fprompt_dollar_post_at s0 k v I a b Φ Ha Hb
                with "Hpin Hlk Hc HΦ"). }
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_pro_at. iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_sp_t_at_taint. }
    { (* the era's head: the dollar is its first byte, and it lands TIGHT *)
      rewrite /fhead_at.
      iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iDestruct "Hvf" as (vf) "#Hvf".
      iDestruct "Hpre" as "[%Hok Hty]".
      iApply ("Hfst" $! (S gen_id) v vf 0%nat b s0 Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hty [HΦ]").
      { exact Hok. }
      { rewrite pro_alts_length. lia. }
      { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_t_at.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]";
        last by iRight.
      iLeft. iExists [0%nat], [], 1%nat.
      iFrame "Htn' Hps' Hcs' HE'".
      iSplitR.
      { iPureIntro. split; [exact (wr_sp_f_head s0) |].
        rewrite /wr_tail_f. cbn [length pro_idx_f]. by vm_compute. }
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0". }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    pose proof (wr_pro_dollar_t_f ps cs s0 I P Hw) as Hsp.
    destruct Hw as (Hpin0 & Hm & Hdv & Hr & Hnd & HP).
    iApply ("Hpro" $! k v vf P 0%nat b ps cs s0 I Φ
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
    { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
    { exact Hnd. } { exact HP. }
    { rewrite pro_alts_length. lia. }
    { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_t_at.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
      last by iRight.
    iLeft. iExists (ps ++ [0%nat]), cs, (S P).
    iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* =================================================================== *)
  (*  3.  THE READS                                                       *)
  (* =================================================================== *)
  (* ---- the read of a completed line ---- *)
  Lemma fwc_read_at (s0 : fstate) (k : nat) (v : era_pins)
      (I l : list (bv 8)) :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ fwc_open_at g s0 k v I -∗
    fwc_owed_at g s0 k v (I ++ l ++ [wl_nl]).
  Proof using .
    intros Hl. iIntros "#HE' Hc". rewrite /fwc_open_at /fwc_owed_at.
    iDestruct "Hc" as "[H | H]"; [| by iRight; iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & _ & Hf)".
    iLeft. iExists ps, cs, P. rewrite /fcur.
    iFrame "Htn Hps Hcs HE' Hf". iPureIntro. right.
    exact (wr_open_read_f ps cs s0 I P l Hw Hl).
  Qed.

  Lemma fwc_read_t_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a : nat) (l : list (bv 8)) :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ fwc_open_t_at g s0 k v I -∗
    fwc_blk_at g s0 k v (I ++ l ++ [wl_nl]) a 0%nat.
  Proof using .
    intros Hl. iIntros "#HE' Hc". rewrite /fwc_open_t_at /fwc_blk_at.
    iDestruct "Hc" as "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & _ & Hf)".
    iLeft. iExists ps, cs, P. cbn [blkcs_f]. rewrite Nat.add_0_r.
    iFrame "Htn Hps Hcs HE' Hf". iPureIntro.
    exact (wr_open_read_t_f ps cs s0 I P l Hw Hl).
  Qed.

  (* ---- the panic's five bytes leave the next round's banner ---- *)
  Lemma fwc_panic_done_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) :
    fwc_blk_at g s0 k v I (fpan_of (fline I))
      (length (fab I (fpan_of (fline I)))) -∗ fwc_ban_at g s0 k v I 0%nat.
  Proof using .
    rewrite /fwc_blk_at /fwc_ban_at.
    iIntros "[H | H]"; [| by iRight; iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    assert (Hbc : blkcs_f cs (fpan_of (fline I))
                    (length (fab I (fpan_of (fline I))))
                  = cs ++ [fpan_of (fline I)]).
    { rewrite (fab_pan I) alt_panic_len5. reflexivity. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [fpan_of (fline I)]),
      (P + length (fab I (fpan_of (fline I))))%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE Hf". iPureIntro. cbn [wr_banp_f].
    exact (wr_blk_ban_f ps cs s0 I P Hw).
  Qed.

  (* ---- a read past a boundary whose prompt is unwritten is the taint ---- *)
  Lemma fowed_read_taint_at (s0 : fstate) (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    fwc_owed_at g s0 k v I -∗ fread_ret g k v n ws -∗ FT.
  Proof using .
    intros HIn Hws. iIntros "Hc Hr".
    rewrite /fread_ret.
    iDestruct "Hr" as "[[#HT _] | [Hdlr Hfacts]]"; [iExact "HT" |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & %Hboots & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0 vf sr)
      "(#Hcs0 & #Hps0 & #Hvf & #Hf0 & %Hbd & #Htlb & %Hrs)".
    set (J := (snd <$> (dl ++ ws))%list).
    assert (Hlen : length J = (n + length ws)%nat).
    { rewrite /J length_fmap length_app Hdl. reflexivity. }
    rewrite /fwc_owed_at.
    iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last by iExact "HT".
    - iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf']".
      iDestruct "Hvf'" as (vf') "[#Hvf' #Hf0']".
      iDestruct (file_era_pin_agree with "Hvf' Hvf") as %<-.
      iDestruct (f0_lb_agree with "Hf0' Hf0") as %<-.
      iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
      iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iDestruct (inp_lb_cmp with "HE Hinp") as %Hic.
      iExFalso. iPureIntro.
      assert (HI : I `prefix_of` J).
      { destruct Hic as [Hc | Hc]; [exact Hc |].
        exfalso. apply prefix_length in Hc. lia. }
      assert (Hne : I <> J) by (intros Hq; rewrite Hq Hlen in HIn; lia).
      exact (wr_owed_read_refute_f ps cs ps0 cs0 s0 I J P Hw HI Hne Hrs
               Hpsc Hcsc Hle).
    - rewrite /fhead_at.
      iDestruct "Hh" as "(-> & %Hk & Htn & #Hps & #Hcs & #HE & _ & _)".
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iExFalso. iPureIntro.
      assert (HI : ([] : list (bv 8)) `prefix_of` J) by apply prefix_nil.
      assert (Hne : ([] : list (bv 8)) <> J).
      { intros Hq. rewrite -Hq in Hlen. cbn [length] in Hlen.
        cbn [length] in HIn. lia. }
      refine (wr_owed_read_refute_f [] [] ps0 cs0 sr [] J 0%nat _ HI Hne Hrs
                ltac:(left; apply prefix_nil) ltac:(left; apply prefix_nil)
                ltac:(lia)).
      left. rewrite /wr_pro_f. split_and!.
      + exact (pro_pin_f_nil _ _).
      + exact rest_of_nil.
      + by rewrite nlines_nil.
      + by left.
      + rewrite nlines_nil. cbn [pro_idx_f pro_from].
        rewrite -pro_fail_0. exact (pro_done_fail 0%nat).
      + rewrite /proc_stream_f proc_before_f_nil pending_at_f_nil.
        by cbn [app pro_of length].
  Qed.

End file_links_at_line.
