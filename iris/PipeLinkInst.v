(* ===================================================================== *)
(*  PipeLinkInst.v -- [LinkRec.LinkRec] AT THE PIPELINE APPLICATION.      *)
(*                                                                       *)
(*  Lane PIPE-LINK-INST (design app-pipe.md section 5.8, STOP B).         *)
(*  [PipeLinksLine]'s families and laws assembled into the record, so     *)
(*  that every console file above the links -- [UShPanic],                *)
(*  [UInitBanner], and through [StageRec] the round itself -- is          *)
(*  INSTANTIATED here rather than twinned.                                *)
(*                                                                       *)
(*  ONE RECORD, NOT TWO.  [FileLinkInst] carries [file_link_inst] (the    *)
(*  era's boot state under each family's own existential) AND             *)
(*  [file_link_inst_at s0] (the same record at a NAMED state), with       *)
(*  packing lemmas both ways.  The pipeline era has no state at all, so   *)
(*  the two coincide; the name kept is [pipe_link_inst_at], because that  *)
(*  is the one [UShRound.v] is stated at and the round's port is meant    *)
(*  to be a rename.                                                       *)
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
Require Import PipeDiscDec.
Require Import PipeOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import EchoLinks.
Require Import EchoLinksLine.
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Local Open Scope list_scope.

Section pipe_link_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context (γ : echo_fixed).
  Context `{HRg : !riscvGS Σ}.

  Definition pipe_link_inst_at : LinkRec Σ :=
    {| lk_T := echo_taint γ;
       lk_pin := era_pin γ;
       lk_epin := era_pin γ;
       lk_links := PipeLinks.pipe_links γ;
       lk_ab := pab;
       lk_apr := papr;
       lk_pan := fun _ => 3%nat;
       lk_exf := fun I => pexf_of (pline_at I);
       lk_exfb := fun I => pexfb (pline_at I);
       lk_noc := 2%nat;
       lk_ban := pwc_ban γ;
       lk_owed := pwc_owed γ;
       lk_sp := pwc_sp γ;
       lk_open := pwc_open γ;
       lk_blk := pwc_blk γ;
       lk_pro := pwc_pro γ;
       lk_sp_t := pwc_sp_t γ;
       lk_open_t := pwc_open_t γ;
       lk_line := pwc_line γ;
       lk_pr := pwc_pr γ;
       lk_lpr := pwc_lpr γ;
       lk_lend := pwc_lend γ;
       lk_rr := fun k v n ws => PipeLinks.pread_ret γ k v n ws;
       lk_rres := pwc_rres γ;
       lk_turn := pturn_pre γ;

       lk_T_pers := _;
       lk_T_tl := _;
       lk_links_pers := PipeLinks.pipe_links_persistent γ;
       lk_pin_pers := era_pin_persistent γ;
       lk_pin_tl := era_pin_timeless γ;
       lk_pin_agr := era_pin_agree γ;
       lk_epin_pers := era_pin_persistent γ;
       lk_epin_tl := era_pin_timeless γ;
       lk_epin_agr := era_pin_agree γ;
       lk_pin_epin := pi_pin_epin γ;
       lk_ban_tl := pwc_ban_timeless γ;
       lk_owed_tl := pwc_owed_timeless γ;
       lk_sp_tl := pwc_sp_timeless γ;
       lk_open_tl := pwc_open_timeless γ;
       lk_blk_tl := pwc_blk_timeless γ;
       lk_pro_tl := pwc_pro_timeless γ;
       lk_sp_t_tl := pwc_sp_t_timeless γ;
       lk_open_t_tl := pwc_open_t_timeless γ;
       lk_line_tl := pwc_line_timeless γ;
       lk_pr_tl := pwc_pr_timeless γ;
       lk_lpr_tl := pwc_lpr_timeless γ;
       lk_lend_tl := pwc_lend_timeless γ;
       lk_rres_pers := pwc_rres_persistent γ;
       lk_rres_tl := pwc_rres_timeless γ;

       lk_pr_0 := fun _ _ _ => eq_refl;
       lk_pr_1 := fun _ _ _ => eq_refl;
       lk_pr_S2 := fun _ _ _ _ => eq_refl;
       lk_lpr_0 := fun _ _ _ => eq_refl;
       lk_lpr_1 := fun _ _ _ => eq_refl;
       lk_lpr_2 := fun _ _ _ => eq_refl;
       lk_lpr_S3 := fun _ _ _ _ => eq_refl;

       lk_ban_taint := pwc_ban_taint γ;
       lk_owed_taint := pwc_owed_taint γ;
       lk_sp_taint := pwc_sp_taint γ;
       lk_open_taint := pwc_open_taint γ;
       lk_blk_taint := pwc_blk_taint γ;
       lk_pro_taint := pwc_pro_taint γ;
       lk_sp_t_taint := pwc_sp_t_taint γ;
       lk_open_t_taint := pwc_open_t_taint γ;
       lk_line_taint := pwc_line_taint γ;
       lk_lend_taint := pwc_lend_taint γ;

       lk_pro_owed := pwc_pro_owed γ;
       lk_blk_owed := pwc_blk_owed γ;
       lk_sp_t_sp := pwc_sp_t_sp γ;
       lk_open_t_open := pwc_open_t_open γ;
       lk_blk_0 := pwc_blk_0 γ;
       lk_line_of_blk0 := pwc_line_of_blk0 γ;
       lk_line_of_post := pwc_line_of_post γ;
       lk_line_of_pro := pwc_line_of_pro γ;
       lk_lend_of_blk0 := pwc_lend_of_blk0 γ;

       lk_ban_step := pban_step γ;
       lk_ban_owed := pwc_ban_owed γ;
       lk_ban_pro := pwc_ban_pro γ;
       lk_ban_done := pwc_ban_done γ;
       lk_ban_done_line := pwc_ban_done_line γ;
       lk_ban_inp := pwc_ban_inp γ;

       lk_prompt_dollar := pprompt_dollar γ;
       lk_prompt_space := pprompt_space γ;
       lk_prompt_dollar_ban := pprompt_dollar_ban γ;
       lk_read := pwc_read γ;
       lk_owed_read_taint := powed_read_taint γ;

       lk_blk_step := pblk_step γ;
       lk_blk_sp := pwc_blk_sp γ;

       lk_prompt_dollar_post := pprompt_dollar_post γ;
       lk_prompt_space_t := pprompt_space_t γ;
       lk_prompt_dollar_line := pprompt_dollar_line γ;
       lk_read_t := pwc_read_t γ;

       lk_ab_pan := fun I => pab_pan I;
       lk_ab_exf := fun I => pab_exf I;
       lk_apr_exf := fun I => papr_exf I;

       lk_ban_read_taint := pban_read_taint γ;
       lk_turn0 := pturn0 γ;
       lk_panic_done := pwc_panic_done γ;

       lk_pban := pwc_pban γ;
       lk_pdiag := pwc_pdiag γ;
       lk_pban_tl := pwc_pban_timeless γ;
       lk_pdiag_tl := pwc_pdiag_timeless γ;
       lk_pban_taint := pwc_pban_taint γ;
       lk_pdiag_taint := pwc_pdiag_taint γ;
       lk_pdiag_0 := pwc_pdiag_0 γ;
       lk_pban_of_ban_done := pwc_pban_of_ban_done γ;
       lk_pro_of_pban := pwc_pro_of_pban γ;
       lk_pdiag_step := ppdiag_step γ;
       lk_pdiag_done_1 := pwc_pdiag_done_1 γ;
    |}.

  (* =================================================================== *)
  (*  THE DEFINITIONAL CHECK (LINK-GEN's checker for a refactor's silent *)
  (*  failure mode, [LinkRec]'s [echo_inst_*]).  Every family the        *)
  (*  record exposes IS the landed [PipeLinksLine] family at this         *)
  (*  instance, BY CONVERSION.  If one of these ever needs a tactic, a    *)
  (*  statement moved.                                                    *)
  (* =================================================================== *)
  Lemma pipe_inst_T : lk_T pipe_link_inst_at = echo_taint γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_pin : lk_pin pipe_link_inst_at = era_pin γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_epin : lk_epin pipe_link_inst_at = era_pin γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_links :
    lk_links pipe_link_inst_at = PipeLinks.pipe_links γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_ab : lk_ab pipe_link_inst_at = pab.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_apr : lk_apr pipe_link_inst_at = papr.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_ban k v I i :
    lk_ban pipe_link_inst_at k v I i = pwc_ban γ k v I i.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_owed k v I :
    lk_owed pipe_link_inst_at k v I = pwc_owed γ k v I.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_blk k v I a i :
    lk_blk pipe_link_inst_at k v I a i = pwc_blk γ k v I a i.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_post k v I a :
    lk_post pipe_link_inst_at k v I a = pwc_post γ k v I a.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_panic k v I i :
    lk_panic pipe_link_inst_at k v I i = pwc_blk γ k v I 3%nat i.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_pr : lk_pr pipe_link_inst_at = pwc_pr γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_lpr : lk_lpr pipe_link_inst_at = pwc_lpr γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_lend k v I :
    lk_lend pipe_link_inst_at k v I = pwc_lend γ k v I.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_rres : lk_rres pipe_link_inst_at = pwc_rres γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_turn : lk_turn pipe_link_inst_at = pturn_pre γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_cred k I p :
    lk_cred pipe_link_inst_at k I p
    = (∃ v : era_pins, era_pin γ k v ∗ pwc_pr γ k v I p)%I.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_lcred k I p :
    lk_lcred pipe_link_inst_at k I p
    = (∃ v : era_pins, era_pin γ k v ∗ pwc_lpr γ k v I p)%I.
  Proof using . reflexivity. Qed.

  (* ---- the three NAMED alternatives, read at the instance.  [lk_pan]
          and [lk_noc] are echo's literals ([PEcho 3] / [PEcho 2]); the
          exec-failed one is NOT -- see [pipe_inst_exf_echo] below. ---- *)
  Lemma pipe_inst_pan I : lk_pan pipe_link_inst_at I = 3%nat.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_noc : lk_noc pipe_link_inst_at = 2%nat.
  Proof using . reflexivity. Qed.

  (* THE EXEC-FAILED CHILD'S BYTES ARE ECHO'S, at every line shape
     ([PipeDisc.alt_execL_echo]) -- which is what [UShRound]'s
     [file_exfb_echo] twin reads, and what makes [UkShDiag]'s printer the
     same law at either application.  The alternative's CODE is per-line
     and is not echo's 1. *)
  Lemma pipe_inst_exfb_echo I :
    lk_exfb pipe_link_inst_at I = EchoDisc.alt_execfail
    /\ (length (lk_exfb pipe_link_inst_at I) - 2)%nat = 17%nat.
  Proof using .
    cbn [lk_exfb pipe_link_inst_at]. rewrite (pexfb_execfail (pline_at I)).
    split; [reflexivity |]. by vm_compute.
  Qed.

End pipe_link_inst.

(* ===================================================================== *)
(*  THE [UShRound]-FACING LEMMAS (lane SKELETON's obligation table,       *)
(*  discharged by NAME at the pipeline instance; [FileLinkInst]'s         *)
(*  [file_Wcl_at] / [file_Wbl_at] section, verbatim one application over). *)
(* ===================================================================== *)
Section sh_round_facing.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context (γ : echo_fixed).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation PI := (pipe_link_inst_at γ).

  Definition pipe_Wcl_at (I : list (bv 8)) (p : nat) : iProp Σ :=
    lk_lcred PI (S gen_id) I p.

  Definition pipe_Wbl_at (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       lk_pin PI (S gen_id) v ∗ lk_ban PI (S gen_id) v I 0%nat)%I.

  Global Instance pipe_Wcl_at_timeless I p : Timeless (pipe_Wcl_at I p).
  Proof using . rewrite /pipe_Wcl_at. apply _. Qed.
  Global Instance pipe_Wbl_at_timeless I : Timeless (pipe_Wbl_at I).
  Proof using . rewrite /pipe_Wbl_at. apply _. Qed.

  (* ---- [UShRound]'s [Hwbl] ---- *)
  Lemma pipe_Hwbl (I : list (bv 8)) : ⊢ pipe_Wcl_at I 3%nat -∗ pipe_Wcl_at I 0%nat.
  Proof using .
    rewrite /pipe_Wcl_at. iApply (lk_lcred_blk_line PI (S gen_id) I).
  Qed.

  (* ---- [UShRound]'s [Hwbwc] ---- *)
  Lemma pipe_Hwbwc (I : list (bv 8)) : ⊢ pipe_Wbl_at I -∗ pipe_Wcl_at I 0%nat.
  Proof using .
    rewrite /pipe_Wcl_at /pipe_Wbl_at.
    iApply (lk_lcred_of_ban PI (S gen_id) I).
  Qed.

  (* ---- [UShRound]'s [Hcltaint], at the two-pin shape ---- *)
  Lemma pipe_Hcltaint (I : list (bv 8)) (p : nat) (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ echo_taint γ -∗ pipe_Wcl_at I p.
  Proof using .
    rewrite /pipe_Wcl_at. iApply (lk_lcred_taint PI (S gen_id) I p v).
  Qed.

  (* ---- [UShRound]'s [Hwc]: the read that completed a line ---- *)
  Lemma pipe_Hwc (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin γ (S gen_id) v -∗
      inp_lb v (I ++ l ++ [wl_nl]) -∗
      pipe_Wcl_at I 2%nat -∗ pipe_Wcl_at (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hl. rewrite /pipe_Wcl_at.
    iApply (lk_lcred_read PI (S gen_id) I l v Hl).
  Qed.

  (* ---- [UShRound]'s [Hwbr]: a read past a banner-owed boundary ---- *)
  Lemma pipe_Hwbr (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin γ (S gen_id) v -∗
      lk_rres PI v (I ++ l ++ [wl_nl]) -∗
      pipe_Wbl_at I -∗ echo_taint γ.
  Proof using .
    intros Hl. iIntros "#Hpin #Hres Hb". rewrite /pipe_Wbl_at.
    iDestruct "Hb" as (v') "[#Hpin' Hb]".
    iDestruct (lk_pin_agr PI (S gen_id) v v' with "Hpin Hpin'") as %<-.
    iApply (lk_ban_read_taint PI (S gen_id) v I l Hl with "Hb Hres").
  Qed.

End sh_round_facing.
