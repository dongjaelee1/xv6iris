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
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
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
Require Import PipeBoth.      (* SH-PIPE-ROUND-4: the WIDENED line credential *)
Require Import EchoLinks.
Require Import EchoLinksLine.
Require Import LinkRec.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Local Open Scope list_scope.

Section pipe_link_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  (* THE RECORD IS THE GENERIC ONE ([GenLinksLine.gen_link_inst]) at the
     pipeline's parameters ([PipeLinksLine.pipe_params]: state [unit],
     witness [emp], no head), with the terminal round's arm on the line
     credential ([PipeBoth.pipe_X]) and its exit as the arm's prompt
     step, the links' entailment of the generic interface, the read
     receipt, the turn and the reader's residue read at the generic
     shapes, and the no-command alternative [PEcho 2]. *)
  Definition pipe_link_inst_at : LinkRec Σ :=
    gen_link_inst pipe_lm (pipe_params g) (pipe_X g) (pipe_X_timeless g)
      (pipe_links g) (pipe_links_persistent g) (pipe_links_gl g)
      (pipe_X_dollar g) (pread_ret g) (pread_ret_res g) (pturn_pre g)
      (pturn0_gen g) pwc_rres pwc_rres_persistent pwc_rres_timeless
      (pwc_rres_res g) 2%nat.

  (* =================================================================== *)
  (*  THE DEFINITIONAL CHECK (LINK-GEN's checker for a refactor's silent *)
  (*  failure mode, [LinkRec]'s [echo_inst_*]).  Every family the        *)
  (*  record exposes IS the [PipeLinksLine] family at this instance, BY   *)
  (*  CONVERSION -- the pipeline's names are abbreviations of the generic *)
  (*  families.  The two pure fields are the model's ([pab_lm], [papr_lm]  *)
  (*  bridge them; [pab] decides admissibility where the model's [lm_ab]  *)
  (*  does, so the block IS [pab] pointwise).                             *)
  (* =================================================================== *)
  Lemma pipe_inst_T : lk_T pipe_link_inst_at = echo_taint γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_pin : lk_pin pipe_link_inst_at = era_pin γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_epin : lk_epin pipe_link_inst_at = era_pin γ.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_links :
    lk_links pipe_link_inst_at = PipeLinks.pipe_links g.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_ab : lk_ab pipe_link_inst_at = pab.
  Proof using .
    apply functional_extensionality; intro I.
    apply functional_extensionality; intro a.
    symmetry. exact (pab_lm I a).
  Qed.
  Lemma pipe_inst_apr I a : lk_apr pipe_link_inst_at I a <-> papr I a.
  Proof using . symmetry. exact (papr_lm I a). Qed.
  Lemma pipe_inst_ban k v I i :
    lk_ban pipe_link_inst_at k v I i = pwc_ban g k v I i.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_owed k v I :
    lk_owed pipe_link_inst_at k v I = pwc_owed g k v I.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_blk k v I a i :
    lk_blk pipe_link_inst_at k v I a i = pwc_blk g k v I a i.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_post k v I a :
    lk_post pipe_link_inst_at k v I a = pwc_post g k v I a.
  Proof using .
    rewrite /lk_post /pwc_post.
    cbn [lk_blk lk_ab pipe_link_inst_at gen_link_inst gK pipe_params].
    by rewrite -pab_lm.
  Qed.
  Lemma pipe_inst_panic k v I i :
    lk_panic pipe_link_inst_at k v I i = pwc_blk g k v I 3%nat i.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_pr : lk_pr pipe_link_inst_at = pwc_pr g.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_lpr : lk_lpr pipe_link_inst_at = pwc_lpr2 g.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_lend k v I :
    lk_lend pipe_link_inst_at k v I = pwc_lend g k v I.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_rres : lk_rres pipe_link_inst_at = pwc_rres.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_turn : lk_turn pipe_link_inst_at = pturn_pre g.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_cred k I p :
    lk_cred pipe_link_inst_at k I p
    = (∃ v : era_pins, era_pin γ k v ∗ pwc_pr g k v I p)%I.
  Proof using . reflexivity. Qed.
  Lemma pipe_inst_lcred k I p :
    lk_lcred pipe_link_inst_at k I p
    = (∃ v : era_pins, era_pin γ k v ∗ pwc_lpr2 g k v I p)%I.
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
    cbn [lk_exfb pipe_link_inst_at gen_link_inst gK pipe_params lmh_exfb pipe_hooks].
    rewrite (pexfb_execfail (pline_at I)).
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
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did -- and
     [pipe_link_inst_at] takes the WHOLE fixed part. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation PI := (pipe_link_inst_at g).

  Definition pipe_Wcl_at (I : list (bv 8)) (p : nat) : iProp Σ :=
    lk_lcred PI (S gen_id) I p.

  Definition pipe_Wbl_at (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       lk_pin PI (S gen_id) v ∗ lk_ban PI (S gen_id) v I 0%nat)%I.

  (* NAME THE LEAF, do not search (upstream's leaf-instance pass). *)
  Global Instance pipe_Wcl_at_timeless I p : Timeless (pipe_Wcl_at I p).
  Proof using . rewrite /pipe_Wcl_at. apply lk_lcred_timeless. Qed.
  Global Instance pipe_Wbl_at_timeless I : Timeless (pipe_Wbl_at I).
  Proof using .
    rewrite /pipe_Wbl_at. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply lk_pin_tl | apply lk_ban_tl].
  Qed.

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
