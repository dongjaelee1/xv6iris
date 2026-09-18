(* ===================================================================== *)
(*  FileLinkInst.v -- [LinkRec.LinkRec] AT THE FILE APPLICATION.          *)
(*                                                                       *)
(*  Lane LINK-GEN-2.  [FileLinksLine]'s families and laws assembled into  *)
(*  the record, so that every console file above the links --             *)
(*  [UShPanic], [UInitBanner] and (once lane LINK-GEN-3's [StageRec]      *)
(*  lands) [UEchoOut] / [UShEchoPay] / [UShLine] / [UShRest] -- is        *)
(*  INSTANTIATED here rather than twinned.                                *)
(*                                                                       *)
(*  The record's echo instance is DEFINITIONAL; this one is not, and does *)
(*  not have to be: nothing above it recovers a landed FILE statement,    *)
(*  because there is none yet.  What it has to be is TOTAL -- every       *)
(*  field inhabited -- which is what makes the generic lemmas usable at   *)
(*  the file era by name.                                                *)
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
Require Import EchoLinksLine.
Require Import LinkRec.
Require Import StageRec.   (* the cursor / stage record *)
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Local Open Scope list_scope.

Section file_link_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Definition file_link_inst : LinkRec Σ :=
    {| lk_T := file_taint (fgn_cl g);
       lk_pin := era_pin (fgn_echo g);
       lk_epin := era_pin (fgn_echo g);
       lk_links := FileLinks.file_links g;
       lk_ab := fab;
       lk_apr := fapr;
       lk_pan := fun I => fpan_of (fline I);
       lk_exf := fun I => fexf_of (fline I);
       lk_exfb := fun I => fexfb (fline I);
       lk_noc := fnoc;
       lk_ban := fwc_ban g;
       lk_owed := fwc_owed g;
       lk_sp := fwc_sp g;
       lk_open := fwc_open g;
       lk_blk := fwc_blk g;
       lk_pro := fwc_pro g;
       lk_sp_t := fwc_sp_t g;
       lk_open_t := fwc_open_t g;
       lk_line := fwc_line g;
       lk_pr := fwc_pr g;
       lk_lpr := fwc_lpr g;
       lk_lend := fwc_lend g;
       lk_rr := fun k v n ws => FileLinks.fread_ret g k v n ws;
       lk_rres := fwc_rres g;
       lk_turn := fturn_pre g;

       lk_T_pers := _;
       lk_T_tl := _;
       lk_links_pers := FileLinks.file_links_persistent g;
       lk_pin_pers := era_pin_persistent (fgn_echo g);
       lk_pin_tl := era_pin_timeless (fgn_echo g);
       lk_pin_agr := era_pin_agree (fgn_echo g);
       lk_epin_pers := era_pin_persistent (fgn_echo g);
       lk_epin_tl := era_pin_timeless (fgn_echo g);
       lk_epin_agr := era_pin_agree (fgn_echo g);
       lk_pin_epin := fi_pin_epin g;
       lk_ban_tl := fwc_ban_timeless g;
       lk_owed_tl := fwc_owed_timeless g;
       lk_sp_tl := fwc_sp_timeless g;
       lk_open_tl := fwc_open_timeless g;
       lk_blk_tl := fwc_blk_timeless g;
       lk_pro_tl := fwc_pro_timeless g;
       lk_sp_t_tl := fwc_sp_t_timeless g;
       lk_open_t_tl := fwc_open_t_timeless g;
       lk_line_tl := fwc_line_timeless g;
       lk_pr_tl := fwc_pr_timeless g;
       lk_lpr_tl := fwc_lpr_timeless g;
       lk_lend_tl := fwc_lend_timeless g;
       lk_rres_pers := fwc_rres_persistent g;
       lk_rres_tl := fwc_rres_timeless g;

       lk_pr_0 := fun _ _ _ => eq_refl;
       lk_pr_1 := fun _ _ _ => eq_refl;
       lk_pr_S2 := fun _ _ _ _ => eq_refl;
       lk_lpr_0 := fun _ _ _ => eq_refl;
       lk_lpr_1 := fun _ _ _ => eq_refl;
       lk_lpr_2 := fun _ _ _ => eq_refl;
       lk_lpr_S3 := fun _ _ _ _ => eq_refl;

       lk_ban_taint := fwc_ban_taint g;
       lk_owed_taint := fwc_owed_taint g;
       lk_sp_taint := fwc_sp_taint g;
       lk_open_taint := fwc_open_taint g;
       lk_blk_taint := fwc_blk_taint g;
       lk_pro_taint := fwc_pro_taint g;
       lk_sp_t_taint := fwc_sp_t_taint g;
       lk_open_t_taint := fwc_open_t_taint g;
       lk_line_taint := fwc_line_taint g;
       lk_lend_taint := fwc_lend_taint g;

       lk_pro_owed := fwc_pro_owed g;
       lk_blk_owed := fwc_blk_owed g;
       lk_sp_t_sp := fwc_sp_t_sp g;
       lk_open_t_open := fwc_open_t_open g;
       lk_blk_0 := fwc_blk_0 g;
       lk_line_of_blk0 := fwc_line_of_blk0 g;
       lk_line_of_post := fwc_line_of_post g;
       lk_line_of_pro := fwc_line_of_pro g;
       lk_lend_of_blk0 := fwc_lend_of_blk0 g;

       lk_ban_step := fban_step g;
       lk_ban_owed := fwc_ban_owed g;
       lk_ban_pro := fwc_ban_pro g;
       lk_ban_done := fwc_ban_done g;
       lk_ban_done_line := fwc_ban_done_line g;
       lk_ban_inp := fwc_ban_inp g;

       lk_prompt_dollar := fprompt_dollar g;
       lk_prompt_space := fprompt_space g;
       lk_prompt_dollar_ban := fprompt_dollar_ban g;
       lk_read := fwc_read g;
       lk_owed_read_taint := fowed_read_taint g;

       lk_blk_step := fblk_step g;
       lk_blk_sp := fwc_blk_sp g;

       lk_prompt_dollar_post := fprompt_dollar_post g;
       lk_prompt_space_t := fprompt_space_t g;
       lk_prompt_dollar_line := fprompt_dollar_line g;
       lk_read_t := fwc_read_t g;

       lk_ab_pan := fab_pan;
       lk_ab_exf := fab_exf;
       lk_apr_exf := fapr_exf;

       lk_ban_read_taint := fban_read_taint g;
       lk_turn0 := fturn0 g;
       lk_panic_done := fwc_panic_done g;
    |}.

End file_link_inst.

(* ===================================================================== *)
(*  THE [UShRound]-FACING LEMMAS.                                         *)
(*                                                                       *)
(*  Lane SKELETON's obligation table, discharged by NAME at the file      *)
(*  instance.  [Wcl]/[Wbl] below are what [UShRound.v] must instantiate   *)
(*  its two parameters at; [Wcf I p = Wcl I p ∗ sh_hold I] is then the    *)
(*  family the loop carries, and the two framed laws admit that linear    *)
(*  conjunct.                                                            *)
(* ===================================================================== *)
Section sh_round_facing.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FI := (file_link_inst g).

  (* the two families [UShRound]'s [Wcl] / [Wbl] are instantiated at *)
  Definition file_Wcl (I : list (bv 8)) (p : nat) : iProp Σ :=
    lk_lcred FI (S gen_id) I p.

  Definition file_Wbl (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       lk_pin FI (S gen_id) v ∗ lk_ban FI (S gen_id) v I 0%nat)%I.

  Global Instance file_Wcl_timeless I p : Timeless (file_Wcl I p).
  Proof using . rewrite /file_Wcl. apply _. Qed.

  (* ---- [UShRound]'s [Hwbl] ---- *)
  Lemma file_Hwbl (I : list (bv 8)) : ⊢ file_Wcl I 3%nat -∗ file_Wcl I 0%nat.
  Proof using . rewrite /file_Wcl. iApply (lk_lcred_blk_line FI (S gen_id) I). Qed.

  (* ---- [UShRound]'s [Hwbwc] ---- *)
  Lemma file_Hwbwc (I : list (bv 8)) : ⊢ file_Wbl I -∗ file_Wcl I 0%nat.
  Proof using . rewrite /file_Wcl /file_Wbl. iApply (lk_lcred_of_ban FI (S gen_id) I). Qed.

  (* ---- [UShRound]'s [Hcltaint], AT THE TWO-PIN SHAPE (the lane's
          one-line change to [UShRound.v]; see the findings) ---- *)
  Lemma file_Hcltaint (I : list (bv 8)) (p : nat) (v : era_pins) :
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗
      file_taint (fgn_cl g) -∗ file_Wcl I p.
  Proof using .
    rewrite /file_Wcl. iApply (lk_lcred_taint FI (S gen_id) I p v).
  Qed.

  (* ---- [UShRound]'s [Hwc]: the read that completed a line ---- *)
  Lemma file_Hwc (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗
      inp_lb v (I ++ l ++ [wl_nl]) -∗
      file_Wcl I 2%nat -∗ file_Wcl (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hl. rewrite /file_Wcl.
    iApply (lk_lcred_read FI (S gen_id) I l v Hl).
  Qed.

  (* ---- [UShRound]'s [Hwbr]: a read past a banner-owed boundary ---- *)
  Lemma file_Hwbr (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗
      lk_rres FI v (I ++ l ++ [wl_nl]) -∗
      file_Wbl I -∗ file_taint (fgn_cl g).
  Proof using .
    intros Hl. iIntros "#Hpin #Hres Hb". rewrite /file_Wbl.
    iDestruct "Hb" as (v') "[#Hpin' Hb]".
    iDestruct (lk_pin_agr FI (S gen_id) v v' with "Hpin Hpin'") as %<-.
    iApply (lk_ban_read_taint FI (S gen_id) v I l Hl with "Hb Hres").
  Qed.

  (* =================================================================== *)
  (*  THE STAGE, AT THE FILE ERA (the program stream, (c))                *)
  (*                                                                     *)
  (*  echo's instance ([StageRec.echo_stage_inst]) opens the era's lend    *)
  (*  into a bundle and names the cursor itself; the file era's is         *)
  (*  SHORTER, because [FileLinksLine] already has both halves:            *)
  (*  [fwc_blk g k v I 0] IS the cursor and [fblk_step] IS its step.       *)
  (*                                                                     *)
  (*  WHAT IT IS ABOUT: the lines whose block is the LINE's own            *)
  (*  alternative, i.e. the [LEcho] ones.  At an [LEchoF] line the child   *)
  (*  writes to the FILE and the console block is the prompt; at an        *)
  (*  [LCat] line it is cat's.  [ck_lineok] is where that is said, and it  *)
  (*  is the record field the program stream added for exactly this.       *)
  (* =================================================================== *)
  Record file_stg := MkFileStg { fs_I : list (bv 8) }.

  Definition file_lineok (I : list (bv 8)) : Prop :=
    fline I = LEcho (last_ws I).

  (* the model's alternative 0 at an echo line IS echo's own output *)
  Lemma file_ralt0 : ralt_dec 0%nat = REcho 0%nat.
  Proof using . reflexivity. Qed.

  Lemma file_ralt0_ok (I : list (bv 8)) :
    file_lineok I -> ralt_ok (fline I) (ralt_dec 0%nat).
  Proof using .
    intro Hl. rewrite Hl file_ralt0. cbn [ralt_ok]. lia.
  Qed.

  Lemma file_ralt0_free : fst_free (ralt_dec 0%nat) = true.
  Proof using . reflexivity. Qed.

  Lemma file_fab0 (I : list (bv 8)) :
    file_lineok I -> fab I 0%nat = line_alts_of (last_ws I) !!! 0%nat.
  Proof using .
    intro Hl.
    rewrite (fab_is I 0%nat (file_ralt0_ok I Hl) file_ralt0_free) Hl.
    reflexivity.
  Qed.

  Lemma file_fab0_len (I : list (bv 8)) :
    file_lineok I ->
    (length (fab I 0%nat) - 2)%nat
    = length (wl_line (drop 1 (last_ws I))).
  Proof using .
    intro Hl. rewrite (file_fab0 I Hl) (line_alts_of_0_length (last_ws I)).
    lia.
  Qed.

  Local Lemma fi_cur_tl (k : nat) (v : era_pins) (st : file_stg) (p : nat) :
    Timeless (fwc_blk g k v (fs_I st) 0%nat p).
  Proof using . apply fwc_blk_timeless. Qed.

  Local Lemma fi_step (k : nat) (v : era_pins) (st : file_stg)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    (fline (fs_I st) = LEcho ws /\ last_ws (fs_I st) = ws) ->
    line_alts_of ws !!! 0%nat !! i = Some b ->
    ⊢ lk_pin FI k v -∗ lk_links FI -∗ fwc_blk g k v (fs_I st) 0%nat i -∗
      (fwc_blk g k v (fs_I st) 0%nat (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros [ Hln Hlast ] Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (fblk_step g k v (fs_I st) 0%nat i b Φ with "Hpin Hlk Hc HΦ").
    rewrite (file_fab0 (fs_I st) ltac:(rewrite /file_lineok Hlast; exact Hln)).
    rewrite Hlast. exact Hb.
  Qed.

  Definition file_cur_inst : CurRec FI :=
    MkCurRec FI file_stg
      (fun st ws => fline (fs_I st) = LEcho ws /\ last_ws (fs_I st) = ws)
      (fun ws => line_alts_of ws !!! 0%nat)
      file_lineok
      (fun k v st p => fwc_blk g k v (fs_I st) 0%nat p)
      fi_cur_tl fi_step.

  (* THE LEND, OPENED.  [fwc_lend] and [fwc_blk _ _ _ 0 0] are the same
     proposition ([blkcs_f cs 0 0 = cs] and [P + 0 = P]), and what the
     block's END pays is [lk_post FI], which is that family at
     [length (fab I 0) - 2]. *)
  Local Lemma fi_lend_stage (k : nat) (v : era_pins) (I : list (bv 8)) :
    file_lineok I ->
    ⊢ fwc_lend g k v I -∗
      (∃ st : file_stg,
         ⌜fline (fs_I st) = LEcho (last_ws I) /\ last_ws (fs_I st) = last_ws I⌝
         ∗ ⌜line_alts_of (last_ws I) !!! 0%nat
            = line_alts_of (last_ws I) !!! 0%nat⌝
         ∗ fwc_blk g k v (fs_I st) 0%nat 0%nat
         ∗ □ (fwc_blk g k v (fs_I st) 0%nat
                (length (wl_line (drop 1 (last_ws I)))) -∗
              lk_post FI k v I 0%nat))
      ∨ lk_T FI.
  Proof using .
    intro Hlok. rewrite /fwc_lend. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    iLeft. iExists (MkFileStg I). cbn [fs_I].
    iSplitR; [ iPureIntro; split; [ exact Hlok | reflexivity ] | ].
    iSplitR; [ by iPureIntro | ].
    iSplitL "Htn".
    - rewrite /fwc_blk. iLeft. iExists ps, cs, s0, P.
      cbn [blkcs_f]. rewrite Nat.add_0_r.
      iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
    - iIntros "!> Hc". rewrite /lk_post. cbn [lk_blk lk_ab file_link_inst].
      rewrite (file_fab0_len I Hlok). iExact "Hc".
  Qed.

  Local Lemma fi_apr0 (I : list (bv 8)) :
    file_lineok I -> lk_apr FI I 0%nat.
  Proof using .
    intro Hl. cbn [lk_apr file_link_inst]. rewrite /fapr.
    split_and!;
      [ exact (file_ralt0_ok I Hl) | exact file_ralt0_free | reflexivity ].
  Qed.

  Definition file_stage_inst : StageRec FI :=
    MkStageRec FI file_cur_inst fi_lend_stage fi_apr0.

End sh_round_facing.
