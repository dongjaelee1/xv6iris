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
