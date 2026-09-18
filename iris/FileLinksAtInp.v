(* ===================================================================== *)
(*  FileLinksAtInp.v -- THE SEAM'S TWO INPUT READINGS AT THE FILE         *)
(*  FAMILIES, PER BOOT STATE (lane INIT-FILE).                           *)
(*                                                                       *)
(*  [UShLine.ush_wc_inp] and [UShLine.ush_wb_inp] are the two Coq-level   *)
(*  readings the seam between /init's position-indexed payload and sh's   *)
(*  input-indexed credential spends: the credential goes in, the SAME     *)
(*  credential comes back, and beside it the era's input as a lower       *)
(*  bound of the pinned era ([EchoOut.inp_lb]), or the taint.             *)
(*  [UShLine.ush_wc_inp_lcred] and [UShLine.ush_wb_inp_ban] discharge     *)
(*  them at the ECHO families; the two lemmas below are the same pair at  *)
(*  the FILE families INDEXED BY THE ERA'S BOOT STATE                     *)
(*  ([FileLinkInst.file_Wcl_at] / [file_Wbl_at], ruling H's twins).       *)
(*                                                                       *)
(*  NOTHING NEW IS CLAIMED: every arm of every indexed family either      *)
(*  carries [FileLinksLine.fcur], whose fourth conjunct IS the input's    *)
(*  lower bound, or is the era's head ([FileLinksAt.fhead_at], which      *)
(*  carries the bound at the empty input together with the equation that  *)
(*  says the input IS empty), or is the taint.                           *)
(*                                                                       *)
(*  A LEAF FILE: it sits above [FileLinkInst] and below nothing, so the   *)
(*  program stream does not move when it does.                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import EchoLinks.
Require Import LinkRec.
Require Import FileLinksAt.
Require Import FileLinksAtBan.
Require Import FileLinksAtLine.
Require Import FileLinkInst.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import WpUart.
Require Import UShLine.
Require Import CtxIdDefs.
Local Open Scope Z_scope.

Section file_links_at_inp.
  (* [UShRound.v]'s binder list, which is [UShRest.v]'s verbatim plus the
     file claim's and the file stage's classes: a shorter list makes Coq
     synthesise an instance and the elaboration explodes. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).

  Local Notation FT := (file_taint (fgn_cl g)).

  (* =================================================================== *)
  (*  1.  THE LOOP'S TIGHT CREDENTIAL                                     *)
  (* =================================================================== *)
  (* The shape is [UShLine.ush_wc_inp_lcred]'s verbatim: one
     [destruct p as [| [| [| p']]]] over [FileLinksAt.fwc_lpr_at]'s four
     positions, an [iAssert] that reads the bound off whichever arm holds,
     and a per-arm rebuild of the family that was taken apart. *)
  Lemma file_wc_inp_at (s0 : fstate) :
    UShLine.ush_wc_inp (fgn_echo g) (file_taint (fgn_cl g))
      (FileLinkInst.file_Wcl_at g s0).
  Proof using .
    intros I p. iIntros "H".
    rewrite /FileLinkInst.file_Wcl_at /LinkRec.lk_lcred.
    iDestruct "H" as (v) "[#Hpin Hc]".
    cbn [LinkRec.lk_pin LinkRec.lk_lpr FileLinkInst.file_link_inst_at] in *.
    iAssert (FileLinksAt.fwc_lpr_at g s0 (S gen_id) v I p
             ∗ (inp_lb v I ∨ FT))%I with "[Hc]" as "[Hc #Hi]".
    { destruct p as [| [| [| p']]]; cbn [FileLinksAt.fwc_lpr_at].
      - rewrite /FileLinksAt.fwc_line_at /FileLinksAt.fwc_pro_at
                /FileLinksAt.fwc_blk_at /FileLinksAt.fhead_at
                /FileLinksLine.fcur.
        iDestruct "Hc" as "[[Hl | [Hh | #HT]] | Hq]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
          iSplitL "Htn".
          * iLeft. iLeft. iExists ps, cs, P.
            iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
          * iLeft. iExact "HE".
        + iDestruct "Hh"
            as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
          iSplitR "".
          * iLeft. iRight. iLeft. iSplitR; [ by iPureIntro | ].
            iSplitR; [ by iPureIntro | ].
            iFrame "Htn Hps Hcs HE Hvf Hpre".
          * iLeft. subst I. iExact "HE".
        + iSplit;
            [ iLeft; iRight; iRight; iExact "HT" | iRight; iExact "HT" ].
        + iDestruct "Hq" as (a) "[%Ha [Hl | #HT]]".
          * iDestruct "Hl"
              as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
            iSplitL "Htn".
            -- iRight. iExists a. iSplitR; [ by iPureIntro | ].
               iLeft. iExists ps, cs, P.
               iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
            -- iLeft. iExact "HE".
          * iSplit.
            -- iRight. iExists a. iSplitR; [ by iPureIntro | ].
               iRight. iExact "HT".
            -- iRight. iExact "HT".
      - rewrite /FileLinksAt.fwc_sp_t_at /FileLinksLine.fcur.
        iDestruct "Hc" as "[Hl | #HT]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
          iSplitL "Htn".
          * iLeft. iExists ps, cs, P.
            iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ].
      - rewrite /FileLinksAt.fwc_open_t_at /FileLinksLine.fcur.
        iDestruct "Hc" as "[Hl | #HT]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
          iSplitL "Htn".
          * iLeft. iExists ps, cs, P.
            iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ].
      - rewrite /FileLinksAt.fwc_blk_at.
        iDestruct "Hc" as "[Hl | #HT]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
          iSplitL "Htn".
          * iLeft. iExists ps, cs, P.
            iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iSplitL "Hc"; [ iExists v; iFrame "Hpin Hc" | ].
    iDestruct "Hi" as "[HE | HT]";
      [ iLeft; iExists v; iFrame "Hpin HE" | iRight; iExact "HT" ].
  Qed.

  (* =================================================================== *)
  (*  2.  THE BANNER-OWED CREDENTIAL, WITH THE BOUNDARY FACT              *)
  (* =================================================================== *)
  (* Nothing is re-destructed here: [FileLinksAtBan.fwc_ban_inp_at] is
     already exactly this read-back at the indexed banner family, so the
     lemma only has to peel the era pin off and put it back. *)
  Lemma file_wb_inp_at (s0 : fstate) :
    UShLine.ush_wb_inp (fgn_echo g) (file_taint (fgn_cl g))
      (FileLinkInst.file_Wbl_at g s0).
  Proof using .
    intros I. iIntros "H". rewrite /FileLinkInst.file_Wbl_at.
    iDestruct "H" as (v) "[#Hpin Hc]".
    cbn [LinkRec.lk_pin LinkRec.lk_ban FileLinkInst.file_link_inst_at] in *.
    iDestruct (FileLinksAtBan.fwc_ban_inp_at g s0 (S gen_id) v I with "Hc")
      as "[Hc #Hi]".
    iSplitL "Hc"; [ iExists v; iFrame "Hpin Hc" | ].
    iDestruct "Hi" as "[[HE %Hr] | HT]".
    - iLeft. iSplitR; [ | by iPureIntro ]. iExists v. iFrame "Hpin HE".
    - iRight. iExact "HT".
  Qed.

End file_links_at_inp.
