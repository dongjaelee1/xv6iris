(* ===================================================================== *)
(*  UInitFileCons.v -- /init's BOOT PAYMENT AT THE FILE RECORD           *)
(*  (lane INIT-FILE, deliverable I1).                                    *)
(*                                                                       *)
(*  [UInitBoot.echo_Hinit_boot]'s assembly, one application over, up to   *)
(*  the point where the campaign's dependency graph stops it -- see the   *)
(*  two walls recorded in [UInitFile.v]'s header and in the lane's        *)
(*  findings block.  What is here is everything /init's entry at the FILE *)
(*  era needs that IS derivable today, each piece named so that whoever   *)
(*  closes [file_prog_law] applies it rather than reproves it.           *)
(*                                                                       *)
(*  WHY IT IS A FILE OF ITS OWN and not the body of [UInitFile.v]:       *)
(*  [UInitBoot.v]'s measured rule.  This is proofmode-heavy u-tier work,  *)
(*  and [UInitFile.v] carries the ADEQUACY cone (it names                 *)
(*  [UFileBootAdequacy.file_prog_law], hence [SystemAdequacy]); mixing    *)
(*  the two is what made echo's assembly blow up at 54 GB.  So the split  *)
(*  here is [UInitBoot.v] / [UInitBootAdequacy.v]'s, with [UInitFile.v]   *)
(*  playing the second role.                                             *)
(*                                                                       *)
(*  THE RECORD EQUATIONS ARE PARAMETERS, exactly as in [FileLinks.v] and  *)
(*  [UShRound.v], and for the same reason: this file may not name         *)
(*  [AppFileRec.app_file] without pulling the adequacy cone in, so it     *)
(*  takes the three PROJECTIONS of the interface equation                 *)
(*  ([riscv_rx_tag = ftag g], [app_taint = file_taint (fgn_cl g)],        *)
(*  [riscv_cons_res = fecl g]) and the claim equation directly.  Each is  *)
(*  a [cbn] on [AppFileRec.file_ifc]'s record literal at the caller.      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ObsTrace.
(* the ghost binder list's defining modules, each IMPORTED and not merely
   required -- [UInitBoot.v]'s header note *)
Require Import CtxIdDefs.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FsAbsDefs.
Require Import FileInvDefs.
Require Import UserFd.
Require Import ConsoleInv.
Require Import WpUart.
Require Import UexecSlot.
Require Import UexecRet.
Require Import UexecSG.
Require Import UexecExecInst.      (* the INSTANCES: [uprogSG_free] *)
Require Import UexecExecMint.      (* [udepw_law_of_sup] / [uslot_mint_all] *)
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import FsImg.
Require Import FsInitPin.
Require Import FsInitPinBoot.      (* [era0_pins] *)
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import AppEcho.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import AppFile.
Require Import AppFileCons.      (* the claim's console readings *)
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import LinkRec.
Require Import FileLinksAt.        (* the families at a NAMED boot state *)
Require Import FileLinksAtBan.
Require Import FileLinkInst.       (* [file_link_inst] / [file_link_inst_at] *)
Require Import UkRun.
Require Import UkRunSys.
Require Import UkWriteClosed.      (* [kinit_w1_of_closed_l0] *)
Require Import UkInit.
Require Import UkInitMain.
Require Import UkSh.               (* [ush_tag_law] and its [D]-form *)
Require Import UInitBanner.        (* the generic banner, at [LinkRec] *)
Require Import LinkUserinit.       (* [UG.uexec_wp_gen] *)
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE PURE HALF: A FILE-DISCIPLINED HISTORY NEVER ENDS IN ^D        *)
(*                                                                       *)
(*  [UkSh.disc_no_ctrl_d]'s twin at [FileDisc.disc_f], and it is what     *)
(*  lane SKELETON's obligation 21 actually costs on the FILE side.  Lane  *)
(*  LINK-GEN-4 made [UkSh.ush_tag_law_at] take the discipline as a        *)
(*  parameter [D]; [ush_tag_law_of_at] then asks the era for exactly this *)
(*  refutation, and here it is, off [FileOutPure.disc_seg_f_no_ctrl_d]    *)
(*  and [FileDisc.disc_f_seg].  The echo proof's first step -- 0x04 is    *)
(*  not a carriage return, so [cons_xlate] is the identity on it -- is    *)
(*  copied verbatim; everything after it is the file discipline's own.    *)
(* ===================================================================== *)
Lemma disc_f_no_ctrl_d (h : list mobs) (b : bv 8) :
  obs_ends_in Uart0 h b -> bv_unsigned (cons_xlate b) = 4 ->
  FileDisc.disc_f h -> False.
Proof using .
  intros [h0 ->] Hx Hd.
  assert (Hb : bv_unsigned b = 4).
  { destruct (decide (b = (mword_of_int 13 : mword 8))) as [-> | Hne].
    - rewrite cons_xlate_cr in Hx. vm_compute in Hx. discriminate Hx.
    - rewrite (cons_xlate_other b Hne) in Hx. exact Hx. }
  destruct (UkSh.ush_cycles_snoc_in h0 b) as (s0 & Hin).
  pose proof (FileDisc.disc_f_seg _ _ Hd Hin) as Hseg.
  exact (FileOutPure.disc_seg_f_no_ctrl_d _ b Hseg
           (ex_intro _ s0 eq_refl) Hb).
Qed.

Section UInitFileCons.
  (* [UInitBoot.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), plus
     the file claim's and the file stage's classes.  NO [uexecSG] and NO
     [uprogSG] SECTION VARIABLE -- every deposit position names
     [UexecExecInst.uprogSG_free] per lemma. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* the era's record ([FileOut]'s gname pair) and the deed's names *)
  Context (g : file_gn) (r : file_names).

  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FI := (FileLinkInst.file_link_inst g).
  Local Notation stc_cons := (FdOpen true true (FdDevice CONSOLE)).

  (* =================================================================== *)
  (*  1.  THE TAG'S READING, AT THE FILE DISCIPLINE                       *)
  (*                                                                     *)
  (*  [UInitBoot]'s [Htg], one application over.  The tag equation is the *)
  (*  top theorem's; what it buys is [UkSh.ush_tag_law], the ONE          *)
  (*  consequence everything below the shell draws from a tagged history  *)
  (*  (a history ending in ^D is the taint).  The route is                *)
  (*  [ush_tag_law_at disc_f] -- the file discipline as the parameter --  *)
  (*  and [ush_tag_law_of_at] at the refutation above.                    *)
  (* =================================================================== *)
  Lemma file_tag_law_at
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ _) = ftag g) :
    ⊢ UkSh.ush_tag_law_at FT FileDisc.disc_f.
  Proof using .
    rewrite /UkSh.ush_tag_law_at. iIntros "!>" (h) "Hr".
    rewrite Htag /ftag. iDestruct "Hr" as "(_ & Hd & _)". iExact "Hd".
  Qed.

  Lemma file_tag_law_holds
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ _) = ftag g) :
    ⊢ UkSh.ush_tag_law FT.
  Proof using .
    iApply (UkSh.ush_tag_law_of_at FT FileDisc.disc_f disc_f_no_ctrl_d).
    iApply (file_tag_law_at Htag).
  Qed.

  (* =================================================================== *)
  (*  2.  THE ERA'S TURN, AS THE LINK RECORD WANTS IT                     *)
  (*                                                                     *)
  (*  STAGE's ONE THING, discharged.  [LinkRec.lk_turn] at the file       *)
  (*  instance is [FileLinksLine.fturn_pre g], which is [FileOut.fturn]   *)
  (*  -- the credential the boot mint hands <init> -- TOGETHER WITH       *)
  (*  [FileLinksLine.f0pre], the era's unfiled boot state with the deed's *)
  (*  own typed witness in its place.  The witness is exactly             *)
  (*  [AppFile.file_boot]'s second conjunct, so the two halves of         *)
  (*  [app_boot] and [app_turn] meet HERE and nowhere else, and what      *)
  (*  spends the result is the era's first banner byte through            *)
  (*  [FileLinks.file_write_link_first].                                  *)
  (*                                                                     *)
  (*  THE LATER IS THE CALLER'S TO STRIP: [file_boot] puts its witness    *)
  (*  under one [▷] (the boot transport only ever sees it there) and      *)
  (*  everything under it is timeless, so /init strips it at its first    *)
  (*  step -- inside the [|==>] of [file_prog_law]'s conclusion.  This    *)
  (*  lemma therefore takes the STRIPPED disjunction.                     *)
  (* =================================================================== *)
  Lemma file_f0pre_of_typed (s : dst) :
    (f_typed (fgn_cl g) s ∨ FT) -∗ FileLinksLine.f0pre g.
  Proof using .
    rewrite /FileLinksLine.f0pre.
    iIntros "[Hty | #HT]".
    - destruct s as [[i bs] | ].
      + iEval (rewrite /f_typed /=) in "Hty".
        iDestruct "Hty" as (ls) "[#Hlb %Hbt]".
        iExists (Some bs). iSplitR.
        { iPureIntro. destruct Hbt as (ws & sel & _ & Hok & Hsel & ->).
          exact (FileDisc.fcont_ok_subseq ws sel Hok Hsel). }
        iLeft. iEval (rewrite /FileOut.f0_typed /=).
        iExists ls. iFrame "Hlb". by iPureIntro.
      + iExists None. iSplitR; [ iPureIntro; exact I | ].
        iLeft. iApply (FileOut.f0_typed_none g).
    - iExists None. iSplitR; [ iPureIntro; exact I | ]. by iRight.
  Qed.

  Lemma file_turn_pre_of_boot (s : dst) :
    FileOut.fturn g (S gen_id) -∗ (f_typed (fgn_cl g) s ∨ FT) -∗
    lk_turn FI (S gen_id).
  Proof using .
    iIntros "Ht Hty".
    cbn [lk_turn FileLinkInst.file_link_inst].
    rewrite /FileLinksLine.fturn_pre.
    iSplitR; [ by iPureIntro | ]. iFrame "Ht".
    iApply (file_f0pre_of_typed s with "Hty").
  Qed.

  (* =================================================================== *)
  (*  3.  THE BANNER, AT THE FILE LINKS                                   *)
  (*                                                                     *)
  (*  [UInitBanner]'s two generic lemmas INSTANTIATED (lane LINK-GEN):    *)
  (*  the era's turn comes apart into the reader's half and round 0's     *)
  (*  banner-owed credential, and the eighteen bytes are paid from the    *)
  (*  second.  Nothing is twinned: [Section UInitBannerGen] is stated at  *)
  (*  [LinkRec] and [file_link_inst] is a total instance of it.           *)
  (* =================================================================== *)
  Lemma file_kinit_ban0 :
    lk_turn FI (S gen_id) -∗
    UInitBanner.kinit_dl0_at FI ∗ UInitBanner.kinit_ban_at FI 0%nat.
  Proof using . iApply (UInitBanner.kinit_ban0_of_eturn_at FI). Qed.

  Lemma file_kinit_ban_law
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = fecl g) :
    ⊢ □ (∀ (n : nat) (N : uk_names Σ),
           UInitBanner.kinit_ban_at FI n -∗
           UkInitMain.kinit_banner0 (PS := uprogSG_free) N stc_cons
             (∃ I : list (bv 8),
                ⌜length I = n⌝ ∗ lk_cred FI (S gen_id) I 0%nat)).
  Proof using .
    iApply (UInitBanner.kinit_ban_law_holds_at (PS := uprogSG_free) FI).
    cbn [lk_links FileLinkInst.file_link_inst].
    iApply (FileLinks.file_links_holds g Hcons).
  Qed.

  (* =================================================================== *)
  (*  4.  THE TWO READINGS OF THE SUPPLY                                  *)
  (*                                                                     *)
  (*  [AppFile.file_sup_of_taint] / [file_taint_of_sup] at the CLAIM      *)
  (*  equation, which is where they become facts about [AppInv.app_sup].  *)
  (* =================================================================== *)
  Lemma file_sup_of_taint_at
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ □ (FT -∗ AppInv.app_sup).
  Proof using .
    rewrite /AppInv.app_sup Heq.
    cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "!> #Ht". iApply (AppFile.file_sup_of_taint (fgn_cl g) r with "Ht").
  Qed.

  Lemma file_taint_of_sup_at
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ AppInv.app_sup -∗ FT.
  Proof using .
    rewrite /AppInv.app_sup Heq.
    cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "#Hs". iApply (AppFile.file_taint_of_sup (fgn_cl g) r with "Hs").
  Qed.

  (* =================================================================== *)
  (*  5.  THE CLAIM'S PURE HALF, AND /init's OWN PIN ROW                  *)
  (*                                                                     *)
  (*  [AppEcho.echo_fs_pure_acc]'s twin, straight off [AppFile.file_pred] *)
  (*  -- the claim IS the taint or the pure half beside the two state     *)
  (*  conjuncts, so the accessor costs nothing -- and the projection      *)
  (*  [FsInitPinBoot.era0_pins] that [PinnedExec]'s bundle asks for.      *)
  (* =================================================================== *)
  Lemma file_fs_pure_law
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ □ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
           AppCfg.app_pred AppCfg.app_run v
           ∗ (⌜FileFsPure.file_fs_pure v⌝ ∨ FT)).
  Proof using .
    rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "!>" (v) "Hp". iApply (AppFileCons.file_fs_pure_acc (fgn_cl g) r v with "Hp").
  Qed.

  Lemma file_era0_pins_law
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    ⊢ □ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
           AppCfg.app_pred AppCfg.app_run v
           ∗ (⌜FsInitPinBoot.era0_pins v⌝ ∨ FT)).
  Proof using .
    iDestruct (file_fs_pure_law Heq) as "#Hfs".
    iIntros "!>" (v) "Hp".
    iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
      [ iFrame "Hp"; iLeft; iPureIntro;
        exact (proj1 (FileFsPure.file_fs_pure_echo v Hf))
      | iFrame "Hp"; iRight; iExact "HT" ].
  Qed.

  (* =================================================================== *)
  (*  6.  /init's THREE DEPOSITS, AT THE FILE TAINT                       *)
  (*                                                                     *)
  (*  [UInitBoot.init_deps_of_laws] is echo's file's, and re-proved here  *)
  (*  rather than imported: importing [UInitBoot.v] would put the whole   *)
  (*  ECHO program tier in front of this leaf for six lines of plumbing.  *)
  (*  The deposits themselves are the supply's, exactly as at echo --     *)
  (*  write(16) under the taint, the closed-fd leaf at every record, and  *)
  (*  open(15) / mknod(17) free off the supply.                           *)
  (* =================================================================== *)
  Lemma file_init_deps_of_laws `{PSx : uprogSG Σ} (T : iProp Σ) :
    □ (T -∗ UkRun.udepw_law (PS := PSx) 16) -∗
    UkInit.kinit_wcl (PS := PSx) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 15) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 17) -∗
    □ UkInit.init_deps (PS := PSx) T.
  Proof using .
    iIntros "#Hwr #Hwcl #H15 #H17 !>".
    rewrite /UkInit.init_deps /UkInit.kinit_wlaw.
    iSplit; [ iSplit; [ iModIntro; iExact "Hwr" | iExact "Hwcl" ] | ].
    iSplit.
    - iModIntro. iExact "H15".
    - iModIntro. iExact "H17".
  Qed.

  Lemma file_init_deps
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r)
      (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = FT) :
    ⊢ □ UkInit.init_deps (PS := uprogSG_free) FT.
  Proof using .
    iDestruct (file_sup_of_taint_at Heq) as "#Hsup".
    iApply (file_init_deps_of_laws (PSx := uprogSG_free) FT
              with "[] [] [] []").
    - iModIntro. iIntros "#HT".
      iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
      + iApply ("Hsup" with "HT").
      + rewrite Hkill. iExact "HT".
    - rewrite /UkInit.kinit_wcl. iIntros "!>" (N0 b).
      iApply (UkWriteClosed.kinit_w1_of_closed_l0 (PS := uprogSG_free) N0 b).
    - iModIntro. iIntros "HT".
      iApply (udepw_law_of_sup (PSx := uprogSG_free) 15 (or_introl eq_refl)).
      iApply ("Hsup" with "HT").
    - iModIntro. iIntros "HT".
      iApply (udepw_law_of_sup (PSx := uprogSG_free) 17 (or_intror eq_refl)).
      iApply ("Hsup" with "HT").
  Qed.

  (* =================================================================== *)
  (*  7.  THE TAINT'S GENERIC SLOT                                        *)
  (*                                                                     *)
  (*  [UInitBoot]'s [Hmint] at the file taint: the arm every pinned exec  *)
  (*  falls back on once the era is off the discipline.                   *)
  (* =================================================================== *)
  Lemma file_gen_mint
      (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r)
      (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = FT) :
    ⊢ □ (∀ (R : iProp Σ) (W : uvis),
           FT -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
           □ (app_taint -∗ R) -∗ uslot W).
  Proof using .
    iDestruct (file_sup_of_taint_at Heq) as "#Hsup".
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iIntros "!>" (R W) "#Ht Hp #HR".
    iDestruct ("Hsup" with "Ht") as "#Hs".
    iAssert (app_taint)%I as "#Hkc"; [ rewrite Hkill; iExact "Ht" | ].
    iApply (uslot_mint_all with "Hs Hkc Hwp Hp HR").
  Qed.

  (* =================================================================== *)
  (*  8.  THE DEED'S RIDE: WHAT /init CAN HAND OVER, AND WHAT IT CANNOT   *)
  (*                                                                     *)
  (*  Lane SKELETON's obligation 22 -- the DEED in [UInitKernel.          *)
  (*  init_boot_pay]'s [Pay] -- does not need a change to                 *)
  (*  [UInitKernel.v]: [init_boot_pay] is abstract in the credential      *)
  (*  record, and [UShRound]'s own ruling puts the deed INSIDE the        *)
  (*  credential family ([Wcf I p := Wcl I p * sh_hold I]).  So the deed  *)
  (*  rides the bundle's one linear slot as part of [cc_wbn Cr 0], the    *)
  (*  round-0 banner-owed credential /init holds from its entry.          *)
  (*                                                                     *)
  (*  WHAT /init HAS AT THAT INSTANT is exactly this -- the deed at the   *)
  (*  boot value with its typed witness, or the taint -- and NOT          *)
  (*  [UShRound.sh_hold []], whose left arm also asks for [FileOut.f0_lb  *)
  (*  vf s0].  That resource cannot exist before the era's first console  *)
  (*  byte: [f0_lb] is a lower bound of [f0_auth vf (opt_list (fo_f0      *)
  (*  so))], the stage's [fo_f0] is [None] until a byte is written, and   *)
  (*  the only producer is [FileLinks.file_write_link_first], fired by    *)
  (*  the banner's first byte.  The lane's findings record the repair.    *)
  (* =================================================================== *)
  Definition file_hold_head : iProp Σ :=
    ((∃ s : dst, fown r s ∗ f_typed (fgn_cl g) s) ∨ FT)%I.

  Lemma file_hold_head_of_boot (s : dst) :
    fown r s -∗ (f_typed (fgn_cl g) s ∨ FT) -∗ file_hold_head.
  Proof using .
    iIntros "Hd [#Hty | #HT]"; rewrite /file_hold_head;
      [ iLeft; iExists s; iFrame "Hd Hty" | by iRight ].
  Qed.

  (* ...AND THE HALF THAT *IS* RECOVERABLE ONCE THE FIRST BYTE IS OUT.
     After the era's first banner byte the head arm of [FileLinksLine.
     fwc_ban] is refuted by its own index, so what is left carries the
     FILED boot state [f0w] -- persistent -- or the taint.  This is half
     of what obligation 22 costs; the other half is the TIE between that
     state and the deed's content, and that one is not derivable today
     (the findings say exactly why). *)
  Lemma file_ban_f0w (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat) :
    FileLinksLine.fwc_ban g k v I (S i) -∗
    FileLinksLine.fwc_ban g k v I (S i)
    ∗ ((∃ s0 : fst, FileLinksLine.f0w g k s0) ∨ FT).
  Proof using .
    iIntros "Hc". iEval (rewrite /FileLinksLine.fwc_ban) in "Hc".
    iDestruct "Hc" as "[Hl | [[%Hq _] | #HT]]".
    - iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & #Hf)".
      iSplitL "Htn Hps Hcs HE".
      + iEval (rewrite /FileLinksLine.fwc_ban). iLeft.
        iExists ps, cs, s0, P. iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
      + iLeft. iExists s0. iExact "Hf".
    - discriminate Hq.
    - iSplit.
      + iEval (rewrite /FileLinksLine.fwc_ban). iRight. iRight. iExact "HT".
      + iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  9.  RULING H': THE DEED AND THE ERA'S BOOT STATE AT ONE NAME        *)
  (*                                                                     *)
  (*  Consequences (a) and (b) of the ruling, checked at the statement.   *)
  (*  (c) is by construction: nothing here mints a ghost and [FileOut]'s  *)
  (*  stage is untouched -- [f0pre_at] is [f0pre]'s own body with the     *)
  (*  witness named, and [f0w] is the same resource it always was.        *)
  (* =================================================================== *)

  (* [file_f0pre_of_typed] with the state NAMED: the witness /init hands
     over is its deed's own content, and now it says so.  THE TYPED ARM
     ONLY -- the taint says nothing about the deed's content, so it cannot
     name a state; under it /init takes [s0 := None] ([file_f0pre_at_taint]
     below), which is admissible everywhere and which every [_at] family's
     taint arm accepts. *)
  Lemma file_f0pre_at_of_typed (s : dst) :
    f_typed (fgn_cl g) s -∗ f0pre_at g (dst_content s).
  Proof using .
    rewrite /FileLinksAt.f0pre_at.
    destruct s as [[i bs] | ];
      cbn [dst_content fmap option_fmap option_map]; iIntros "Hty".
    - iEval (rewrite /f_typed /=) in "Hty".
      iDestruct "Hty" as (ls) "[#Hlb %Hbt]".
      iSplitR.
      { iPureIntro. destruct Hbt as (ws & sel & _ & Hok & Hsel & ->).
        exact (FileDisc.fcont_ok_subseq ws sel Hok Hsel). }
      iLeft. iEval (rewrite /FileOut.f0_typed /=).
      iExists ls. iFrame "Hlb". by iPureIntro.
    - iSplitR; [ iPureIntro; exact I | ].
      iLeft. iApply (FileOut.f0_typed_none g).
  Qed.

  Lemma file_f0pre_at_taint : FT -∗ f0pre_at g None.
  Proof using .
    iIntros "#HT". rewrite /FileLinksAt.f0pre_at.
    iSplitR; [ iPureIntro; exact I | ]. by iRight.
  Qed.

  (* THE TURN, AT THE NAMED STATE.  [FileLinksAtBan.fturn_pre_at] is
     [lk_turn (file_link_inst_at g s0)]. *)
  Lemma file_turn_pre_at_of_boot (s0 : fst) :
    FileOut.fturn g (S gen_id) -∗ f0pre_at g s0 -∗
    lk_turn (file_link_inst_at g s0) (S gen_id).
  Proof using .
    iIntros "Ht Hpre".
    cbn [lk_turn FileLinkInst.file_link_inst_at].
    rewrite /FileLinksAtBan.fturn_pre_at.
    iSplitR; [ by iPureIntro | ]. iFrame "Ht Hpre".
  Qed.

  (* ---- (a) [Wbl_at s0 []] IS INHABITED AT /init's FIRST INSTRUCTION ----
     at [s0] the deed's own content, out of [AppFile.file_boot]'s two
     halves and nothing else.  This is what ruling H buys: the credential
     /init holds from its entry and the deed it holds beside it are at ONE
     state, so [UShRound]'s hold can be stated without [f0_lb] and the
     round's first prompt has its tie. *)
  Lemma file_Wbl_at_of_boot (s0 : fst) :
    FileOut.fturn g (S gen_id) -∗ f0pre_at g s0 -∗
    (∃ v : era_pins, era_pin (fgn_echo g) (S gen_id) v
       ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ file_Wbl_at g s0 [].
  Proof using .
    iIntros "Ht Hpre".
    iDestruct (file_turn_pre_at_of_boot s0 with "Ht Hpre") as "Hturn".
    iDestruct (lk_turn0 (file_link_inst_at g s0) (S gen_id) with "Hturn")
      as "[Hrd Hwr]".
    iSplitL "Hrd"; [ iExact "Hrd" | iExact "Hwr" ].
  Qed.

  (* ---- (b) AFTER THE BANNER'S FIRST BYTE THE SAME NAME COMES BACK ----
     [FileLinksAtBan.fban_at_f0w]: at [S i] the head arm is refuted by its
     own index, so what is left carries [f0w] AT THE CALLER'S [s0].  The
     first-drain pinning is untouched -- it reads [f0w] exactly as it
     always did. *)
  Lemma file_ban_f0w_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (i : nat) :
    fwc_ban_at g s0 k v I (S i) -∗
    fwc_ban_at g s0 k v I (S i)
    ∗ (FileLinksLine.f0w g k s0 ∨ FT).
  Proof using . iApply (FileLinksAtBan.fban_at_f0w g s0 k v I i). Qed.

End UInitFileCons.
