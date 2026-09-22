From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.
Require Import UexecSG.
Require Import PathElems.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import ConsoleInv.
Require Import SpecKexec.
Require Import FsAbsDefs.
Require Import FsAbsEra.
Require Import PinnedExec.
Require Import UexecExecInst.
Require Import UkRun.
Require Import UkInit.
Require Import UexecExecMint.
Require Import UkWriteClosed.
Require Import UInitKernel.
Require Import LineWords.
Require Import EchoLinks.
Require Import UInitDiag.
Require Import UInitBanner.
Require Import UInitCons.
Require Import UInitConsK.
Require Import UInitSh.
Require Import UShPanic.
Require Import UShEcho.
Require Import EchoLinksPro.
Require Import EchoLinksLine.
Require Import EchoLinksBan.
Require Import UShLine.
Require Import AppEcho.
Require Import EchoOut.
Require Import UserConsole.
Require Import UserFd.
Require Import LinkUserinit.
Require Import UkSh.
Require Import UShConsK.
Require Import KexecDefs.
Require Import PageGeom.
Require Import InitBoot.
Require Import ElfUser.
Require Import ElfLoadable.
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import UInitBoot.          (* [init_deps_of_laws] / [init_boot_bundle_of_pinned] *)
(* ---- the pipeline era's own layers ---- *)
Require Import LinkRec.
Require Import ReadRec.
Require FsImg.
Require InodeInv.
Require Import FileDisc.
Require Import FileState.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import FileLinksAt.
Require Import FileLinkInst.
Require Import FileReadInst.       (* [file_read_leaf_holds_at]: the read leaf at the index *)
Require Import UShRound.           (* the round, its families and their laws *)
Require Import UInitFileCons.      (* the claim's laws at /init *)
Require Import UInitConsFile.      (* the console's two open leaves at the file claim *)
Require Import AppFileCons.        (* [file_cons_never_law] *)
Require Import UkShRedirBody.      (* [ush_line_file]: the era's three line shapes *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  UInitFileCC.v -- THE FILE ERA'S CONSOLE CREDENTIAL, AND ITS TEN LAWS  *)
(*  (item 4 of the file application; PROGRAM-STREAM stretch 15).          *)
(*                                                                       *)
(*  [UInitPipe.pipe_cc] / [pipe_cc_holds] one era over.  The families are  *)
(*  [UShRound.Wcf] / [Wbf] -- the record's credential WITH THE DEED'S     *)
(*  HOLD (RULING HOLD-POS), at the era's boot state [s0] (RULING H') --   *)
(*  which is why one conjunct is not a transfer: the prologue credential  *)
(*  [cc_wp] must carry the hold too, and the /init prologue laws frame   *)
(*  it through the writer ([kinit_banner_pay_frame]).                    *)
(* ===================================================================== *)
Section FileInitCC.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!fileAppG Σ, !fileOutG Σ}.

  (* THE HOLD AS A POSITION-INDEXED FAMILY: what /init's prologue carries
     beside the record's own credential.  The DONE tie at the input the
     prologue is at ([UShRound.sh_done_at]). *)
  Definition file_H (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate) (n : nat) : iProp Σ :=
    (∃ I : list (bv 8), ⌜length I = n⌝
       ∗ ((∃ v : era_pins, era_pin (fgn_echo g) (S gen_id) v ∗ inp_lb v I)
          ∨ file_taint (fgn_cl g))
       ∗ UShRound.sh_done_at g r s0 I)%I.

  Lemma file_cc_rd_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (s0 : fstate) :
    forall i : nat,
      Timeless (UShLine.ush_rd_pin_at (lk_rres (file_link_inst_at g s0))
                  (fgn_echo g) i).
  Proof using .
    intro i. rewrite /UShLine.ush_rd_pin_at.
    apply bi.exist_timeless; intro v.
    apply bi.exist_timeless; intro I.
    apply bi.sep_timeless; [ apply bi.pure_timeless | ].
    apply bi.sep_timeless; [ apply era_pin_timeless | ].
    apply bi.sep_timeless; [ apply _ | ].
    apply bi.sep_timeless; [ apply inp_lb_timeless | ].
    apply (lk_rres_tl (file_link_inst_at g s0)).
  Qed.

  Lemma file_cc_wb_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate) :
    forall I : list (bv 8), Timeless (UShRound.Wbf g r s0 I).
  Proof using . intro I. apply UShRound.Wbf_timeless. Qed.

  Definition file_cc (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate) : cons_cred Σ :=
    MkConsCred
      (UShLine.ush_rd_pin_at (lk_rres (file_link_inst_at g s0)) (fgn_echo g))
      (file_cc_rd_timeless HR GEN g s0)
      (UShLine.ush_mid_at (lk_rres (file_link_inst_at g s0)) (fgn_echo g))
      (UShRound.Wcf g r s0)
      (UShRound.Wbf g r s0)
      (file_cc_wb_timeless HR GEN g r s0)
      (fun n => (UInitDiag.kinit_pro_at (file_link_inst_at g s0) n
                 ∗ file_H HR GEN g r s0 n)%I).

  (* THE WRITER FRAMES A RESOURCE (PROGRAM-STREAM stretch 15): [UkInit.
     kinit_banner_pay]'s per-byte family carries [H] beside each step
     ([UkInit.kinit_w1_frame]) and hands it back beside the post.  This is
     what lets the /init prologue laws, stated at the bare record
     credential, carry the deed's hold. *)
  Lemma kinit_banner_pay_frame (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (N : uk_names Σ) (stc : fdstate) (len : nat) (f : nat -> bv 8)
      (Rt H : iProp Σ) :
    UkInit.kinit_banner_pay (PS := uprogSG_free) N stc len f Rt -∗ H -∗
    UkInit.kinit_banner_pay (PS := uprogSG_free) N stc len f (Rt ∗ H).
  Proof using .
    iIntros "Hp HH Hstd". iDestruct ("Hp" with "Hstd") as (Ch) "(#Hst & H0 & Hend)".
    iExists (fun j : nat => (Ch j ∗ H)%I). iSplitR.
    { iIntros "!>" (j) "%Hj".
      iApply (UkInit.kinit_w1_frame with "[]"). iApply ("Hst" $! j with "[%]").
      exact Hj. }
    iSplitL "H0 HH"; [ iFrame "H0 HH" | ].
    iIntros "[Hc HH]". iDestruct ("Hend" with "Hc") as "[$ $]". iExact "HH".
  Qed.

  (* the prologue credential's record half is the line credential at
     position 0 ([UInitPipe.pipe_wp_line]'s twin) *)
  Lemma file_wp_line (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (s0 : fstate) (n : nat) :
    ⊢ UInitDiag.kinit_pro_at (file_link_inst_at g s0) n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝
        ∗ FileLinkInst.file_Wcl_at g s0 I 0%nat.
  Proof using .
    iIntros "H". rewrite /UInitDiag.kinit_pro_at.
    iDestruct "H" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists I. iSplitR; [ by iPureIntro | ].
    rewrite /FileLinkInst.file_Wcl_at /lk_lcred. iExists v. iFrame "Hpin".
    rewrite (lk_lpr_0 (file_link_inst_at g s0) (S gen_id) v I).
    iApply (lk_line_of_pro (file_link_inst_at g s0) (S gen_id) v I).
    iApply (lk_pro_of_pban (file_link_inst_at g s0) (S gen_id) v I with "Hc").
  Qed.


  (* THE BANNER-OWED FAMILY WITH THE HOLD IS THE RECORD'S [cc_wbn] (item
     4's assembly, [UInitPipe]'s [Hbto]/[Hbfr] with the deed's hold): the
     record's banner credential beside the deed's DONE, the two at ONE
     input by the era's input bound -- or the hold is the taint's. *)
  Lemma file_wbn_to (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate) (n : nat) :
    UserConsole.cc_wbn (file_cc HR GEN g r s0) n -∗
    UInitBanner.kinit_ban_at (file_link_inst_at g s0) n
    ∗ file_H HR GEN g r s0 n.
  Proof using .
    rewrite /UserConsole.cc_wbn /file_cc /=. iIntros "H".
    iDestruct "H" as (I) "[%Hlen Hb]".
    iDestruct (UShRound.Wbf_inp g r s0 I with "Hb") as "[Hb #Hinp]".
    rewrite /UShRound.Wbf /FileLinkInst.file_Wbl_at.
    iDestruct "Hb" as "[Hb Hd]". iDestruct "Hb" as (v) "[#Hpin Hb]".
    iSplitL "Hb".
    { rewrite /UInitBanner.kinit_ban_at. iExists v, I.
      iSplitR; [ by iPureIntro | ]. iFrame "Hpin Hb". }
    rewrite /file_H. iExists I. iSplitR; [ by iPureIntro | ]. iFrame "Hd".
    iDestruct "Hinp" as "[[Hinp _] | #HT]"; [ iLeft; iExact "Hinp" | by iRight ].
  Qed.

  Lemma file_wbn_of (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate) (n : nat) :
    UInitBanner.kinit_ban_at (file_link_inst_at g s0) n -∗
    file_H HR GEN g r s0 n -∗
    UserConsole.cc_wbn (file_cc HR GEN g r s0) n.
  Proof using .
    rewrite /UInitBanner.kinit_ban_at /file_H /UserConsole.cc_wbn /file_cc /=.
    iIntros "Hb Hh".
    iDestruct "Hb" as (v I) "(%Hlen & #Hpin & Hb)".
    iDestruct "Hh" as (I') "(%Hlen' & #Hinp' & Hd)".
    iAssert (FileLinkInst.file_Wbl_at g s0 I) with "[Hb]" as "Hb".
    { rewrite /FileLinkInst.file_Wbl_at. iExists v. iFrame "Hpin Hb". }
    iDestruct (FileLinksAtInp.file_wb_inp_at g s0 I with "Hb") as "[Hb #Hinp]".
    iExists I. iSplitR; [ by iPureIntro | ]. rewrite /UShRound.Wbf. iFrame "Hb".
    iDestruct "Hinp" as "[[Hinp _] | #HT]"; last first.
    { iApply (UShRound.sh_deed_taint with "HT"). }
    iDestruct "Hinp'" as "[Hinp' | #HT]"; last first.
    { iApply (UShRound.sh_deed_taint with "HT"). }
    iDestruct "Hinp" as (v1) "[#Hpin1 #Hi]".
    iDestruct "Hinp'" as (v') "[#Hpin' #Hi']".
    iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v1 v' with "Hpin1 Hpin'")
      as %<-.
    iDestruct (inp_lb_agree v1 I I' ltac:(congruence) with "Hi Hi'") as %<-.
    iExact "Hd".
  Qed.

  (* ===================================================================== *)
  (*  THE TEN LAWS ([UInitSh.cons_cred_holds_at]) at the file era.          *)
  (*  [UInitPipe.pipe_cc_holds] is the pattern: nine transfers, one step.   *)
  (* ===================================================================== *)
  Lemma file_cc_holds (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate)
      (Heq : @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl g)) r)
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = fecl g)
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = FileOut.ftag g) :
    (⊢ FileLinks.file_links g) ->
    UInitSh.cons_cred_holds_at fsc_cons (file_taint (fgn_cl g))
      FileDisc.disc_input_f
      (proj1 (FileReadInst.file_gets_holds))
      (proj1 (proj2 (FileReadInst.file_gets_holds)))
      UkShRedirBody.ush_line_file
      (proj2 (proj2 (FileReadInst.file_gets_holds)))
      (file_cc HR GEN g r s0).
  Proof using .
    intros Hlkp.
    assert (Htsw : ⊢ file_taint (fgn_cl g) -∗ app_sup).
    { iIntros "#HT".
      iApply (UInitFileCons.file_sup_of_taint_at g r Heq with "HT"). }
    assert (Hstw : ⊢ app_sup -∗ file_taint (fgn_cl g)).
    { iIntros "#Hs".
      iApply (UInitFileCons.file_taint_of_sup_at g r Heq with "Hs"). }
    pose proof (UShRound.Wcf_inp g r s0) as Hwci.
    pose proof (UShRound.Wbf_inp g r s0) as Hwbi.
    rewrite /UInitSh.cons_cred_holds_at /file_cc /=.
    split_and!.
    - (* (1) the read leaf at the index *)
      intros γp N l Hpeq.
      exact (FileReadInst.file_read_leaf_holds_at g Htag s0
               (UShRound.Wbf g r s0) N γp l Hpeq Hstw Htsw Hlkp).
    - intros γp N i Hpeq.
      exact (UShLine.ush_lease_of_at (lk_rres (file_link_inst_at g s0))
               (fgn_echo g) (file_taint (fgn_cl g)) (UShRound.Wbf g r s0)
               N γp i Hpeq).
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_taint_at (lk_rres (file_link_inst_at g s0))
               (fgn_echo g) (file_taint (fgn_cl g)) (UShRound.Wbf g r s0)
               N γp I Hpeq).
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_wb_at (lk_rres (file_link_inst_at g s0))
               (fgn_echo g) (file_taint (fgn_cl g)) (UShRound.Wbf g r s0)
               N γp I Hpeq Hwbi).
    - (* (5) the read that completes a line, at the deed *)
      intros γp I l Hnl. exact (UShRound.Hwc_f g r s0 γp I l Hnl).
    - intros I. exact (UShRound.Hwbwc_f g r s0 I).
    - intros I. exact (UShRound.Hwbl_f g r s0 I).
    - (* (8) a banner-owed credential meets a delivered line: the taint --
         [Wbf] is the record's banner credential beside the deed's DONE *)
      intros γp I l Hnl. iIntros "Hm [Hb _]".
      iApply (UShRound.Hwbr g s0 γp I l Hnl with "Hm Hb").
    - intros γp N l i Hpeq.
      exact (UShLine.ush_posb_of_lend_at (lk_rres (file_link_inst_at g s0))
               (fgn_echo g) (file_taint (fgn_cl g)) N γp
               (UShRound.Wcf g r s0) (UShRound.Wbf g r s0) l i Hpeq
               Hwci Hwbi).
    - (* (10) THE STEP: the prologue credential carries the hold, and the
         two inputs -- the record's and the hold's, both of length [n] --
         are one input, by the era's input bound *)
      intros n. iIntros "[Hp Hh]".
      iDestruct (file_wp_line HR GEN g s0 n with "Hp") as (I) "[%Hlen Hc]".
      rewrite /file_H. iDestruct "Hh" as (I') "(%Hlen' & #Hinp' & Hd)".
      iExists I. iSplitR; [ by iPureIntro | ].
      iDestruct (FileLinksAtInp.file_wc_inp_at g s0 I 0%nat with "Hc")
        as "[Hc #Hinp]".
      (* [Wcf I 0]'s DONE arm, entered by the equation rather than by a
         rewrite (the goal is the record's field, not the family's name) *)
      assert (Hdone : forall J : list (bv 8),
                ⊢ FileLinkInst.file_Wcl_at g s0 J 0%nat -∗
                  UShRound.sh_done_at g r s0 J -∗
                  UShRound.Wcf g r s0 J 0%nat).
      { intro J. iIntros "Hc Hd". rewrite (UShRound.Wcf_0 g r s0 J).
        iLeft. iFrame "Hc Hd". }
      iDestruct "Hinp" as "[Hinp | #HT]"; last first.
      { iApply (Hdone I with "Hc"). iApply (UShRound.sh_deed_taint with "HT"). }
      iDestruct "Hinp'" as "[Hinp' | #HT]"; last first.
      { iApply (Hdone I with "Hc"). iApply (UShRound.sh_deed_taint with "HT"). }
      iDestruct "Hinp" as (v) "[#Hpin #Hi]".
      iDestruct "Hinp'" as (v') "[#Hpin' #Hi']".
      iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v v' with "Hpin Hpin'")
        as %<-.
      iDestruct (inp_lb_agree v I I' ltac:(congruence) with "Hi Hi'") as %<-.
      iApply (Hdone I with "Hc Hd").
  Qed.


  (* ===================================================================== *)
  (*  THE CONSOLE'S TWO OPEN LEAVES, out of /init's console credential      *)
  (*  ([UInitPipe.pipe_cons_in_of_Cns] at the file claim).                  *)
  (* ===================================================================== *)
  Lemma file_cons_in_of_Cns (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names)
      (Heq : @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl g)) r) :
    app_inv fsc_fs -∗ UInitCons.init_cons_cred (file_taint (fgn_cl g)) (fn_cons r) -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N (file_taint (fgn_cl g)))
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N
               (file_taint (fgn_cl g)) (cons_never (fn_cons r)))
        ∗ cons_never (fn_cons r))
     ∨ file_taint (fgn_cl g)).
  Proof using .
    iIntros "#Hinv #Hc". rewrite /UInitCons.init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (UInitConsFile.sh_cons_absent_file g r (cons_never (fn_cons r))
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /UShConsK.sh_cons_never_law. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (AppFileCons.file_cons_never_law (fgn_cl g) r).
    - iLeft.
      iApply (UInitConsFile.sh_cons_console_file_of_leg g r i Heq
                with "[] Hm Hinv").
      iApply UInitConsFile.file_cons_create_leg_holds.
    - iRight. iRight. iExact "HT".
  Qed.

  (* ===================================================================== *)
  (*  THE CONSOLE SUPPLY OUT OF sh's SLOT ([UInitPipe.pipe_cons_sup_of_sh_   *)
  (*  slot] at the file era's five readings and its credential).            *)
  (* ===================================================================== *)
  (* SEALED, as [UInitPipe.v:444] / [UInitSh.v:139]: with the discipline and
     the line constructor VARIABLES, a [Persistent]/[IntoWand] search on
     [sh_pay_at] descends into [ush_rest_l_at]'s wand tower and does not
     return. *)
  #[local] Typeclasses Opaque UInitSh.sh_pay_at.
  #[local] Typeclasses Opaque UkSh.ush_rest_l_at.

  (* THE CREDENTIAL /init HANDS DOWN, READ AS THE FILE CLAIM'S: the three
     arms of [UInitCons.init_cons_cred] are the two flags of
     [AppFileCons.file_cons_cred] beside its taint arm -- [None] serves the
     sealed console and the tainted era alike, since the file claim's
     consumers only ever spend the flag as "not the row I am touching". *)
  Lemma file_cons_cred_of_init (g : file_gn) (r : file_names) :
    UInitCons.init_cons_cred (file_taint (fgn_cl g)) (fn_cons r) -∗
    ∃ jo : option Z, file_cons_cred (fgn_cl g) r jo.
  Proof using .
    rewrite /UInitCons.init_cons_cred. iIntros "#[Hn | [[%j Hm] | HT]]".
    - iExists None. iApply (file_cons_cred_of_never with "Hn").
    - iExists (Some j). iApply (file_cons_cred_of_made with "Hm").
    - iExists None. iApply (file_cons_cred_of_taint with "HT").
  Qed.

  (* THE SLOT IS BUILT UNDER THE CREDENTIAL (the design point of
     PROGRAM-STREAM stretch 16, option C): the round inside [sh_pay_at]
     needs the console's flag ([UShRound.sh_round_holds_file]), and the
     flag is decided by /init's own mknod MID-WALK, so what /init's boot
     supplies is not the slot but a wand from the flag to it.  The exec
     supply is then built under the credential in every arm, the sealed
     and the tainted ones at [None]. *)
  Lemma file_cons_sup_of_sh_slot (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) (s0 : fstate)
      (Heq : @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl g)) r)
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = fecl g)
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = FileOut.ftag g)
      (st : fdstate) (n0 : nat) :
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    (⊢ FileLinks.file_links g) ->
    udep (PS := uprogSG_free) -∗
    □ (file_taint (fgn_cl g) -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (UShRound.Wcf g r s0) -∗
    □ (∀ jo : option Z,
         file_cons_cred (fgn_cl g) r jo -∗
         UInitSh.init_sh_slot (file_taint (fgn_cl g))
           (UInitSh.sh_pay_at UkShRedirBody.ush_line_file (file_taint (fgn_cl g))
              (file_cc HR GEN g r s0) UInitSh.sh_Rsh n0)) -∗
    UkInit.init_cons_sup fsc_cons (file_taint (fgn_cl g))
      (UInitCons.init_cons_cred (file_taint (fgn_cl g)) (fn_cons r)) st
      (file_cc HR GEN g r s0).
  Proof using .
    intros Hpsok_free Hn0 Hst Hlkp.
    iIntros "#Hdep #Hdp #Hplaw #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct (file_cons_cred_of_init g r with "Hcns") as (jo) "#Hcred".
      iDestruct ("Hcore" $! jo with "Hcred") as "#Hcore'".
      iApply (UInitSh.init_exec_sup_of_sh_slot_at FileDisc.disc_input_f
                (proj1 (FileReadInst.file_gets_holds))
                (proj1 (proj2 (FileReadInst.file_gets_holds)))
                UkShRedirBody.ush_line_file
                (proj2 (proj2 (FileReadInst.file_gets_holds)))
                (file_taint (fgn_cl g)) fsc_cons st (cons_never (fn_cons r))
                (file_cc HR GEN g r s0) UInitSh.sh_Rsh n0
                Hpsok_free Hn0 Hst
                (file_cc_holds HR GEN g r s0 Heq Hcons Htag Hlkp)
                with "Hdep Hdp Hplaw [] Hcore'").
      iApply (file_cons_in_of_Cns HR GEN g r Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (UInitCons.init_cons_cred_of_taint (file_taint (fgn_cl g)) (fn_cons r)
                with "HT").
  Qed.

End FileInitCC.
