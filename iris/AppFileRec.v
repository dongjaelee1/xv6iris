(* AppFileRec.v -- THE FILE APPLICATION'S RECORD (AppFile layer B).

   Design of record: claude-notes/design/app-file.md section 4.4,
   deliverable 4.  [AppEcho.v]'s sections 5 and 6 at the file claim: the
   conclusion, the record [app_file], and [App.xv6_app_laws] with every
   field but [al_programs] discharged.

   THE FIXED PART IS [FileOut.file_gn] -- [AppFile.file_fixed] paired with
   the file era map's gname -- so nothing in [AppFile.v] moves: every one
   of its lemmas is read at [fgn_cl c].

   ONE THING IS A SECTION HYPOTHESIS AND IS NOT DISCHARGED HERE:
   [al_programs], lane SH-ROUND's (the first process's exec bundle).  It is
   not an axiom -- every result below is a theorem with it in its binder
   list.  [Decision (FileDisc.disc_f h)] WAS the second and is now
   [FileDiscDec.disc_f_dec] (lane FILE-DEC). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsImgDisk.
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsState.
Require Import FsAbsDefs.
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import AppInv.
Require Import DevModel.
Require Import UartNames.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
Require Import FileInvDefs.
Require Import AppCfg.
Require Import FsCfg.
Require Import App.
Require Import UserFd.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import Xv6Cameras.
Require Import InitBoot.
Require Import InodeInv.
Require Import RiscvAdequacy.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE CONCLUSION                                                     *)
(*                                                                        *)
(*  [FileDisc.file_phi] VERBATIM.  Like [AppEcho.echo_phi] it reads the    *)
(*  trace alone, so the state argument is dropped.                         *)
(* ====================================================================== *)
Definition file_phi : gstate -> list mobs -> Prop :=
  fun _ h => FileDisc.file_phi h.

Section FileApp.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* ---- the four fields that are resources ---- *)

  Definition file_R (c : file_gn) (h : list mobs) : iProp Σ := file_led c h.

  Global Instance file_R_timeless c h : Timeless (file_R c h).
  Proof using . rewrite /file_R. apply _. Qed.

  Definition file_tag (c : file_gn) (h : list mobs) : iProp Σ := ftag c h.

  Global Instance file_tag_persistent c h : Persistent (file_tag c h).
  Proof using . rewrite /file_tag. apply _. Qed.
  Global Instance file_tag_timeless c h : Timeless (file_tag c h).
  Proof using . rewrite /file_tag. apply _. Qed.

  Definition file_kill (c : file_gn) : iProp Σ := file_taint (fgn_cl c).

  Global Instance file_kill_persistent c : Persistent (file_kill c).
  Proof using . rewrite /file_kill. apply _. Qed.
  Global Instance file_kill_timeless c : Timeless (file_kill c).
  Proof using . rewrite /file_kill. apply _. Qed.

  Definition file_cons (c : file_gn)
    : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ := fecl c.

  Global Instance file_cons_timeless c k h H : Timeless (file_cons c k h H).
  Proof using . rewrite /file_cons. apply _. Qed.

  (* ...AND THE INTERFACE'S LICENCE LAW ([RiscvPtsto.ai_lic], lane
     SUP-ONE): [file_al_sup] read at the CREDENTIAL instead of at the
     supply -- the file application's kill price is its taint, and a
     tainted claim answers any boundary event. *)
  Lemma file_cons_lic (c : file_gn) :
    file_kill c ⊢
      □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
           (ev : ConsLog.cons_ev),
           file_cons c k h H ==∗ file_cons c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /file_cons /file_kill. iIntros "#Ht !>" (k h H ev) "Ho".
    iApply (fecl_sup c k h H ev with "Ht Ho").
  Qed.

  Definition file_ifc (c : file_gn) : app_iface Σ :=
    MkAppIface (file_tag c) (file_tag_persistent c) (file_tag_timeless c)
               (file_kill c) (file_kill_persistent c) (file_kill_timeless c)
               (file_cons c) (file_cons_timeless c) (file_cons_lic c).

  Definition file_turn (c : file_gn) : nat -> iProp Σ := fturn c.

  (* ====================================================================== *)
  (*  2.  THE RECORD                                                        *)
  (* ====================================================================== *)
  Definition app_file : xv6_app Σ :=
    MkApp file_gn file_cl_all file_names
          (fun c => file_pred (fgn_cl c))
          (fun c k r => file_boot (fgn_cl c) k r)
          file_R file_ifc file_turn file_phi.

  (* ---- the birth step ---- *)
  Lemma file_al_birth : ⊢ |==> ∃ c : app_fixed app_file, app_cl app_file c.
  Proof using . cbn [app_file app_fixed app_cl]. exact file_birth_all. Qed.

  Lemma file_al_Rt (c : app_fixed app_file) (h : list mobs) :
    Timeless (app_R app_file c h).
  Proof using . cbn [app_file app_fixed app_R] in c |- *. apply _. Qed.

  (* the supply buys the kill credential, and the two are one reading of
     the taint counter ([AppFile.file_taint_of_sup]) *)
  Lemma file_al_kill (c : app_fixed app_file) (r : app_names app_file) :
    AppInv.app_sup_raw (app_pred app_file c) r ⊢ □ app_kill app_file c.
  Proof using .
    rewrite /app_kill.
    cbn [app_file app_fixed app_names app_pred app_ifc file_ifc ai_kill]
      in c, r |- *.
    iIntros "#Hs". iModIntro. rewrite /file_kill.
    iApply (file_taint_of_sup (fgn_cl c) r with "Hs").
  Qed.

  Lemma file_al_sup (c : app_fixed app_file) (r : app_names app_file) :
    AppInv.app_sup_raw (app_pred app_file c) r
      ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
             (ev : ConsLog.cons_ev),
             app_cons app_file c k h H ==∗
             app_cons app_file c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /app_cons.
    cbn [app_file app_fixed app_names app_ifc file_ifc ai_cons file_cons]
      in c, r |- *.
    iIntros "#Hs".
    iDestruct (file_taint_of_sup (fgn_cl c) r with "Hs") as "#Ht".
    iIntros "!>" (k h H ev) "Ho".
    iApply (fecl_sup c k h H ev with "Ht Ho").
  Qed.

  Lemma file_al_R0 (c : app_fixed app_file) :
    app_cl app_file c ⊢ |==> app_R app_file c [].
  Proof using .
    cbn [app_file app_fixed app_cl app_R] in c |- *.
    iIntros "Hc". iModIntro. rewrite /file_R.
    iApply (file_led_init c with "Hc").
  Qed.

  Lemma file_al_pow (c : app_fixed app_file) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_file c h ==∗
      app_R app_file c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
      (if on then emp
       else app_cons app_file c (S (obs_boots h)) []
              (LogEntryDefs.MkCH [] [] [] None) ∗
            app_turn app_file c (S (obs_boots h))).
  Proof using .
    intros _.
    rewrite /app_cons.
    cbn [app_file app_fixed app_R file_R app_ifc file_ifc ai_cons file_cons
         app_turn file_turn] in c |- *.
    iApply (file_led_pow c h on).
  Qed.

  (* the two UART arms, at the theorem's literal shape *)
  Lemma file_al_tx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_file) (r : app_names app_file)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_file) (app_pred app_file c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
           (ho : list mobs) (H : LogEntryDefs.cons_hist),
           ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
           ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
           ⌜u_wire u = u_out u⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
           ⌜ho `prefix_of` h⌝ -∗
           ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
           (if i is Uart0 then app_cons app_file c (S gen_id) ho H else emp) -∗
           uart_ghosts γ u' -∗ app_R app_file c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           (if i is Uart0 then app_cons app_file c (S gen_id) ho H else emp) ∗
           uart_ghosts γ u' ∗ app_R app_file c (h ++ [ObsUartOut i b])%list).
  Proof using .
    intros _ _.
    rewrite /app_cons.
    cbn [app_file app_fixed app_R file_R app_ifc file_ifc ai_cons file_cons]
      in c |- *.
    iIntros "!>" (h b u u' ho H)
      "%Htxp %Hlp %Hsh %Hwi %Hwo %Hbt %Hpo %Hacc Ho Hg Hled".
    iAssert (|==> (if i is Uart0 then fecl c (S gen_id) ho H else emp)
                  ∗ (file_taint (fgn_cl c)
                     ∨ (match i with
                        | Uart0 => ∃ (s0 : fst) (vf : file_era),
                                     ⌜good_out_f s0
                                        (open_seg h ++ [ObsUartOut Uart0 b])⌝
                                     ∗ f0_typed c s0
                                     ∗ file_era_pin c (obs_boots h) vf
                                     ∗ f0_lb vf s0
                        | _ => True
                        end)))%I with "[Ho]" as ">[Ho Hgo]".
    { destruct i; last first.
      { iModIntro. iFrame "Ho". by iRight. }
      assert (Hins : ins (open_seg h ++ [ObsUartOut Uart0 b])
                     = ins (open_seg h))
        by (by rewrite ins_app ins_out app_nil_r).
      assert (Hpre : obs_wire Uart0 (open_seg h ++ [ObsUartOut Uart0 b])
                     `prefix_of` uart_acc u).
      { rewrite obs_wire_app Hwi Hwo.
        replace (obs_wire Uart0 [ObsUartOut Uart0 b]) with [b] by reflexivity.
        rewrite -(DevModel.uart_tx_pop_acc u b u' Htxp) /DevModel.uart_acc
                (DevModel.uart_tx_pop_out u b u' Htxp).
        exists (u_tx u'). by rewrite -app_assoc. }
      (* THE DRAIN IS AT A NONEMPTY WIRE -- this byte is on it -- which is
         what lets it hand over the era's boot state's lower bound *)
      assert (Hne : obs_wire Uart0 (open_seg h ++ [ObsUartOut Uart0 b]) <> []).
      { rewrite obs_wire_app.
        replace (obs_wire Uart0 [ObsUartOut Uart0 b]) with [b] by reflexivity.
        intros Hz. apply (f_equal length) in Hz.
        rewrite length_app in Hz. cbn [length] in Hz. lia. }
      iDestruct (fecl_drain c (S gen_id) h ho H
                   (open_seg h ++ [ObsUartOut Uart0 b])
                   Hsh Hbt Hpo Hins ltac:(rewrite Hacc; exact Hpre) Hne
                   with "Ho") as "[Ho Hgo]".
      iModIntro. iFrame "Ho".
      rewrite /fdrain_ret.
      iDestruct "Hgo" as "[HT | Hgo]"; [by iLeft |].
      iDestruct "Hgo" as (s0 vf) "(%Hg & %Hfok & #Hty & #Hfp & #Hlb)".
      iRight. iExists s0, vf. rewrite Hbt. iFrame "Hty Hfp Hlb".
      by iPureIntro. }
    iMod (file_led_tx c h i b Hsh with "Hgo Hled") as "Hled".
    iModIntro. iFrame "Ho Hg Hled".
  Qed.

  Lemma file_al_rx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_file) (r : app_names app_file)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_file) (app_pred app_file c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
           ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
           ⌜obs_boots h = S gen_id⌝ -∗
           uart_ghosts γ u' -∗ app_R app_file c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           uart_ghosts γ u' ∗ app_R app_file c (h ++ [ObsUartIn i b])%list ∗
           app_tag app_file c (h ++ [ObsUartIn i b])%list).
  Proof using .
    intros _ _. rewrite /app_tag.
    cbn [app_file app_fixed app_R file_R app_ifc file_ifc ai_tag] in c |- *.
    iIntros "!>" (h b u u') "_ %Hsh _ Hg Hled".
    iMod (file_led_rx c h i b Hsh with "Hled") as "[Hled Htag]".
    iModIntro. iFrame "Hg Hled". rewrite /file_tag. iExact "Htag".
  Qed.

  (* ---- the transport, with the first process's boot resource ---- *)
  Lemma file_al_xfer (c : app_fixed app_file) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred app_file c) (app_boot app_file c k).
  Proof using .
    cbn [app_file app_fixed app_names app_pred app_boot] in c |- *.
    rewrite /app_xfer_boot_raw. iApply file_xfer_boot.
  Qed.

  (* ---- the echo shift ---- *)
  Lemma file_al_echo (HR : riscvGS Σ) (c : app_fixed app_file) :
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_file c ->
    ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift Σ HR GEN XI.
  Proof using .
    cbn [app_file app_fixed app_ifc] in c |- *.
    intros Hiface.
    iApply (FileLinks.file_happ_echo c (HRg := HR)).
    - rewrite /riscv_cons_res Hiface. by cbn [file_ifc ai_cons file_cons].
    - rewrite /riscv_rx_tag Hiface. by cbn [file_ifc ai_tag file_tag].
  Qed.

  (* ---- era 0's claim at the literal image ---- *)
  Lemma file_Happ_init (gst : gstate) (sb : fs_sb) (nib : nat)
      (cov : gset Z) :
    fs_boot_image_wf (v_disk (gst.(gdev).(dvirtio))) XV6_DISK_BYTES
      sb nib cov ->
    fs_blocks (v_disk (gst.(gdev).(dvirtio))) = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    forall c : app_fixed app_file,
      ⊢ |==> ∃ r : app_names app_file,
          app_pred app_file c r (abs_view (fss_inodes (FsDurImg.img_state
             (fs_blocks (v_disk (gst.(gdev).(dvirtio)))) sb nib))).
  Proof using .
    intros Himg Hdk Hsb Hcov c.
    cbn [app_file app_fixed app_names app_pred] in c |- *.
    exact (file_init_img (fgn_cl c) _ XV6_DISK_BYTES sb nib cov
             Himg Hdk Hsb Hcov).
  Qed.

  (* ---- the conclusion's one ingredient ---- *)
  Lemma file_Hphi_R (c : app_fixed app_file) (gst : gstate) (h : list mobs) :
    app_R app_file c h ⊢ ⌜app_phi app_file gst h⌝.
  Proof using .
    cbn [app_file app_fixed app_R app_phi] in c |- *.
    rewrite /file_R /file_phi. iIntros "H".
    iApply (file_led_phi c h with "H").
  Qed.

End FileApp.

(* ====================================================================== *)
(*  3.  THE LAWS, AS THE CLASS INSTANCE                                    *)
(*                                                                        *)
(*  Every field but [al_programs] is one of the lemmas above.              *)
(*  [al_programs] -- the first process's exec bundle -- is lane SH-ROUND's *)
(*  and is a SECTION HYPOTHESIS here rather than an [Admitted] lemma, so   *)
(*  that nothing in this file is admitted and the instance simply does not *)
(*  exist until that lane lands.                                          *)
(* ====================================================================== *)
Section FileLaws.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* lane SH-ROUND's field, verbatim from [App.xv6_app_laws] *)
  Context (Hprog :
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : app_fixed (app_file (Σ := Σ)))
           (r : app_names (app_file (Σ := Σ))),
      @file_app Σ HF
        = MkAppcfg (app_names app_file) (app_pred app_file c) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_file c ->
      @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_file c (S gen_id) r -∗
        app_turn app_file c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0).

  Global Instance file_laws : App.xv6_app_laws (app_file (Σ := Σ)).
  Proof using Hprog ufdG0.
    split.
    - exact file_al_birth.
    - exact file_al_Rt.
    - exact file_al_kill.
    - exact file_al_sup.
    - exact file_al_R0.
    - exact file_al_pow.
    - intros HR GEN HF c r i γ Heq Huart.
      exact (file_al_tx (HF := HF) HR GEN c r i γ Heq Huart).
    - intros HR GEN HF c r i γ Heq Huart.
      exact (file_al_rx (HF := HF) HR GEN c r i γ Heq Huart).
    - exact file_al_xfer.
    - exact Hprog.
    - exact file_al_echo.
  Qed.
End FileLaws.
