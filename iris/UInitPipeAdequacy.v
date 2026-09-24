(* ===================================================================== *)
(*  UInitPipeAdequacy.v -- [App.al_programs] AT [AppPipe.app_pipe], AND   *)
(*  THE PIPELINE APPLICATION'S CLOSED THEOREM (lane PIPE-CC).             *)
(*                                                                       *)
(*  A SEPARATE FILE from the assembly, for a measured reason:             *)
(*  [UInitPipe.v] is a proofmode-heavy u-tier assembly, and pulling       *)
(*  [RiscvAdequacy] / [SystemAdequacy] / [FsCfgBoot] -- which             *)
(*  [UPipeBootAdequacy.pipe_prog_law] needs to even ELABORATE (its class  *)
(*  binders are [riscvGpreS] and the five [*GpreS]) -- into that one      *)
(*  blows the elaboration up.  So this file carries the adequacy cone     *)
(*  and takes exactly TWO things from the assembly:                       *)
(*  [UInitPipe.pipe_Hinit_boot] and [UInitPipe.sh_pipe_child_law_all].     *)
(*                                                                       *)
(*  WHY [UPipeBootAdequacy.v] IS NOT EDITED INSTEAD.  It DEFINES          *)
(*  [pipe_prog_law], which this file discharges; making it take the child *)
(*  law instead would need it to [Require] its own discharger.  The       *)
(*  restated corollary therefore lives here, and                          *)
(*  [iris/PipeAssumptions.v] audits THIS one -- a cone strictly larger    *)
(*  than the old target's, since it now walks the whole program tier.     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang ObsTrace RiscvPtsto.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import VirtioModel.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import UserFd.
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import App.
Require Import EchoDisc.            (* [disc] / [good_out]: the echo corollary *)
Require Import PipeDisc.
Require Import EchoOut.
Require Import PipeOut.
Require Import AppPipe.
Require Import UPipeBootAdequacy.   (* [pipe_prog_law] / [pipeSigma] *)
Require Import UInitPipe.           (* [pipe_Hinit_boot] / the premise *)

Local Open Scope Z_scope.

Section PipeProgLaw.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{HU : !ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ}.

  Theorem pipe_prog_law_of_child :
    sh_pipe_child_law_all -> pipe_prog_law (Σ := Σ).
  (* POINTWISE, and through the record's [cbn], for a measured reason: the record's fields ARE [AppPipe]'s definitions, but
     unification does not delta-unfold a record literal for them, and an
     [exact] of the whole term asks for one conversion of two [box]-heavy
     bundles at once. *)
  Proof using HU.
    intros Hchild HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface Hgen.
    cbn [app_pipe app_names app_pred app_ifc] in Heq, Hiface.
    iIntros "#Hinv Hb Hturn".
    iApply (pipe_Hinit_boot HR GEN c r
              (Hchild HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface) Heq Hiface
              with "Hinv [Hb] [Hturn]").
    - cbn [app_pipe app_boot]. iExact "Hb".
    - cbn [app_pipe app_turn pipe_turn]. iExact "Hturn".
  Qed.

End PipeProgLaw.

(* ===================================================================== *)
(*  THE THEOREM -- [UPipeBootAdequacy.pipe_adequacy_pipeSigma] with its    *)
(*  [Hprog] discharged by the child law ([UInitPipe.                       *)
(*  sh_pipe_child_law_all_holds], lane SH-PIPE-ROUND-14): no premise of    *)
(*  its own, the functor list the concrete [pipeSigma] (so every ghost     *)
(*  class is realised by [subG] and the statement is not vacuous), the    *)
(*  disk the literal mkfs image, and a conclusion that mentions no Iris -- *)
(*  [PipeDisc.pipe_phi] is the whole specification.                        *)
(* ===================================================================== *)
Theorem pipe_adequacy_pipeΣ_final
    (gst : gstate)
    (Hgen0 : gst.(ggen) = 0%nat) (Hpow0 : gst.(gpow) = false)
    (Hdisk : v_disk (gst.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], gst)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ PipeDisc.pipe_phi κs.
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (gst.(gdev).(dvirtio)))
                   XV6_DISK_BYTES fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (gst.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (pipe_adequacy_at_img (Σ := pipeΣ)
           (pipe_prog_law_of_child (Σ := pipeΣ) sh_pipe_child_law_all_holds)
           gst fsimg_sb fsimg_nib fsimg_cov Hgen0 Hpow0 Himg Hdk
           eq_refl eq_refl n κs t2 g2 Hn).
Qed.

(* ===================================================================== *)
(*  THE ECHO APPLICATION'S THEOREM IS A COROLLARY (design app-pipe.md     *)
(*  SS0.2): an echo-disciplined history is pipe-disciplined, and at an    *)
(*  echo-only input the pipeline conclusion reads back as                 *)
(*  [EchoDisc.good_out] ([PipeDisc.pipe_phi_echo]).  Same premises, same  *)
(*  cone, so [iris/PipeAssumptions.v] is this theorem's audit too.        *)
(* ===================================================================== *)
Corollary echo_adequacy
    (gst : gstate)
    (Hgen0 : gst.(ggen) = 0%nat) (Hpow0 : gst.(gpow) = false)
    (Hdisk : v_disk (gst.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], gst)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ (disc κs -> Forall good_out (cycles_of κs)).
Proof.
  intros n κs t2 g2 Hn.
  destruct (pipe_adequacy_pipeΣ_final gst Hgen0 Hpow0 Hdisk n κs t2 g2 Hn)
    as [Hsafe Hphi].
  split; [exact Hsafe | exact (pipe_phi_echo κs Hphi)].
Qed.
