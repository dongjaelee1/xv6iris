(* ===================================================================== *)
(*  UShPipeCatSlot.v -- THE PIPELINE ERA'S /cat SLOT (lane                *)
(*  SH-PIPE-ROUND-6; the missing producer the round's assembly needs).    *)
(*                                                                       *)
(*  WHAT THIS FILE IS, AND WHY IT EXISTS.  The round the pipe line's      *)
(*  child law is about EXECS /cat in its right child, and the (W) half    *)
(*  of that exec ([UShCatPay.sh_exec_sup_cat_wq_holds_at], through        *)
(*  [ExecRun.exec_walk_of_pin]) takes [UShCatPay.sh_cat_slot T] -- whose  *)
(*  middle conjunct is the claim's law at [FsCatPin.era0_cat_pins].       *)
(*                                                                       *)
(*  THAT LAW HAS EXACTLY ONE PRODUCER IN THE TREE                         *)
(*  ([UShCatPay.sh_cat_slot_of_fs_pure_holds], at                         *)
(*  [FileFsPure.file_fs_pure]) and reaching it needs the ERA EQUATION     *)
(*  [file_app = MkAppcfg echo_names (pipe_pred gamma) r] -- which lives   *)
(*  in [UInitPipe.pipe_Hinit_boot] and NOWHERE below it.  In particular   *)
(*  [UShPipeRound.sh_round_holds_pipe], whose five premises are           *)
(*  [pipe_links], [udep], [UShEcho.sh_echo_slot T], the era pin and       *)
(*  [sh_pipe_child_law], cannot build it: [sh_echo_slot]'s law is at      *)
(*  [FsEchoPin.era0_echo_pins] and /cat's pin does not follow from        *)
(*  /echo's.  See the lane's Findings block, finding (2).                 *)
(*                                                                       *)
(*  So this is the ONE LINE [pipe_Hinit_boot] is missing, factored out    *)
(*  so that wiring it is an [iAssert] beside the [Hslot] one it already   *)
(*  has (the same [Hinv] and the same [Hmint]).                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import UexecSlot UexecRet UexecSG UexecExecInst.
Require Import ChildTok.
Require Import FsCfg.
Require Import FsAbsDefs.
Require Import AppCfg AppInv.
Require Import FsCatPin.
Require Import FileFsPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppPipeClaim.
Require Import AppPipeCons.
Require Import PipeOut.
Require Import UShCatPay.
Require Import CtxIdDefs.
Local Open Scope Z_scope.

Section UShPipeCatSlot.
  (* [UShCatPay.v]'s binder list verbatim, plus the pipeline era's own. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* THE PIPE ERA'S /cat SLOT, out of what [pipe_Hinit_boot] already
     holds: the application invariant, the era equation, and the generic
     slot's mint. *)
  Lemma pipe_sh_cat_slot (γ : echo_fixed) (r : echo_names) :
    @file_app Σ _ = MkAppcfg echo_names (pipe_pred γ) r ->
    app_inv fsc_fs -∗
    □ (∀ (R : iProp Σ) (W : uvis),
         echo_taint γ -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
         □ (app_taint -∗ R) -∗ uslot W) -∗
    UShCatPay.sh_cat_slot (echo_taint γ).
  Proof using .
    intros Heq. iIntros "#Hinv #Hmint".
    rewrite /UShCatPay.sh_cat_slot. iFrame "Hinv Hmint".
    rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "!>" (v) "Hp".
    iApply (AppPipeCons.pipe_cat_pins_acc γ r v with "Hp").
  Qed.

End UShPipeCatSlot.
