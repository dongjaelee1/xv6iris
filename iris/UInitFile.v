(* ===================================================================== *)
(*  UInitFile.v -- THE FILE APPLICATION'S [al_programs] (lane SKELETON,   *)
(*  K3; lane INIT-FILE): [UInitBoot.echo_Hinit_boot]'s twin, and the one  *)
(*  line that closes [UFileBootAdequacy.file_adequacy_fileSigma].         *)
(*                                                                       *)
(*  THE THEOREM IS [UFileBootAdequacy.file_prog_law] VERBATIM.  It is not *)
(*  restated here: this file names it and proves it, so that the day the  *)
(*  proof lands, [file_adequacy_fileSigma] loses its premise and NOTHING  *)
(*  else in the campaign moves.  The corollary below is transitive, which *)
(*  is why NEITHER is added to [iris/FileAssumptions.v]'s audit target    *)
(*  and why nothing in the tree imports this file.                       *)
(*                                                                       *)
(*  ===== WHAT IS PROVED, AND WHERE ==================================== *)
(*                                                                       *)
(*  /init's boot payment at the FILE console record is [iris/             *)
(*  UInitFileCons.v] -- a file of its own for [UInitBoot.v]'s measured    *)
(*  reason (this one carries the ADEQUACY cone through                    *)
(*  [UFileBootAdequacy]; mixing that with a proofmode-heavy u-tier        *)
(*  assembly is what made echo's blow up).  It has, each at the file era  *)
(*  and each by name:                                                    *)
(*                                                                       *)
(*    [disc_f_no_ctrl_d] / [file_tag_law_holds]  the tag's reading at the *)
(*        FILE discipline -- [UkSh.ush_tag_law_at disc_f] through         *)
(*        [ush_tag_law_of_at].  (Lane SKELETON's obligation 21, closed:   *)
(*        LINK-GEN-4 made the discipline a parameter, and this is the     *)
(*        file era's refutation of a tagged ^D.)                          *)
(*    [file_f0pre_of_typed] / [file_turn_pre_of_boot]  the era's turn as  *)
(*        the link record wants it: [AppFile.file_boot]'s typed witness   *)
(*        and [FileOut.fturn] are ONE resource, and the era's first       *)
(*        banner byte files the boot state out of it                      *)
(*        ([GenLinks.gwrite_link_first], through                          *)
(*        [FileLinksLine.fban_step]).                                     *)
(*    [file_kinit_ban0] / [file_kinit_ban_law]  the banner, at            *)
(*        [UInitBanner]'s generic lemmas at [FileLinkInst.                *)
(*        file_link_inst] -- an INSTANTIATION, not a twin.                *)
(*    [file_sup_of_taint_at] / [file_taint_of_sup_at] / [file_fs_pure_law]*)
(*        [file_era0_pins_law] / [file_init_deps] / [file_gen_mint]       *)
(*        the claim's readings, /init's three deposits and the taint's    *)
(*        generic slot.                                                   *)
(*    [file_hold_head_of_boot] / [file_ban_f0w]  the DEED's ride          *)
(*        (obligation 22): what /init holds at its first instruction, and *)
(*        the filed boot state as it comes back out of the banner.        *)
(*                                                                       *)
(*  [iris/AppFileCons.v] carries SEVEN of the NINE conjuncts of           *)
(*  [UInitCons.init_cons_laws_at] at the file claim: the five whose view   *)
(*  does not move (one application of [AppFile.file_pred_cons] each) and   *)
(*  the two that do -- the ARM, by [AppFile.file_step_free] at four        *)
(*  landed [FileDeltas] legs, and the console's own MKNOD, by              *)
(*  [file_pred_split] / [file_pred_join].                                  *)
(*                                                                       *)
(*  ===== CLOSED (2026-09-22) ============================================ *)
(*                                                                       *)
(*  The four things the earlier header listed are all landed: (1) the    *)
(*  index (RULING H', [FileLinksAt]), (2) the era-head arm (RULING        *)
(*  HOLD-POS, [UShRound.sh_done_head]), (3) [UInitFileCC.file_cc_holds]  *)
(*  and (4) the name predicate (RULING NM / NM-OPEN).  Two more were met  *)
(*  on the way and are rulings of their own: the console credential over *)
(*  [option Z] (RULING CONS-CRED) and the boot state filed at boot        *)
(*  (RULING F0-BOOT).  The assembly is [UInitFileBoot.file_Hinit_boot_at]; *)
(*  this file applies it and closes the corollary.                       *)
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
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import RiscvAdequacy.
Require Import UserFd.
Require Import FileDisc.
Require Import FsImgDisk.
Require Import AppFile.
Require Import EchoOut.
Require Import FileOut.
Require Import App.                      (* [app_names] / [app_pred] / [app_boot] / [app_turn] *)
Require Import UFileBootAdequacy.        (* [file_prog_law], [fileΣ] *)
Require Import AppFileRec.               (* [app_file]'s projections *)
Require Import UInitFileBoot.            (* [file_Hinit_boot_at]: the assembly *)
Local Open Scope Z_scope.

Section UInitFile.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{HU : !ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* THE LAW, BY ITS NAME AND NOT BY A COPY OF ITS TEXT.  A restatement
     would be a second thing to keep in step with [App.xv6_app_laws]'s
     field; naming [UFileBootAdequacy.file_prog_law] is what makes the
     corollary below a one-liner.  The body is [UInitFileBoot.
     file_Hinit_boot_at] at the record's own two equations. *)
  Theorem file_Hinit_boot : file_prog_law (Σ := Σ).
  Proof using HU.
    intros HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface Hgen.
    cbn [app_file app_names app_pred app_ifc] in Heq, Hiface.
    iIntros "#Hinv Hb Hturn".
    iApply (file_Hinit_boot_at HR GEN c r Heq Hiface with "Hinv [Hb] [Hturn]").
    - cbn [app_file app_boot]. iExact "Hb".
    - cbn [app_file app_turn file_turn]. iExact "Hturn".
  Qed.

End UInitFile.

(* ===================================================================== *)
(*  THE COROLLARY -- ONE LINE.                                           *)
(*                                                                       *)
(*  [UFileBootAdequacy.file_adequacy_fileSigma] with its only remaining   *)
(*  premise discharged.  This is the campaign's theorem, and              *)
(*  [iris/FileAssumptions.v] audits it: the fourteen ambient assumptions  *)
(*  and nothing else.                                                    *)
(* ===================================================================== *)
Corollary file_adequacy_closed
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ FileDisc.file_phi κs.
Proof.
  exact (file_adequacy_fileΣ (file_Hinit_boot (Σ := fileΣ))
           g Hgen0 Hpow0 Hdisk).
Qed.
