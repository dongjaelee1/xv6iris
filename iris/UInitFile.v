(* ===================================================================== *)
(*  UInitFile.v -- THE FILE APPLICATION'S [al_programs] (lane SKELETON,    *)
(*  K3): [UInitBoot.echo_Hinit_boot]'s twin, and the one line that closes  *)
(*  [UFileBootAdequacy.file_adequacy_fileSigma].                          *)
(*                                                                       *)
(*  THE THEOREM IS [UFileBootAdequacy.file_prog_law] VERBATIM.  It is not *)
(*  restated here: this file names it and proves it, so that the day the  *)
(*  proof lands, [file_adequacy_fileSigma] loses its premise and NOTHING  *)
(*  else in the campaign moves.  The proof is [Admitted] -- this is the   *)
(*  skeleton lane -- and the corollary below is Admitted transitively,    *)
(*  which is why NEITHER is added to [iris/FileAssumptions.v]'s audit     *)
(*  target and why nothing in the tree imports this file.                 *)
(*                                                                       *)
(*  ===== WHAT THE PROOF IS, STEP BY STEP ============================== *)
(*                                                                       *)
(*  [UInitBoot.echo_Hinit_boot] one application over; every step below    *)
(*  cites the echo lemma it copies and the file lemma that replaces it.   *)
(*                                                                       *)
(*  (1) THE THREE PROJECTIONS, off the record's interface equation:       *)
(*      [riscv_rx_tag = ftag c], [app_taint = file_taint (fgn_cl    *)
(*      c)], [riscv_cons_res = fecl c].  [AppFileRec.file_ifc] is built   *)
(*      from exactly those three, so each is [cbn] on the record literal, *)
(*      as in echo's [Htag] / [Hkill] / [Hcons].                         *)
(*                                                                       *)
(*  (2) THE LICENCE AND THE SUPPLY: [WpUart.cons_licence] out of          *)
(*      [FileOut]'s [fecl_sup] (echo's [EchoOut.ecl_sup]), and            *)
(*      [AppInv.app_sup] out of the taint ([AppFile.file_sup_of_taint]).  *)
(*      Both are wands from the taint, exactly as in echo.                *)
(*                                                                       *)
(*  (3) THE LINKS, ONCE.  echo proves [EchoLinks.echo_links_holds] here;  *)
(*      the file era proves the [FileLinks] bundle lane LINK-GEN owes --  *)
(*      the SAME eight links ([file_write_link], [_blk], [_pro],          *)
(*      [file_write_link_first], [file_read_link], [file_cons_link_of_    *)
(*      taint], [file_write_link_taint], [file_cons_run]) packaged as one *)
(*      persistent record, which CAT-ENTRY already asked for.  [FileLinks *)
(*      .v] has the links and NOT the bundle.                            *)
(*                                                                       *)
(*  (4) THE BANNER FILES THE ERA'S BOOT STATE.  This is the ONE step with *)
(*      no echo counterpart: the era's FIRST process byte goes through    *)
(*      [FileLinks.file_write_link_first], which takes the deed's own     *)
(*      typed witness ([AppFile.file_boot]'s second conjunct, stripped of *)
(*      its later) and files [o_f0 := Some s0] -- design SS4.1, the      *)
(*      paragraph on who files s0 and with what.  /init holds the deed   *)
(*      at that instant                                                  *)
(*      because [app_boot app_file] IS [file_boot], so the value is its   *)
(*      own.                                                              *)
(*                                                                       *)
(*  (5) /init's ENTRY: [UInitKernel.init_boot_pay] at the FILE console    *)
(*      record, through [UInitKernel.init_boot_con] and                   *)
(*      [InitBoot.init_boot_bundle_of_pinned], with [Pay] GAINING THE     *)
(*      DEED -- [file_boot]'s [fown r s] rides the bundle's one linear    *)
(*      slot into <init>'s entry beside [fturn], exactly as echo's turn   *)
(*      does.  Everything else ([UInitKernel.init_cons_dance_all],        *)
(*      [UkInit.init_deps], [UInitDiag]'s three laws, [UInitBanner]) is   *)
(*      echo's at the file links.                                         *)
(*                                                                       *)
(*  (6) SH'S SLOT: [UInitSh.init_sh_image_entry] is already abstract in   *)
(*      [T], [Cr] and [Rsh], so it is INSTANTIATED (not twinned) at the   *)
(*      file families, with the deed in the lend to sh; its tail is       *)
(*      [UShRound.sh_round_holds_file] where echo's is                    *)
(*      [UShRest.sh_rest_holds].                                          *)
(*                                                                       *)
(*  ===== THE ONE PREMISE OF (6) THAT DOES NOT TYPECHECK TODAY ========= *)
(*                                                                       *)
(*  [UInitSh.sh_pay_of_parts] takes sh's TAG LAW, and [UkSh.ush_tag_law]  *)
(*  concludes the ECHO discipline [EchoDisc.disc h] or the taint.  The    *)
(*  file era's tag is [FileOut.ftag], whose second conjunct is            *)
(*  [FileDisc.disc_f h] or the taint, and [disc_f] does NOT imply [disc]  *)
(*  (lane STAGE's ruling: a cat line is not an echo line).  So            *)
(*  [ush_tag_law]'s [disc] must become a PARAMETER [D : list mobs ->      *)
(*  Prop] -- a NEW obligation, recorded in this lane's findings.  It does *)
(*  not surface in K2, because [UkSh.ush_rest_l] does not mention the     *)
(*  tag; it surfaces here.                                               *)
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
Require Import RiscvLang ObsTrace RiscvPtsto.
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
Require Import AppFileRec.
Require Import UFileBootAdequacy.        (* [file_prog_law], [fileΣ] *)
Local Open Scope Z_scope.

Section UInitFile.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* THE LAW, BY ITS NAME AND NOT BY A COPY OF ITS TEXT.  A restatement
     would be a second thing to keep in step with [App.xv6_app_laws]'s
     field; naming [UFileBootAdequacy.file_prog_law] is what makes the
     corollary below a one-liner. *)
  Theorem file_Hinit_boot : file_prog_law (Σ := Σ).
  Proof using.
  Admitted.

End UInitFile.

(* ===================================================================== *)
(*  THE COROLLARY -- ONE LINE.                                           *)
(*                                                                       *)
(*  [UFileBootAdequacy.file_adequacy_fileSigma] with its only remaining   *)
(*  premise discharged.  ADMITTED TRANSITIVELY (through                   *)
(*  [file_Hinit_boot]), so this is NOT added to                           *)
(*  [iris/FileAssumptions.v]: the audit target must keep printing the     *)
(*  thirteen ambient assumptions and nothing else.  The day K3's proof    *)
(*  lands, this corollary becomes the campaign's theorem and              *)
(*  [FileAssumptions.v] is repointed at it -- one line there too.         *)
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
