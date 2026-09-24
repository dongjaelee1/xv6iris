(* ===================================================================== *)
(* UFileBootAdequacy.v -- THE FILE APPLICATION'S TOP-LEVEL THEOREM        *)
(* (lane ADEQUACY).                                                      *)
(*                                                                       *)
(* [App.xv6_app_adequacy] at [AppFileRec.app_file]: every obligation of   *)
(* the record discharged, the functor list fixed at a concrete [fileSig], *)
(* the disk at the literal mkfs image, and NOTHING left as a premise but  *)
(* the hardware setup AND [Hprog] -- lane SH-ROUND's [App.al_programs],   *)
(* the first process's exec bundle.                                      *)
(*                                                                       *)
(* WHICH MOULD, AND WHY.  [UInitBootAdequacy.v] (the ECHO application) is *)
(* the mould, not [UTreeAdequacy.v].  Both are the same statement one     *)
(* application over, but the tree twin's conclusion is [True] -- its      *)
(* claim's break is witnessed by no trace event, so its closed corollary  *)
(* keeps only the reducibility half and its [Hphi] is [Logic.I].  The     *)
(* file application has a real trace predicate ([FileDisc.file_phi],      *)
(* read off the ledger by [AppFileRec.file_Hphi_R]), so the shape that    *)
(* fits is the echo one: BOTH conjuncts survive into the corollary and    *)
(* [Hphi] is [RiscvAdequacy.obs_ledger_at_phi] at the application's own   *)
(* ledger.  What is taken from the tree twin is the treatment of the one  *)
(* law that is not proved yet (below).                                   *)
(*                                                                       *)
(* THE ONE THING THAT IS OWED, AND ITS SHAPE.  [App.al_programs] at this  *)
(* record -- lane SH-ROUND's -- is a SECTION HYPOTHESIS [Hprog], exactly  *)
(* as [AppFileRec.file_laws] takes it, and therefore an explicit PREMISE  *)
(* of both theorems below.  It is not an [Axiom] and not an [Admitted]:   *)
(* every result here is a theorem with it in its binder list, and the     *)
(* moment SH-ROUND lands, [Hprog] is discharged at its lemma and the two  *)
(* statements lose a premise without changing a character otherwise.      *)
(*                                                                       *)
(* WHAT THE AUDIT RULE THEREFORE SEES, AND WHAT IT DOES NOT.  A theorem's *)
(* PREMISES are part of its statement and NEVER appear in a [Print        *)
(* Assumptions] ([EchoAssumptions.v] says so about [Hsh_owed]).  So       *)
(* [make audit-file-only] prints the ambient assumptions and says nothing *)
(* about [Hprog]; the binder list of [file_adequacy_fileSig] is the       *)
(* complementary check, and [iris/FileAssumptions.v]'s header carries it. *)
(* The alternative shape -- an [Axiom], which WOULD print -- was declined *)
(* for the reason durable-notes gives: an axiom is refutable-free weight  *)
(* in the tree, [tools/lemma_diff.py] reports it as a regression, and a   *)
(* premise the audit cannot see is strictly more honest than an axiom the *)
(* audit prints and nothing ever discharges.                             *)
(*                                                                       *)
(* IS [Hprog] SATISFIABLE?  (durable-notes: a premise on the anchor       *)
(* theorem is worth a satisfiability witness before it is worth an        *)
(* audit.)  Yes, and two landed proofs of the SAME field at other records *)
(* are the witnesses: [App.app_triv_init_boot] at the generic application *)
(* and [UInitBoot.echo_Hinit_boot] at [AppEcho.app_echo], the latter      *)
(* being a fully verified /init and /sh.  The field's three equational    *)
(* premises are the ones every record gets, so nothing in [Hprog]'s shape *)
(* is peculiar to this claim; what SH-ROUND owes is its CONTENT.          *)
(*                                                                       *)
(* WHY IT IS ITS OWN FILE and not the bottom of [AppFileRec.v]:           *)
(* [UInitBootAdequacy.v]'s reason, one application over -- and here it is *)
(* weaker than there, since [AppFileRec.v] already carries the adequacy   *)
(* cone.  What this file adds is the CLOSED corollary's functor list,     *)
(* which is the only thing in the campaign that names [fileAppSig] /      *)
(* [fileOutSig], and the audit target.  Keeping it separate also keeps    *)
(* [AppFileRec.v]'s statements exactly where lane STAGE left them.        *)
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
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import VirtioModel.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FsImg.
Require Import ProcAvail.
Require Import Xv6G.
Require Import UserFd.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import InitBoot.           (* [init_boot_bundle] *)
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import App.                (* [xv6_app_adequacy] and the record *)
Require Import InodeInv.           (* [ROOTINO] *)
Require Import FileDisc.           (* [file_phi] -- the conclusion, spelled out *)
Require Import AppFile.            (* [fileAppG] / [fileAppSig] *)
Require Import EchoOut.            (* [echoOutG] / [echoOutSig] *)
Require Import FileOut.            (* [fileOutG] / [fileOutSig] *)
Require Import AppFileRec.         (* [app_file] and its ten discharged laws *)
Require UkFileIface.               (* [fifRegSig]: the tree route's device registry *)

Local Open Scope Z_scope.

Section FileAdequacy.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* =================================================================== *)
  (*  1.  THE ONE LAW THAT IS OWED, NAMED                                 *)
  (*                                                                     *)
  (*  [App.al_programs] at [app_file], VERBATIM from the class -- and      *)
  (*  verbatim from [AppFileRec]'s own [Context (Hprog : ...)], so that    *)
  (*  the instance below is the section hypothesis applied and not a       *)
  (*  restatement of it.  Giving it a NAME is what makes the premise       *)
  (*  readable in the closed corollary's binder list, which is the only    *)
  (*  place [Hprog] is ever visible (the header says why the audit cannot  *)
  (*  see it).                                                            *)
  (* =================================================================== *)
  Definition file_prog_law : Prop :=
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
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.

  Context (Hprog : file_prog_law).

  (* THE ELEVEN LAWS, AS THE INSTANCE.  [AppFileRec.file_laws] is already
     the class instance with ten fields discharged and the eleventh as its
     own section hypothesis; here it is simply applied to [Hprog].  It is
     declared at priority 0 so that resolution never reaches
     [AppFileRec.file_laws] itself, whose trailing [Hprog] argument is not
     a class and would be left to [typeclasses eauto]. *)
  #[local] Instance file_laws_at : App.xv6_app_laws (app_file (Σ := Σ)) | 0 :=
    @AppFileRec.file_laws Σ _ _ _ _ _ _ _ Hprog.

  (* =================================================================== *)
  (*  2.  THE THEOREM, over an abstract [Σ] and at the image's facts      *)
  (*                                                                     *)
  (*  [UInitBootAdequacy.echo_adequacy_modulo_phi]'s shape.  The two laws  *)
  (*  that are about an IMAGE are the arguments: era 0's claim             *)
  (*  ([AppFileRec.file_Happ_init], the literal mkfs image with no [f] in  *)
  (*  the root) and [Hphi], which is the ledger's own reading.             *)
  (* =================================================================== *)
  Theorem file_adequacy_at_img
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
      (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                sb nib cov)
      (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
      (Hsb : sb = fsimg_sb) (Hcov : cov = fsimg_cov) :
    forall (n : nat) (κs : list mobs) t2 g2,
      language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
        κs (t2, g2) ->
      (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
      /\ app_phi app_file g2 κs.
  Proof using Hprog bioslotGpreS0 echoOutG0 fdslotGpreS0 fileAppG0 fileGpreS0
              fileOutG0 inG0 irefslotGpreS0 pavGpreS0 riscvGpreS0 ufdG0
              wchGpreS0 xv6G0.
    intros n κs t2 g2 Hn.
    (* EVERY OBLIGATION GOES IN AS A HOLE ([UInitBootAdequacy]'s measured
       rule): handing [xv6_app_adequacy] its arguments at once makes the
       elaborator unify each against a record field whose type it is still
       solving, and it does not come back. *)
    refine (xv6_app_adequacy Σ g sb nib cov app_file
              (file_Happ_init g sb nib cov Himg Hdk Hsb Hcov)
              _ Hgen0 Hpow0 Himg n κs t2 g2 Hn).
    (* [Hphi]: a PURE reading of the application's trace ledger, so the
       crash slot and the power interpretation are dropped and what is left
       is [RiscvAdequacy.obs_ledger_at_phi] at [AppFileRec.file_Hphi_R] --
       the ledger's own [FileOut.file_led_phi]. *)
    intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h.
    iIntros "_ Hauth _ _ Hled".
    iApply (obs_ledger_at_phi (app_R app_file c) (al_Rt c)
              (app_phi app_file g') (fun h' => file_Hphi_R c g' h')
              γobs h with "Hauth Hled").
  Qed.

End FileAdequacy.

(* ===================================================================== *)
(*  3.  THE CLOSED COROLLARY                                             *)
(*                                                                       *)
(*  [UInitBootAdequacy.echo_adequacy_echoSig]'s two closures at the file  *)
(*  application: the FUNCTOR LIST is a concrete one, so the claim that    *)
(*  the ghost state is realisable is CHECKED, not assumed, and the        *)
(*  statement is therefore not vacuous                                    *)
(*  (durable-notes, the Vacuity section); and the IMAGE facts follow from *)
(*  the one hardware equation by [SystemAdequacy.fsimg_image_wf] and the  *)
(*  definitional [fs_blocks fsimg_dk = fsimg_P].                          *)
(*                                                                       *)
(*  WHAT IT DOES NOT CLOSE, and cannot: [Hdisk] -- the machine is         *)
(*  switched on with the disk mkfs wrote -- and [Hprog], lane SH-ROUND's. *)
(*                                                                       *)
(*  THE CONCLUSION MENTIONS NO IRIS.  [AppFileRec.file_phi] does not      *)
(*  depend on [Sigma], so [app_phi app_file] unfolds to a proposition     *)
(*  about the observable trace alone, and it is spelled out here rather   *)
(*  than left behind the record ([App.xv6_app_adequacy_triv_xv6Sig]'s own *)
(*  rule: naming the record would put the whole ghost layer into the      *)
(*  STATEMENT's trusted base).  What it says: IF the console input kept   *)
(*  the FILE discipline ([FileDisc.disc_f] -- the user types lines of the *)
(*  three shapes echo / echo > f / cat f, waiting for the prompt and for  *)
(*  each byte's echo), THEN there is one boot state per power cycle such  *)
(*  that the FIRST cycle boots with no [f] at all, every later cycle      *)
(*  boots at a chunk subsequence of an [echo ... > f] line typed in a     *)
(*  STRICTLY EARLIER cycle ([FileDisc.fadm_boot]), and each cycle's       *)
(*  console output is a prefix of the transcript its input calls for from *)
(*  that state ([FileDisc.good_out_f]).  A reader needs no separation     *)
(*  logic to read it; [FileDisc.v] is the whole specification.            *)
(* ===================================================================== *)

(* The shell's line-choice list.  Bundled with its own [subG] instance for
   [UInitBootAdequacy.echoLineSig]'s reason -- the generic [subG_inG]
   cannot be applied to a bare [GFunctor] entry of a longer list without
   one -- and spelled again HERE rather than imported from that file,
   because importing it would put the whole echo program tier
   ([UInitBoot.v] and everything under it) into this file's build cone for
   one line of functor list. *)
Definition fileLineΣ : gFunctors := #[ GFunctor (mono_listR (leibnizO Z)) ].

Global Instance subG_fileLineΣ {Σ} :
  subG fileLineΣ Σ -> inG Σ (mono_listR (leibnizO Z)).
Proof. solve_inG. Qed.

Definition fileΣ : gFunctors :=
  #[ xv6Σ                (* the system theorem's own list                  *)
   ; bioslotΣ            (* not in [xv6Σ]: the bio escrow's slot camera    *)
   ; echoOutΣ            (* the console stage's five ghosts                *)
   ; fileLineΣ           (* the shell's line-choice list                   *)
   ; fileAppΣ            (* the deed and the typed-line list               *)
   ; fileOutΣ            (* the per-era boot-state map and its bound       *)
   ; UkFileIface.fifRegΣ (* the tree route's device registry              *)
   ].

Corollary file_adequacy_fileΣ
    (Hprog : file_prog_law (Σ := fileΣ))
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ FileDisc.file_phi κs.
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                   fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (file_adequacy_at_img (Σ := fileΣ) Hprog g fsimg_sb fsimg_nib
           fsimg_cov Hgen0 Hpow0 Himg Hdk eq_refl eq_refl n κs t2 g2 Hn).
Qed.
