(* ===================================================================== *)
(* UInitBootAdequacy.v -- E2's B3: the whole-system theorem at echo's     *)
(* era, with every obligation of the application record discharged        *)
(* EXCEPT [Hphi] (E5's) and what the rest of the arc still owes on the    *)
(* shell's side.                                                         *)
(*                                                                       *)
(* WHY IT IS ITS OWN FILE AND NOT THE BOTTOM OF [UInitBoot.v].  This      *)
(* statement needs the ADEQUACY CONE -- [RiscvAdequacy.boot_fixedGS],     *)
(* [SystemAdequacy.xv6_slot], [FsCfgBoot.fs_boot_image_wf],              *)
(* [FsImgDisk.fsimg_P], [iris.program_logic.adequacy] -- and a [Require   *)
(* Import App] brings none of it along ([App.v] is not a [Require         *)
(* Export]).  Pulling that cone into [UInitBoot.v], which is a            *)
(* proofmode-heavy u-tier assembly full of [UexecSG.sbundle] wand towers, *)
(* makes the elaboration blow up: measured at 54 GB RSS in 64 seconds     *)
(* (and 489 GB in nine minutes, before the build cap was tightened).      *)
(* Split, each file carries one cone and both elaborate promptly.  The    *)
(* SAME shape of rule is already in durable-notes for the other           *)
(* direction ("do not import application-level files into the            *)
(* proofmode-heavy walks").                                              *)
(*                                                                       *)
(* WHAT IT TAKES FROM THE LANE: exactly [UInitBoot.echo_Hinit_boot].      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
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
Require Import FsImg.
Require Import ProcAvail.
Require Import Xv6G.
Require Import UserFd.
Require Import SystemAdequacy.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import App.                (* [xv6_app_adequacy] and the record *)
Require Import AppEcho.            (* [app_echo] and its obligations *)
Require Import EchoOut.            (* [echoOutG]: the class the record's four
                                      claims and its ledger are stated at
                                      (lane ECHO-OUT part 5) *)
Require Import UInitBoot.          (* [echo_Hinit_boot] -- E2's discharge *)
(* ===================================================================== *)
(*  6.  THE ADEQUACY STATEMENT E2 CLOSES (B3)                             *)
(*                                                                       *)
(*  [App.xv6_app_adequacy] at [AppEcho.app_echo], with every obligation   *)
(*  of the record discharged and only what the rest of the arc still owes *)
(*  ON THE SHELL'S SIDE left as a hypothesis.  [Hphi] WAS one of them and *)
(*  IS NOT ANY MORE (lane ECHO-OUT part 5): the conclusion is read off    *)
(*  the application's own ledger by [AppEcho.echo_Hphi_R] through         *)
(*  [RiscvAdequacy.obs_ledger_at_phi], so the theorem's hypothesis list   *)
(*  is one shorter and its CONCLUSION is [AppEcho.echo_phi] -- "if the    *)
(*  console input kept the discipline, every power cycle's output is a    *)
(*  prefix of the transcript its input calls for".                        *)
(* ===================================================================== *)
Section EchoAdequacy.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  (* the echo claims' class (lane ECHO-OUT part 5) *)
  Context `{!echoOutG Σ}.

  (* THE NAME IS KEPT AND IT IS NOW A MISNOMER: the theorem is no longer
     modulo [Hphi] (lane ECHO-OUT part 5 closed it), and as of lane R3 it
     is not modulo anything about the shell's program either -- [Hsh_owed]
     is gone.  What is left are the machine model, the disk image and the
     thirteen ambient assumptions the audit prints. *)
  Theorem echo_adequacy_modulo_phi
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (* ---- NOTHING ABOUT THE SHELL'S PROGRAM IS OWED ANY MORE.
             [Hsh_owed] IS GONE (lane R3).  It had two Coq-level
             entailments at [UexecExecInst.uprogSG_free]:

               (1) [(⊢ UkSh.sh_deps (PS := uprogSG_free))], the FREE WRITE
                   LAW -- "a write(16) counts as paid without the era's
                   credential".  Lane EXEC-SEAM (D) deleted it: the paid
                   walks spend write's deposit under the TAINT, where it is
                   the application's own supply
                   ([UexecExecMint.udepw_law_of_sup_write]), and init's
                   diagnostics on a closed descriptor pay through the
                   closed-fd leaf, which reaches no wire.

               (2) [(⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)], the shell's
                   REST-OF-LINE obligation -- "for EVERY taint and EVERY
                   credential family, the command loop's body holds the
                   line fact".  It is deleted here, and [UInitSh.
                   sh_pay_rest] with it: the body's one proof
                   ([UkShFork.ushf_rest_of_body]) needs the paid child's
                   law, a killed child's credential and sh's fork panic --
                   facts about THE ERA's families, false for some families
                   -- so the [∀ T Wc Wb Pm] form could never be supplied.
                   [UShRest.sh_rest_holds] discharges the obligation at the
                   echo era's own families instead, inside
                   [UInitBoot.echo_Hinit_boot].

             sh's CONSOLE READ LEAF was a third conjunct from lane
             ECHO-OUT part 5 until lane IO-LEAF M5 paid it. ---- *)
      (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
      (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                sb nib cov)
      (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
      (Hsb : sb = fsimg_sb) (Hcov : cov = fsimg_cov) :
    forall (n : nat) (κs : list mobs) t2 g2,
      language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
        κs (t2, g2) ->
      (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
      /\ app_phi app_echo g2 κs.
  Proof.
    intros n κs t2 g2 Hn.
    (* EVERY OBLIGATION GOES IN AS A HOLE, and that is not a style choice.
       Handing [xv6_app_adequacy] its fifteen arguments at once makes the
       elaborator unify each one against a record field whose type it is
       still solving, and it does not come back (measured: 47 GB RSS in 59
       seconds, killed by the build cap; the theorem's STATEMENT and these
       intros elaborate promptly, so the blow-up is this application and
       nothing before it).  With holes, each obligation is checked against
       a type that is already known. *)
    (* FIFTEEN HOLES, AND THE BULLETS IN THE ORDER [refine] LEAVES THEM.
       Handing [xv6_app_adequacy] its arguments instead of holes makes the
       elaborator unify each one against a record field whose type it is
       still solving, and it does not come back (measured: 47 GB RSS in 59
       seconds).  Offering the same [exact]s to every goal with a [try
       first [...]] sweep is worse: each is then tried against
       [Hinit_boot]'s goal as well, which is that unification twice over
       (493 GB in nine minutes, killed).  With holes the elaboration is
       prompt -- and THREE of the fifteen never become goals at all:
       [HRt], [Htagp] and [Htagt] are fixed by unification, because
       [Hphi]'s own statement above names [echo_Htagp c] and [echo_Htagt
       c] inside [boot_fixedGS].  The twelve that remain are these, in
       this order (read off the elaborator, not guessed). *)
    (* THREE MORE HOLES since lane KILL-PAY (K1): [Hkillp] and [Hkillt] are
       fixed by unification the way [Htagp]/[Htagt] are (they are named in
       [Hphi]'s own literal above), so only [Happ_kill] becomes a goal.
       THREE MORE AGAIN since lane OUT-FUPD: [Houtt] is fixed the same way
       (it too is named in [Hphi]'s literal), so the two that become goals
       are [Happ_out_sup] and [Happ_echo]. *)
    (* ONE MORE HOLE since lane CONS-IO: [Hinpt] is fixed by unification the
       way [Houtt] is (it is named in [Hphi]'s literal above), so the only
       new goal is [Happ_in_sup]. *)
    (* ONE MORE HOLE AGAIN since lane CONS-IO milestone F: [Hwint] is fixed
       by unification the way [Hinpt] is (it is named in [Hphi]'s literal
       above), so the hole list is one longer and no new goal appears. *)
    refine (xv6_app_adequacy Σ g sb nib cov app_echo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n κs t2 g2 Hn).
    - exact echo_Hbirth.
    - exact echo_Happ_kill.
    - exact echo_Happ_out_sup.
    - exact echo_Happ_in_sup.
    - exact echo_HR0.
    - exact echo_Hpow.
    - (* POINTWISE, not as one term.  [echo_Htx]/[echo_Hrx] state the era
         identification with [fileG] and [uartGhostG] as INSTANCE binders,
         ahead of [HR]; the record field puts [HR] first and [fileG] after
         it.  [exact echo_Htx] therefore asks for one unification of two
         [box]-quantified UART bodies at once, and it does not come back
         (measured: 34 GB RSS in 45 seconds).  Introducing the field's own
         binders first turns it into an application at known arguments. *)
      
      intros HR GEN HF c r γ Heq Huart.
      exact (echo_Htx (HF := HF) HR GEN c r γ Heq Huart).
    - 
      intros HR GEN HF c r γ Heq Huart.
      exact (echo_Hrx (HF := HF) HR GEN c r γ Heq Huart).
    - exact echo_Happ_boot.
    - exact (echo_Happ_init g sb nib cov Himg Hdk Hsb Hcov).
    - (* ---- [Hinit_boot]: E2's own, and the only obligation of the
             record this lane owes.  Everything it needs is at
             [UexecExecInst.uprogSG_free],
             and [echo_Hinit_boot] now takes NO Coq-level entailment about
             the shell's program: it builds /init's slot, sh's entry
             payload and sh's tail obligation itself, off the era's links
             and the boot resource. ---- *)
      
      intros HR GEN HBs HFd HIr HPav HWc HF c r Heq Htag Hkill Hgen Hout Hin
             Hwin.
      (* the record's [app_kill] field IS [AppEcho.echo_taint] (lane
         KILL-PAY, K1); [echo_Hinit_boot] is stated at the latter, and
         unification does not delta-unfold the record literal for it. *)
      cbn [app_echo app_kill] in Hkill.
      (* ...and the [app_out] field IS [AppEcho.echo_out], for the same
         reason (lane OUT-FUPD) *)
      cbn [app_echo app_out] in Hout.
      (* THE TWO LAYERS NO LONGER HAVE TO MEET (lane ECHO-OUT part 5).  Until
         part 5 [Heq]/[Htag]/[Hkill] arrived carrying [AppEcho.echo_taint]
         at the record's PRE-STRUCTURE [mono_natG] while [echo_Hinit_boot]
         and every [AppInv] law its proof uses were at the FIXED layer's,
         and [Hgen] was rewritten to reconcile them.  The taint is stated at
         [EchoOut.echoOutG]'s own [eo_mono_nat] now -- a class this section
         binds ONCE and hands to both sides -- so there is nothing left to
         move and [Hgen] is a premise this discharge does not read. *)
      (* [GEN] is IMPLICIT and fixed by unification -- from [Hw16] first
         and [Heq] after, both of which carry the record's own [GenId].
         Naming it here would pin the wrong one: the [GEN] this field
         binds is not the one [app_echo] was elaborated at. *)
      cbn [app_echo app_in] in Hin.
      (* ...and the window token's field IS [AppEcho.echo_win] (lane
         CONS-IO milestone F), on [app_in]'s mould *)
      cbn [app_echo app_win] in Hwin.
      iIntros "#Hinv Hb Hturn".
      iApply (echo_Hinit_boot HR GEN c r
                Heq Htag Hkill Hout Hin Hwin with "Hinv Hb [Hturn]").
      cbn [app_echo app_turn]. iExact "Hturn".
    - (* [Happ_echo]: at [AppEcho.echo_out]'s E5 placeholder the console's
         output claim is trivial, so the echo justifies itself. *)
      exact echo_Happ_echo.
    - (* ---- [Hphi]: CLOSED (lane ECHO-OUT part 5).  The conclusion is a
             PURE reading of the application's trace ledger, so the crash
             slot and the power interpretation are dropped and what is left
             is [RiscvAdequacy.obs_ledger_at_phi] at [echo_Hphi_R] -- the
             ledger's own [EchoOut.echo_led_phi], whose taint premise is
             [AppEcho.echo_taint] by definition. ---- *)
      intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h.
      iIntros "_ Hauth _ _ Hled".
      iApply (obs_ledger_at_phi (app_R app_echo c) (echo_HRt c)
                (app_phi app_echo g') (fun h' => echo_Hphi_R c g' h')
                γobs h with "Hauth Hled").
    - exact Hgen0.
    - exact Hpow0.
    - exact Himg.
  Qed.



End EchoAdequacy.
(* ====================================================================== *)
(*  THE CLOSED COROLLARY -- the application theorem with NOTHING left as   *)
(*  a premise but the hardware setup.                                      *)
(*                                                                        *)
(*  [echo_adequacy_modulo_phi] above is stated over an ABSTRACT [Σ] and    *)
(*  lists the disk's well-formedness facts separately.  Neither is a       *)
(*  defect of the proof, but both are things a reader must discharge       *)
(*  before the statement says anything, and a [Print Assumptions] of a     *)
(*  CONDITIONAL statement is worth less than one of a closed one           *)
(*  (durable-notes: prefer a theorem with nothing left as a premise over   *)
(*  a shorter axiom list obtained by leaving one undischarged).  This      *)
(*  corollary closes both, on [SystemAdequacy.xv6_fs_adequacy_xv6Σ]'s      *)
(*  mould, and IT is what [iris/EchoAssumptions.v] audits.                 *)
(*                                                                        *)
(*  WHAT IT CLOSES.                                                        *)
(*                                                                        *)
(*  (1) THE FUNCTOR LIST.  Every ghost class the theorem quantifies over   *)
(*  is discharged from [echoΣ] by the standard [subG] instances, so -- the *)
(*  ghost state is realisable -- is CHECKED rather than claimed.  This     *)
(*  matters more than it looks: a [Σ]-generic theorem whose class          *)
(*  constraints no concrete [Σ] satisfies is VACUOUS, and nothing in a     *)
(*  build sees that (durable-notes, the Vacuity section).                  *)
(*  [EchoOut.echoOutΣ] was written for this corollary and had no user      *)
(*  until now.                                                             *)
(*                                                                        *)
(*  (2) THE IMAGE.  [Himg]/[Hdk] follow from the one hardware equation by  *)
(*  the same two steps the system theorem takes: [Hdisk] rewrites the      *)
(*  machine's disk to the literal image, [SystemAdequacy.fsimg_image_wf]   *)
(*  (a closed lemma) closes the well-formedness, and [FsImgDisk.fsimg_P]   *)
(*  IS [fs_blocks fsimg_dk] by definition, so the block equation is        *)
(*  [reflexivity] -- no [vm_compute] on 2,048,000 bytes.  [Hsb]/[Hcov]     *)
(*  are [eq_refl] once [sb]/[cov] are instantiated at the parsed           *)
(*  superblock and the coverage.                                           *)
(*                                                                        *)
(*  WHAT IT DOES NOT CLOSE, and cannot: [Hdisk] itself -- the machine is   *)
(*  switched on with the disk mkfs wrote.  That is a statement about the   *)
(*  HARDWARE SETUP, not about the file system, and                         *)
(*  [xv6_fs_adequacy_xv6Σ] assumes exactly the same thing.                 *)
(*                                                                        *)
(*  THE CONCLUSION MENTIONS NO IRIS.  [AppEcho.echo_phi] does not depend   *)
(*  on [Σ], so [app_phi app_echo] unfolds to a proposition about the       *)
(*  observable trace alone, and it is spelled out here rather than left    *)
(*  behind the record: IF the console input kept the discipline            *)
(*  ([EchoDisc.disc] -- the user types the echo line over and over,        *)
(*  waiting for the prompt and for each byte's echo), THEN every power     *)
(*  cycle's console output is a legal session transcript                   *)
(*  ([EchoDisc.good_out]).  A reader needs no separation logic to read it. *)
(* ====================================================================== *)

(* The shell's line-choice list.  Bundled with its own [subG] instance for
   the reason every Iris library does it: the generic [subG_inG] cannot be
   applied to a bare [GFunctor] entry of a longer list without one. *)
Definition echoLineΣ : gFunctors := #[ GFunctor (mono_listR (leibnizO Z)) ].

Global Instance subG_echoLineΣ {Σ} :
  subG echoLineΣ Σ -> inG Σ (mono_listR (leibnizO Z)).
Proof. solve_inG. Qed.

Definition echoΣ : gFunctors :=
  #[ xv6Σ                (* the system theorem's own list                  *)
   ; bioslotΣ            (* not in [xv6Σ]: the bio escrow's slot camera    *)
   ; echoOutΣ            (* the echo claims' four ghosts                   *)
   ; echoLineΣ           (* the shell's line-choice list                   *)
   ].

Corollary echo_adequacy_echoΣ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ (disc κs -> Forall good_out (cycles_of κs)).
Proof.
  assert (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                   fsimg_sb fsimg_nib fsimg_cov)
    by (rewrite Hdisk; exact fsimg_image_wf).
  assert (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
    by (rewrite Hdisk; reflexivity).
  intros n κs t2 g2 Hn.
  exact (echo_adequacy_modulo_phi (Σ := echoΣ) g fsimg_sb fsimg_nib fsimg_cov
           Hgen0 Hpow0 Himg Hdk eq_refl eq_refl n κs t2 g2 Hn).
Qed.
