(* ===================================================================== *)
(*  AppFileCons.v -- THE FILE CLAIM'S CONSOLE READINGS (lane INIT-FILE). *)
(*                                                                       *)
(*  [AppEcho]'s console laws at [AppFile.file_pred], each one            *)
(*  application of [AppFile.file_pred_cons] over the echo lemma.  They    *)
(*  are exactly the conjuncts of [UInitCons.init_cons_laws_at] whose      *)
(*  view does NOT move: the accessor closes at the same [av], so the      *)
(*  file conjunct of the claim is framed and nothing about the file is    *)
(*  read.  [FileOpen.file_cons_law] is the shape and was the first of     *)
(*  them; these are the other five, gathered here rather than in          *)
(*  [FileOpen.v] because they are about the CONSOLE and not the deed,     *)
(*  and because a consumer of them should not have to take the whole      *)
(*  open cone.                                                           *)
(*                                                                       *)
(*  WHAT IS DELIBERATELY NOT HERE: the two conjuncts whose view MOVES     *)
(*  ([init_cons_laws_at]'s arm, unarm, mknod and create-other legs).      *)
(*  Those need [AppFile.file_step_free] / [file_pred_split] and the       *)
(*  [FileDeltas] legs, and one of them -- the UNARM -- is not derivable   *)
(*  from the conjunct as [UInitCons] states it at all; see the lane's     *)
(*  findings (claude-notes/projects/app-file-findings/INIT-FILE.md).      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import FsAbsDefs.
Require Import AppCfg.
Require Import AppInv.
Require Import FsConsPin.
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import EchoDisc.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FsTree.            (* [fname] *)
Require Import FsAbsDelta.        (* [cre_pre] / [delta_arm] / [delta_create] *)
Require Import FsImg.             (* [ROOTINO] *)
Require Import FileDeltas.        (* the pure legs *)
Require Import ConsoleInv.        (* [CONSOLE] *)
Local Open Scope Z_scope.

Section AppFileCons.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context (c : file_fixed) (r : file_names).

  (* ---- the claim's PURE half, at both readings ---- *)
  (* [AppEcho.echo_fs_pure_acc]'s twin.  It needs no accessor at all: the
     file claim IS the taint or the pure half beside its two state
     conjuncts, so the reading is a destructuring. *)
  Lemma file_fs_pure_acc (av : aview) :
    file_pred c r av -∗
    file_pred c r av ∗ (⌜file_fs_pure av⌝ ∨ file_taint c).
  Proof using .
    rewrite /file_pred. iIntros "[#HT | (%Hp & Hcs & Hf)]".
    - iSplitR; [ by iLeft | by iRight ].
    - iSplitL "Hcs Hf"; [ | by iLeft ].
      iRight. iFrame "Hcs Hf". by iPureIntro.
  Qed.

  (* ...AND THE WEAKENING EVERY LANDED CONSUMER READS
     ([FileFsPure.file_fs_pure_echo]): [UInitSh.init_sh_slot_core] and
     [UShEcho.sh_echo_slot_of_fs_pure] are stated at [echo_fs_pure], and
     this is the one line that lets the file era feed them. *)
  Lemma file_echo_fs_pure_acc (av : aview) :
    file_pred c r av -∗
    file_pred c r av ∗ (⌜echo_fs_pure av⌝ ∨ file_taint c).
  Proof using .
    iIntros "Hp". iDestruct (file_fs_pure_acc av with "Hp") as "[Hp Hr]".
    iFrame "Hp". iDestruct "Hr" as "[%Hf | HT]"; [ | by iRight ].
    iLeft. iPureIntro. exact (file_fs_pure_echo av Hf).
  Qed.

  (* ---- the key's ABSENCE law ([AppEcho.echo_cons_abs_law]) ---- *)
  Lemma file_cons_abs_law :
    ⊢ □ (∀ v : aview, cons_key (fn_cons r) -∗ file_pred c r v -∗
           file_pred c r v ∗ cons_key (fn_cons r)
           ∗ (⌜cons_absent v⌝ ∨ file_taint c)).
  Proof using .
    iDestruct (echo_cons_abs_law c.1 (fn_cons r)) as "#Hl".
    iIntros "!>" (v) "Hk Hp".
    iDestruct (file_pred_cons c r v with "Hp") as "[He Hback]".
    iDestruct ("Hl" $! v with "Hk He") as "(He & Hk & Hc)".
    iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    iFrame "Hk". rewrite /file_taint. iExact "Hc".
  Qed.

  (* ---- the SEAL's law ([AppEcho.echo_cons_never_law]) ---- *)
  Lemma file_cons_never_law :
    ⊢ □ (cons_never (fn_cons r) -∗
           □ (∀ v : aview, file_pred c r v -∗
                file_pred c r v ∗ (⌜cons_absent v⌝ ∨ file_taint c))).
  Proof using .
    iDestruct (echo_cons_never_law c.1 (fn_cons r)) as "#Hl".
    iIntros "!> #Hn". iDestruct ("Hl" with "Hn") as "#Hl'".
    iIntros "!>" (v) "Hp".
    iDestruct (file_pred_cons c r v with "Hp") as "[He Hback]".
    iDestruct ("Hl'" $! v with "He") as "[He Hc]".
    iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* ---- the SEAL STEP ([AppEcho.echo_cons_seal_step]) ---- *)
  Lemma file_cons_seal_step (av : aview) :
    cons_key (fn_cons r) -∗ file_pred c r av ==∗
      file_pred c r av ∗ (cons_never (fn_cons r) ∨ file_taint c).
  Proof using .
    iIntros "Hk Hp".
    iDestruct (file_pred_cons c r av with "Hp") as "[He Hback]".
    iMod (echo_cons_seal_step c.1 (fn_cons r) av with "Hk He") as "[He Hc]".
    iModIntro. iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* ---- the FLAG's birth ([AppEcho.echo_cons_shoot]) ---- *)
  Lemma file_cons_shoot (av : aview) (i : Z) :
    cons_present_at i av ->
    file_pred c r av ==∗
      file_pred c r av ∗ (cons_made (fn_cons r) i ∨ file_taint c).
  Proof using .
    intros Hpr. iIntros "Hp".
    iDestruct (file_pred_cons c r av with "Hp") as "[He Hback]".
    iMod (echo_cons_shoot c.1 (fn_cons r) av i Hpr with "He") as "[He Hc]".
    iModIntro. iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* =================================================================== *)
  (*  THE TWO MOVING-VIEW LEGS THAT DO GO THROUGH                        *)
  (*                                                                     *)
  (*  [UInitCons.init_cons_laws_at]'s (d) and (f).  Here the view MOVES,  *)
  (*  so [file_pred_cons] is useless -- it closes only at the same [av].  *)
  (*  (d) touches neither the console's ghost nor [f], so it is           *)
  (*  [AppFile.file_step_free] at four landed [FileDeltas] legs; (f) IS   *)
  (*  the console's own create, so the echo half moves by echo's own law  *)
  (*  and the file half rides across on [AppFile.file_pred_split] /       *)
  (*  [file_pred_join].                                                   *)
  (*                                                                     *)
  (*  THE OTHER TWO -- (e) the UNARM and (g) the create at ANOTHER name   *)
  (*  -- do NOT go through at this claim as [init_cons_laws_at] states    *)
  (*  them.  The lane's findings say exactly why and what each costs.     *)
  (* =================================================================== *)
  Local Notation cdev := (ADev CONSOLE 0).

  Lemma file_cons_arm_nd : forall e : gmap fname Z, cdev <> ADir e.
  Proof using . exact FileDeltas.cons_dev_nondir. Qed.

  (* ---- (d) THE ARM: a row [ialloc] just took, at the console's node ---- *)
  Lemma file_cons_arm (av : aview) (i : Z) :
    av !! i = None ->
    file_pred c r av -∗ file_pred c r (delta_arm i cdev av).
  Proof using .
    intros Hfree.
    iApply (file_step_free c r av (delta_arm i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_arm i cdev av Hfree Hp)
              (fun Hab => FileDeltas.cons_absent_arm_nd i cdev av
                            file_cons_arm_nd Hab)
              (fun j Hpr => FileDeltas.cons_present_arm_nd j i cdev av
                              Hfree Hpr)
              (fun s Hok => FileDeltas.f_ok_arm i cdev av s Hfree
                              file_cons_arm_nd Hok)).
  Qed.

  (* ---- (f) THE CONSOLE'S OWN CREATE ---- *)
  Lemma file_cons_mknod (av : aview) (ents : gmap fname Z) (nl : nat)
      (i : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i cdev ->
    cons_key (fn_cons r) -∗ file_pred c r av -∗
    file_pred c r (delta_create FsImg.ROOTINO fname_console i cdev av).
  Proof using .
    intros Hpre. iIntros "Hk Hp".
    iDestruct (file_pred_split c r av with "Hp") as "[He Hres]".
    iDestruct (echo_cons_mknod c.1 (fn_cons r) av ents nl i Hpre
                 with "Hk He") as "He".
    iApply (file_pred_join c r _ with "He").
    iDestruct "Hres" as "[#Ht | [%Hp Hf]]"; [ by iLeft | ].
    iRight. iSplitR.
    { iPureIntro.
      exact (FileDeltas.file_fs_pure_create FsImg.ROOTINO fname_console
               ents nl i cdev av Hpre file_cons_arm_nd Hp). }
    iApply (f_state_mono c r av (delta_create FsImg.ROOTINO fname_console
                                   i cdev av)
              (fun s Hok =>
                 FileDeltas.f_ok_create_other FsImg.ROOTINO fname_console
                   ents nl i cdev av s Hpre file_cons_arm_nd
                   (or_intror FileDeltas.fname_console_ne_f) Hok)
              with "Hf").
  Qed.

End AppFileCons.
