(* ===================================================================== *)
(*  AppPipeCons.v -- THE PIPE CLAIM'S CONSOLE READINGS (lane PIPE-CLAIM). *)
(*                                                                       *)
(*  [AppEcho]'s console laws at [AppPipeClaim.pipe_pred] -- i.e. the      *)
(*  NINE conjuncts of [UInitCons.init_cons_laws_at] at a claim that is    *)
(*  not echo's, which is what /init's console dance needs before          *)
(*  SH-PIPE-ROUND can run a round at the pipeline record.  Upstream's     *)
(*  [AppFileCons.v] is the mould, file for file; this one is SHORTER for  *)
(*  two reasons, both worth stating because they are the whole of what    *)
(*  the pipeline claim costs over the echo one:                           *)
(*                                                                       *)
(*   - THE SAME-VIEW LAWS ARE ONE ACCESSOR EACH.  [pipe_pred_cons] closes *)
(*     at the same [av], so the /cat conjunct is framed and nothing about *)
(*     /cat is read -- exactly as [AppFile.file_pred_cons] frames the     *)
(*     deed.                                                              *)
(*                                                                       *)
(*   - THE MOVING-VIEW LAWS ARE ONE LEMMA.  [pipe_step_of_echo] below     *)
(*     takes the echo-side move as a WAND and the [file_fs_pure]          *)
(*     preservation as a Prop, and every one of the four legs (arm,       *)
(*     unarm, the console's own create, a create elsewhere) is that       *)
(*     lemma at one [AppEcho] lemma and one [FileDeltas] leg.  The file   *)
(*     application needs a four-premise [file_step_free] and a case       *)
(*     analysis per leg because its claim carries a DEED whose row the    *)
(*     step might be touching; the pipe claim carries no deed, so there   *)
(*     is nothing to separate.                                           *)
(*                                                                       *)
(*  ONE CONSEQUENCE IS WORTH FLAGGING: conjunct (g) -- a create at some   *)
(*  other (d, nm) -- needs only [init_cons_laws_at]'s FIRST side          *)
(*  condition here.  Lane INIT-FILE had to add a SECOND one               *)
(*  ([d <> ROOTINO \/ nmn <> fname_f]) because a device called `f` in the *)
(*  root refutes the file claim's deed conjunct at every deed value; the  *)
(*  pipeline claim has no deed and ignores that premise.                  *)
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
Require Import AppPipeClaim.
Require Import FsTree.            (* [fname] *)
Require Import FsAbsDelta.        (* [cre_pre] / [delta_arm] / [delta_create] *)
Require Import FsImg.             (* [ROOTINO] *)
Require Import FileDeltas.        (* the pure legs, upstream's, READ-ONLY *)
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import FsShPin.
Require Import FsEchoPin.
Require Import FsCatPin.
Require Import ConsoleInv.        (* [CONSOLE] *)
Local Open Scope Z_scope.

Section AppPipeCons.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context (γ : echo_fixed) (r : echo_names).

  Local Notation cdev := (ADev CONSOLE 0).

  Lemma pipe_cons_arm_nd : forall e : gmap fname Z, cdev <> ADir e.
  Proof using . exact FileDeltas.cons_dev_nondir. Qed.

  (* =================================================================== *)
  (*  1.  THE CLAIM'S PURE HALF, AT ALL THREE READINGS                    *)
  (* =================================================================== *)

  (* (b) of [init_cons_laws_at], at [Pure := FileFsPure.file_fs_pure]. *)
  Lemma pipe_fs_pure_acc (av : aview) :
    pipe_pred γ r av -∗
    pipe_pred γ r av ∗ (⌜file_fs_pure av⌝ ∨ echo_taint γ).
  Proof using .
    rewrite /pipe_pred. iIntros "[#HT | (%Hp & Hcs)]".
    - iSplitR; [by iLeft | by iRight].
    - iSplitL "Hcs"; [| by iLeft]. iRight. iFrame "Hcs". by iPureIntro.
  Qed.

  (* ...AND THE WEAKENING EVERY LANDED CONSUMER READS.
     [UInitSh.init_sh_slot_core] and [UShEcho.sh_echo_slot_of_fs_pure] are
     stated at [echo_fs_pure] as a CONSTANT, so this one line is what lets
     a pipeline era feed them unchanged -- the same line
     [AppFileCons.file_echo_fs_pure_acc] is for the file era. *)
  Lemma pipe_echo_fs_pure_acc (av : aview) :
    pipe_pred γ r av -∗
    pipe_pred γ r av ∗ (⌜echo_fs_pure av⌝ ∨ echo_taint γ).
  Proof using .
    iIntros "Hp". iDestruct (pipe_fs_pure_acc av with "Hp") as "[Hp Hr]".
    iFrame "Hp". iDestruct "Hr" as "[%Hf | HT]"; [| by iRight].
    iLeft. iPureIntro. exact (file_fs_pure_echo av Hf).
  Qed.

  (* ...AND THE READING THE WHOLE LANE EXISTS FOR: /cat is the image's
     binary at inum 3 at every view the claim holds of.  This is what
     SH-PIPE-ROUND's exec of /cat stands on and what the echo claim could
     not give ([AppPipeClaim]'s header). *)
  Lemma pipe_cat_pins_acc (av : aview) :
    pipe_pred γ r av -∗
    pipe_pred γ r av ∗ (⌜era0_cat_pins av⌝ ∨ echo_taint γ).
  Proof using .
    iIntros "Hp". iDestruct (pipe_fs_pure_acc av with "Hp") as "[Hp Hr]".
    iFrame "Hp". iDestruct "Hr" as "[%Hf | HT]"; [| by iRight].
    iLeft. iPureIntro. exact (file_fs_pure_cat av Hf).
  Qed.

  (* =================================================================== *)
  (*  2.  THE SAME-VIEW CONSOLE LAWS                                      *)
  (*                                                                     *)
  (*  Each is one application of [AppPipeClaim.pipe_pred_cons] over the   *)
  (*  [AppEcho] lemma: the accessor closes at the same [av], so the /cat  *)
  (*  conjunct is framed and never read.                                  *)
  (* =================================================================== *)

  (* (i) THE PRESENT LAW THE SECOND OPEN RUNS ON *)
  Lemma pipe_cons_law (i : Z) :
    cons_made r i -∗
    □ (∀ v : aview, pipe_pred γ r v -∗
         pipe_pred γ r v ∗ (⌜cons_present_at i v⌝ ∨ echo_taint γ)).
  Proof using .
    iIntros "#Hm". iDestruct (echo_cons_law γ r i with "Hm") as "#Hl".
    iIntros "!>" (v) "Hp".
    iDestruct (pipe_pred_cons γ r v with "Hp") as "[He Hback]".
    iDestruct ("Hl" $! v with "He") as "[He Hc]".
    iSplitL "He Hback"; [iApply ("Hback" with "He") |]. iExact "Hc".
  Qed.

  (* (c) at the KEY arm ([AppEcho.echo_cons_abs_law]) *)
  Lemma pipe_cons_abs_law :
    ⊢ □ (∀ v : aview, cons_key r -∗ pipe_pred γ r v -∗
           pipe_pred γ r v ∗ cons_key r
           ∗ (⌜cons_absent v⌝ ∨ echo_taint γ)).
  Proof using .
    iDestruct (echo_cons_abs_law γ r) as "#Hl".
    iIntros "!>" (v) "Hk Hp".
    iDestruct (pipe_pred_cons γ r v with "Hp") as "[He Hback]".
    iDestruct ("Hl" $! v with "Hk He") as "(He & Hk & Hc)".
    iSplitL "He Hback"; [iApply ("Hback" with "He") |].
    iFrame "Hk". iExact "Hc".
  Qed.

  (* the SEAL's law ([AppEcho.echo_cons_never_law]) *)
  Lemma pipe_cons_never_law :
    ⊢ □ (cons_never r -∗
           □ (∀ v : aview, pipe_pred γ r v -∗
                pipe_pred γ r v ∗ (⌜cons_absent v⌝ ∨ echo_taint γ))).
  Proof using .
    iDestruct (echo_cons_never_law γ r) as "#Hl".
    iIntros "!> #Hn". iDestruct ("Hl" with "Hn") as "#Hl'".
    iIntros "!>" (v) "Hp".
    iDestruct (pipe_pred_cons γ r v with "Hp") as "[He Hback]".
    iDestruct ("Hl'" $! v with "He") as "[He Hc]".
    iSplitL "He Hback"; [iApply ("Hback" with "He") |]. iExact "Hc".
  Qed.

  (* the SEAL STEP ([AppEcho.echo_cons_seal_step]) *)
  Lemma pipe_cons_seal_step (av : aview) :
    cons_key r -∗ pipe_pred γ r av ==∗
      pipe_pred γ r av ∗ (cons_never r ∨ echo_taint γ).
  Proof using .
    iIntros "Hk Hp".
    iDestruct (pipe_pred_cons γ r av with "Hp") as "[He Hback]".
    iMod (echo_cons_seal_step γ r av with "Hk He") as "[He Hc]".
    iModIntro. iSplitL "He Hback"; [iApply ("Hback" with "He") |].
    iExact "Hc".
  Qed.

  (* (h) THE SHOOT: phase 2 of the commit, and the flag out *)
  Lemma pipe_cons_shoot (av : aview) (i : Z) :
    cons_present_at i av ->
    pipe_pred γ r av ==∗
      pipe_pred γ r av ∗ (cons_made r i ∨ echo_taint γ).
  Proof using .
    intros Hpr. iIntros "Hp".
    iDestruct (pipe_pred_cons γ r av with "Hp") as "[He Hback]".
    iMod (echo_cons_shoot γ r av i Hpr with "He") as "[He Hc]".
    iModIntro. iSplitL "He Hback"; [iApply ("Hback" with "He") |].
    iExact "Hc".
  Qed.

  (* (a) the supply, off the taint *)
  Lemma pipe_sup_of_taint :
    echo_taint γ -∗ app_sup_raw (pipe_pred γ) r.
  Proof using .
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /pipe_pred. iLeft. iExact "Ht".
  Qed.

  (* =================================================================== *)
  (*  3.  THE MOVING-VIEW LEGS -- ALL FOUR, THROUGH ONE LEMMA             *)
  (*                                                                     *)
  (*  The echo-side move is a WAND, so a leg that spends a credential     *)
  (*  (the console's own create spends the KEY) is the same lemma as one  *)
  (*  that spends nothing.  The [file_fs_pure] preservation is a Prop --  *)
  (*  the /cat conjunct crosses as design section 5.6 prices it -- and    *)
  (*  every instance of it is a landed [FileDeltas] leg.                  *)
  (* =================================================================== *)
  Lemma pipe_step_of_echo (av av' : aview) :
    (file_fs_pure av -> file_fs_pure av') ->
    pipe_pred γ r av -∗
    (echo_pred γ r av -∗ echo_pred γ r av') -∗
    pipe_pred γ r av'.
  Proof using .
    intros Hpure. iIntros "Hp Hmv".
    rewrite {1}/pipe_pred. iDestruct "Hp" as "[#HT | (%Hp & Hcs)]".
    { rewrite /pipe_pred. by iLeft. }
    iAssert (echo_pred γ r av) with "[Hcs]" as "He".
    { rewrite /echo_pred. iRight. iFrame "Hcs". iPureIntro.
      exact (file_fs_pure_echo av Hp). }
    iDestruct ("Hmv" with "He") as "He".
    iApply (pipe_pred_split_2 γ r av' with "He").
    rewrite /pipe_cat. iRight. iPureIntro.
    exact (file_fs_pure_cat av' (Hpure Hp)).
  Qed.

  (* ---- (d) THE ARM: a DEVICE row at an inum the view does not have ---- *)
  Lemma pipe_cons_arm (av : aview) (i : Z) :
    av !! i = None ->
    pipe_pred γ r av -∗ pipe_pred γ r (delta_arm i cdev av).
  Proof using .
    intros Hfree. iIntros "Hp".
    iApply (pipe_step_of_echo av (delta_arm i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_arm i cdev av Hfree Hp)
              with "Hp").
    iIntros "He". iApply (echo_cons_arm γ r av i CONSOLE 0 Hfree with "He").
  Qed.

  (* ---- (e) THE UNARM, at the KEY arm ---- *)
  Lemma pipe_cons_unarm_absent (av0 av : aview) (i : Z) :
    av0 !! i = None ->
    file_fs_pure av0 ->
    cons_absent av ->
    pipe_pred γ r av -∗ pipe_pred γ r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hab. iIntros "Hp".
    iApply (pipe_step_of_echo av (delta_unarm i av)
              (fun Hp => FileDeltas.file_fs_pure_unarm_fresh i av0 av
                           Hfree Hp0 Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_unarm γ r av0 av i Hfree
              (file_fs_pure_echo av0 Hp0) Hab with "He").
  Qed.

  (* ---- (e) THE UNARM, at the FLAG arm ---- *)
  Lemma pipe_cons_unarm_present (av0 av : aview) (i j : Z) :
    av0 !! i = None ->
    file_fs_pure av0 ->
    cons_present_at j av0 ->
    cons_made r j -∗ pipe_pred γ r av -∗ pipe_pred γ r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hpr0. iIntros "#Hm Hp".
    iApply (pipe_step_of_echo av (delta_unarm i av)
              (fun Hp => FileDeltas.file_fs_pure_unarm_fresh i av0 av
                           Hfree Hp0 Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_unarm_present γ r av0 av i j Hfree
              (file_fs_pure_echo av0 Hp0) Hpr0 with "Hm He").
  Qed.

  (* ---- (f) THE CONSOLE'S OWN CREATE, at the KEY arm ---- *)
  Lemma pipe_cons_mknod (av : aview) (ents : gmap fname Z) (nl : nat)
      (i : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i cdev ->
    cons_key r -∗ pipe_pred γ r av -∗
    pipe_pred γ r (delta_create FsImg.ROOTINO fname_console i cdev av).
  Proof using .
    intros Hpre. iIntros "Hk Hp".
    iApply (pipe_step_of_echo av
              (delta_create FsImg.ROOTINO fname_console i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_create FsImg.ROOTINO
                           fname_console ents nl i cdev av Hpre
                           pipe_cons_arm_nd Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_mknod γ r av ents nl i Hpre with "Hk He").
  Qed.

  (* ---- (f) THE CONSOLE'S OWN CREATE, at the FLAG arm (vacuous: the pin
         says `console` resolves and [cre_pre] says the root's map does
         not have the name) ---- *)
  Lemma pipe_cons_mknod_present (av : aview) (ents : gmap fname Z) (nl : nat)
      (i j : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i cdev ->
    cons_made r j -∗ pipe_pred γ r av -∗
    pipe_pred γ r (delta_create FsImg.ROOTINO fname_console i cdev av).
  Proof using .
    intros Hpre. iIntros "#Hm Hp".
    iApply (pipe_step_of_echo av
              (delta_create FsImg.ROOTINO fname_console i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_create FsImg.ROOTINO
                           fname_console ents nl i cdev av Hpre
                           pipe_cons_arm_nd Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_mknod_present γ r av ents nl i j Hpre with "Hm He").
  Qed.

  (* ---- (g) A CREATE AT ANOTHER (d, nm).  ONE side condition, not two:
         lane INIT-FILE's second premise is about the FILE claim's deed,
         and this claim has none. ---- *)
  Lemma pipe_cons_create_other (av : aview) (d : Z) (nmn : fname)
      (ents : gmap fname Z) (nl : nat) (i : Z) :
    cre_pre av d nmn ents nl i cdev ->
    (d <> FsImg.ROOTINO \/ nmn <> fname_console) ->
    pipe_pred γ r av -∗ pipe_pred γ r (delta_create d nmn i cdev av).
  Proof using .
    intros Hpre Hother. iIntros "Hp".
    iApply (pipe_step_of_echo av (delta_create d nmn i cdev av)
              (fun Hp => FileDeltas.file_fs_pure_create d nmn ents nl i cdev
                           av Hpre pipe_cons_arm_nd Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_create_other γ r av d nmn ents nl i CONSOLE 0
              Hpre Hother with "He").
  Qed.

  (* =================================================================== *)
  (*  4.  THE UNARM AT THE *WEAKER* PURE PARAMETER                        *)
  (*                                                                     *)
  (*  [init_cons_laws_at]'s (e) hands over [Pure av0], and the consumers  *)
  (*  in [UInitConsK] / [UShConsK] fix (b) at [EchoFsPure.echo_fs_pure],  *)
  (*  which has only THREE pins -- so [FileDeltas.file_fs_pure_unarm_     *)
  (*  fresh], which wants all four at the arm's view, does not apply.     *)
  (*  Upstream (lane INIT-FILE, [UInitConsFile]) re-does the leg off the  *)
  (*  unarmed ROW instead: a pinned row is a FILE and the row the unarm   *)
  (*  deletes is the DEVICE the arm put there, so the four pins ride      *)
  (*  across at the row and the arm's view is needed only for the ROOT.   *)
  (*  The two pure steps are re-proved here rather than imported: they    *)
  (*  are Sigma-free and importing them would put the whole FILE          *)
  (*  application's u-tier cone in front of this leaf.                    *)
  (* =================================================================== *)

  Lemma pipe_unarm_root (av0 : aview) (i : Z) :
    av0 !! i = None -> echo_fs_pure av0 -> i <> FsImg.ROOTINO.
  Proof using .
    intros Hfree (Hp & _ & _).
    destruct (FileDeltas.node_pin_root _ _ _ av0
                (FileDeltas.node_pin_of_file_pin _ _ _ av0
                   (proj2 (file_pin_init av0) Hp)))
      as (ents & nl & Hrt & _).
    intros ->. by rewrite Hrt in Hfree.
  Qed.

  Lemma pipe_fs_pure_unarm_dev (i : Z) (av : aview) (cn : absnode) :
    i <> FsImg.ROOTINO ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    file_fs_pure av -> file_fs_pure (delta_unarm i av).
  Proof using .
    intros Hroot Hrow Hcn Hp.
    assert (Hne : forall (nm : fname) (ino : Z) (bs : list (bv 8)),
              FileDeltas.node_pin nm ino (MkAnode (AFile bs) 1%nat) av ->
              i <> ino).
    { intros nm ino bs Hpin Hij. destruct Hpin as (_ & Hr).
      rewrite Hij in Hrow. rewrite Hrow in Hr.
      injection Hr as Hnode. rewrite Hcn in Hnode. discriminate Hnode. }
    destruct (FileDeltas.file_fs_pure_pins av Hp) as (H1 & H2 & H3 & H4).
    apply FileDeltas.file_fs_pure_of_pins.
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H1) H1).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H2) H2).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H3) H3).
    - exact (FileDeltas.node_pin_unarm _ _ _ i av Hroot (Hne _ _ _ H4) H4).
  Qed.

  (* ---- (e) at the KEY arm, at [echo_fs_pure av0] ---- *)
  Lemma pipe_cons_unarm_efp_absent (av0 av : aview) (i : Z) (cn : absnode) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    cons_absent av ->
    pipe_pred γ r av -∗ pipe_pred γ r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hab. iIntros "Hp".
    pose proof (pipe_unarm_root av0 i Hfree Hp0) as Hroot.
    iApply (pipe_step_of_echo av (delta_unarm i av)
              (fun Hp => pipe_fs_pure_unarm_dev i av cn Hroot Hrow Hcn Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_unarm γ r av0 av i Hfree Hp0 Hab with "He").
  Qed.

  (* ---- (e) at the FLAG arm, at [echo_fs_pure av0] ---- *)
  Lemma pipe_cons_unarm_efp_present (av0 av : aview) (i j : Z)
      (cn : absnode) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    av !! i = Some (MkAnode cn 1%nat) ->
    cn = cdev ->
    cons_present_at j av0 ->
    cons_made r j -∗ pipe_pred γ r av -∗ pipe_pred γ r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hrow Hcn Hpr0. iIntros "#Hm Hp".
    pose proof (pipe_unarm_root av0 i Hfree Hp0) as Hroot.
    iApply (pipe_step_of_echo av (delta_unarm i av)
              (fun Hp => pipe_fs_pure_unarm_dev i av cn Hroot Hrow Hcn Hp)
              with "Hp").
    iIntros "He".
    iApply (echo_cons_unarm_present γ r av0 av i j Hfree Hp0 Hpr0
              with "Hm He").
  Qed.

End AppPipeCons.
