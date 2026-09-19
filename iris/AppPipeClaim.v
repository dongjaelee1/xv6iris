(* AppPipeClaim.v -- THE PIPELINE APPLICATION'S CLAIM ON THE FILE SYSTEM.

   Design of record: claude-notes/design/app-pipe.md section 5.6, RULED
   2026-09-18 after lane PIPE-STAGE's finding.  Lane PIPE-CLAIM
   (= PIPE-STAGE part 2), deliverable 1.

   WHY THIS FILE EXISTS.  PIPE-STAGE landed [AppPipe.app_pipe] at
   [app_pred := AppEcho.echo_pred] -- echo's claim, verbatim, as the design
   then said -- and reported that it TYPECHECKS but cannot carry the
   application: [EchoFsPure.echo_fs_pure] pins /init, /sh and /echo and NOT
   /cat, so sh's exec of /cat in a pipeline round has nothing to stand on.
   The ruling is route (a): the pipe claim is echo's SHAPE with the
   STRONGER PURE CONJUNCT, [FileFsPure.file_fs_pure] (upstream's landed
   [echo_fs_pure av /\ era0_cat_pins av], imported read-only).

   THE ONE IDEA THIS FILE IS BUILT ON.  The two claims differ ONLY in a
   PERSISTENT, [r]-FREE factor:

     pipe_pred γ r av ⊣⊢ echo_pred γ r av ∗ (echo_taint γ ∨ ⌜era0_cat_pins av⌝)

   ([pipe_pred_split] below).  The second factor -- [pipe_cat] -- names no
   instance, holds no token and is persistent, so it CROSSES THE TRANSPORT
   FOR FREE (both the original and the fresh copy are at the SAME view) and
   every law of the claim is [AppEcho]'s with that factor framed.  That is
   why no proof of [AppEcho]'s [EchoPred] section is transcribed here: the
   transport, the boot resource, the supply law and the era-0 mint are all
   reached by the split, and the only genuinely new step is reading
   [era0_cat_pins] off the image ([FileFsPure.file_fs_era0], which upstream
   landed for the FILE application and which is exactly what [AppFileRec]
   spends).

   WHAT DOES *NOT* CHANGE: [app_fixed] ([AppEcho.echo_fixed]), [app_names]
   ([echo_names]), the console state ([cons_state]) and the boot resource
   ([echo_boot]).  A pipeline round modifies no file, so the claim has no
   deed, no per-era file state and no ghost of its own -- where
   [AppFile.file_pred] carries [f_state c r av] beside the console, this
   one carries nothing. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsImgDisk.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsState.
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import FsCatPin.          (* [era0_cat_pins], [CAT_INO] *)
Require Import FsConsPin.
Require Import FileFsPure.        (* [file_fs_pure] -- upstream's, READ-ONLY *)
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import AppInv.
Require Import FsAbsDefs.
Require Import EchoOut.
Require Import AppEcho.
Local Open Scope Z_scope.

Section PipeClaim.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* ================================================================== *)
  (*  1.  THE CLAIM, AND THE FACTOR THAT IS ALL IT ADDS                  *)
  (* ================================================================== *)

  (* WHAT THE PIPELINE APPLICATION KNOWS AND THE ECHO ONE DOES NOT: at
     every view the claim holds of, /cat is the image's binary at inum 3 --
     or the console discipline has already broken, in which case the
     application has been paid off and says nothing.  PERSISTENT, TIMELESS,
     and it names NO instance, which is the whole reason the laws below are
     one-liners. *)
  Definition pipe_cat (γ : echo_fixed) (av : aview) : iProp Σ :=
    (echo_taint γ ∨ ⌜era0_cat_pins av⌝)%I.

  Global Instance pipe_cat_persistent γ av : Persistent (pipe_cat γ av).
  Proof using . rewrite /pipe_cat. apply _. Qed.
  Global Instance pipe_cat_timeless γ av : Timeless (pipe_cat γ av).
  Proof using . rewrite /pipe_cat. apply _. Qed.

  (* THE PREDICATE: tainted, or the FOUR binaries are the image's and the
     console is in one of its states.  [AppEcho.echo_pred]'s shape with
     [FileFsPure.file_fs_pure] where [echo_fs_pure] was. *)
  Definition pipe_pred (γ : echo_fixed) (r : echo_names) (av : aview)
      : iProp Σ :=
    (echo_taint γ ∨ (⌜file_fs_pure av⌝ ∗ cons_state r av))%I.

  Global Instance pipe_pred_timeless γ r av : Timeless (pipe_pred γ r av).
  Proof using . rewrite /pipe_pred. apply _. Qed.

  (* ---- THE SPLIT, both ways ---- *)

  Lemma pipe_pred_split_1 (γ : echo_fixed) (r : echo_names) (av : aview) :
    pipe_pred γ r av -∗ echo_pred γ r av ∗ pipe_cat γ av.
  Proof using .
    rewrite /pipe_pred /echo_pred /pipe_cat.
    iIntros "[#Ht | [%Hp Hc]]".
    { iSplitR; [by iLeft | by iLeft]. }
    iSplitR "".
    - iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp).
    - iRight. iPureIntro. exact (file_fs_pure_cat av Hp).
  Qed.

  Lemma pipe_pred_split_2 (γ : echo_fixed) (r : echo_names) (av : aview) :
    echo_pred γ r av -∗ pipe_cat γ av -∗ pipe_pred γ r av.
  Proof using .
    rewrite /pipe_pred /echo_pred /pipe_cat.
    iIntros "[#Ht | [%Hp Hc]] Hcat"; [by iLeft |].
    iDestruct "Hcat" as "[#Ht | %Hcat]"; [by iLeft |].
    iRight. iFrame "Hc". iPureIntro. by split.
  Qed.

  Lemma pipe_pred_split (γ : echo_fixed) (r : echo_names) (av : aview) :
    pipe_pred γ r av ⊣⊢ echo_pred γ r av ∗ pipe_cat γ av.
  Proof using .
    iSplit.
    - iApply pipe_pred_split_1.
    - iIntros "[He Hcat]". iApply (pipe_pred_split_2 with "He Hcat").
  Qed.

  (* THE ECHO APPLICATION'S CLAIM IS THIS ONE WITH /cat FORGOTTEN -- which
     is what lets every console law [AppEcho] proves at [echo_pred] be read
     here: open, apply, close with the persistent factor framed.  Stated as
     an ACCESSOR, exactly as [AppFile.file_pred_cons] is, so that nothing is
     lost. *)
  Lemma pipe_pred_cons (γ : echo_fixed) (r : echo_names) (av : aview) :
    pipe_pred γ r av -∗
    echo_pred γ r av ∗ (echo_pred γ r av -∗ pipe_pred γ r av).
  Proof using .
    iIntros "H". iDestruct (pipe_pred_split_1 with "H") as "[He #Hcat]".
    iFrame "He". iIntros "He". iApply (pipe_pred_split_2 with "He Hcat").
  Qed.

  (* the weakening on its own, for the places that never put the claim back *)
  Lemma pipe_pred_echo (γ : echo_fixed) (r : echo_names) (av : aview) :
    pipe_pred γ r av -∗ echo_pred γ r av.
  Proof using .
    iIntros "H". by iDestruct (pipe_pred_split_1 with "H") as "[$ _]".
  Qed.

  (* the era-0 shape: the pins (all FOUR of them), the console absent, the
     flag unraised.  [AppEcho.echo_pred_absent] at the stronger conjunct. *)
  Lemma pipe_pred_absent (γ : echo_fixed) (r : echo_names) (av : aview) :
    file_fs_pure av -> cons_absent av -> cons_tok r -∗ pipe_pred γ r av.
  Proof using .
    intros Hp Hc. iIntros "Ht". rewrite /pipe_pred. iRight.
    iSplitR; [by iPureIntro |]. rewrite /cons_state. iLeft.
    iSplitR; [by iPureIntro | iExact "Ht"].
  Qed.

  (* ================================================================== *)
  (*  2.  THE SUPPLY LAW                                                 *)
  (* ================================================================== *)

  (* a holder of the supply is a party the discipline has already accounted
     for.  [AppEcho.echo_taint_of_sup] through the weakening: the supply is
     a [□ ∀ av], so the pointwise weakening lifts to it with no case
     analysis of its own. *)
  Lemma pipe_sup_echo (γ : echo_fixed) (r : echo_names) :
    app_sup_raw (pipe_pred γ) r -∗ app_sup_raw (echo_pred γ) r.
  Proof using .
    rewrite /app_sup_raw. iIntros "#Hs !>" (av).
    iApply (pipe_pred_echo γ r av). iApply "Hs".
  Qed.

  Lemma pipe_taint_of_sup (γ : echo_fixed) (r : echo_names) :
    app_sup_raw (pipe_pred γ) r -∗ echo_taint γ.
  Proof using .
    iIntros "#Hs".
    iApply (echo_taint_of_sup γ r). by iApply pipe_sup_echo.
  Qed.

  (* ================================================================== *)
  (*  3.  THE TRANSPORT, AND THE FIRST PROCESS'S BOOT RESOURCE           *)
  (*                                                                    *)
  (*  [AppEcho.echo_xfer] / [echo_xfer_boot] with [pipe_cat] framed.     *)
  (*  The factor is PERSISTENT and reads the VIEW ALONE, and the         *)
  (*  transport's copy is at the SAME view -- so the copy gets it for    *)
  (*  free and the pure conjunct crosses as a Prop, exactly as design    *)
  (*  section 5.6 prices it.                                            *)
  (* ================================================================== *)

  Lemma pipe_xfer (γ : echo_fixed) : ⊢ app_xfer_raw (pipe_pred γ).
  Proof using .
    rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iAssert (▷ (echo_pred γ r av ∗ pipe_cat γ av))%I with "[H]" as "Hsp".
    { iNext. by iApply pipe_pred_split_1. }
    iDestruct "Hsp" as "[He #Hcat]".
    iDestruct (echo_xfer γ) as "#Hx".
    iMod ("Hx" $! r av with "He") as "[He Hc]".
    iDestruct "Hc" as (r') "He'".
    iModIntro. iSplitL "He".
    { iNext. iApply (pipe_pred_split_2 with "He Hcat"). }
    iExists r'. iNext. iApply (pipe_pred_split_2 with "He' Hcat").
  Qed.

  (* the boot resource is ECHO'S, unchanged: it is the console key or the
     console flag, and neither reads the file system's pins *)
  Definition pipe_boot (γ : echo_fixed) (k : nat) (r : echo_names) : iProp Σ :=
    echo_boot γ k r.

  Lemma pipe_xfer_boot (γ : echo_fixed) (k : nat) :
    ⊢ □ (∀ (r : echo_names) (av : FsAbsDefs.aview),
           ▷ pipe_pred γ r av ==∗ ▷ pipe_pred γ r av ∗
           ∃ r' : echo_names, ▷ pipe_pred γ r' av ∗ pipe_boot γ k r').
  Proof using .
    iIntros "!>" (r av) "H".
    iAssert (▷ (echo_pred γ r av ∗ pipe_cat γ av))%I with "[H]" as "Hsp".
    { iNext. by iApply pipe_pred_split_1. }
    iDestruct "Hsp" as "[He #Hcat]".
    iDestruct (echo_xfer_boot γ k) as "#Hx".
    iMod ("Hx" $! r av with "He") as "[He Hc]".
    iDestruct "Hc" as (r') "[He' Hb]".
    iModIntro. iSplitL "He".
    { iNext. iApply (pipe_pred_split_2 with "He Hcat"). }
    iExists r'. rewrite /pipe_boot. iFrame "Hb".
    iNext. iApply (pipe_pred_split_2 with "He' Hcat").
  Qed.

  (* ================================================================== *)
  (*  4.  THE ERA-0 CLAIM AT THE LITERAL IMAGE                           *)
  (*                                                                    *)
  (*  The ONE genuinely new step, and it is one line: /cat's pins are     *)
  (*  read off the image by [FileFsPure.file_fs_era0], upstream's own     *)
  (*  composition (the four transports together), which is exactly what   *)
  (*  [AppFileRec.file_Happ_init] spends.                                *)
  (* ================================================================== *)

  Lemma pipe_init_key (γ : echo_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : echo_names,
        pipe_pred γ r (abs_view (fss_inodes S)) ∗ cons_key r.
  Proof using .
    intros Hdk Hrec HS.
    iMod cons_tok_alloc as (r) "[Htok Hkey]".
    iModIntro. iExists r. iFrame "Hkey".
    iApply (pipe_pred_absent γ r _ (file_fs_era0 dk D S Hdk Hrec HS)
              (era0_recovery_cons_absent dk D S Hdk Hrec HS) with "Htok").
  Qed.

  Lemma pipe_init (γ : echo_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : echo_names, pipe_pred γ r (abs_view (fss_inodes S)).
  Proof using .
    intros Hdk Hrec HS.
    iMod (pipe_init_key γ dk D S Hdk Hrec HS) as (r) "[Hp _]".
    iModIntro. iExists r. iExact "Hp".
  Qed.

  Lemma pipe_init_img (γ : echo_fixed) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_blocks dk = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    ⊢ |==> ∃ r : echo_names,
        pipe_pred γ r (abs_view (fss_inodes
          (FsDurImg.img_state (fs_blocks dk) sb nib))).
  Proof using .
    intros Himg Hdk -> ->.
    pose proof (img_snap_ok dk ndisk fsimg_sb nib fsimg_cov Himg) as HS.
    rewrite Hdk in HS. rewrite Hdk.
    exact (pipe_init γ dk era0_D _ Hdk (era0_recovery dk Hdk) HS).
  Qed.

End PipeClaim.
