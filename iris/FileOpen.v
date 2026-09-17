(* ===================================================================== *)
(* FileOpen.v -- THE FILE APPLICATION'S OPEN AND READ SUPPLIERS: the AU   *)
(* bundles a program derives FROM THE DEED (lane F-OPEN).                 *)
(*                                                                       *)
(* Design of record: claude-notes/design/app-file.md sections 2 and 3.    *)
(* [TreeMove.v] is the mould at the tree claim and [UInitCons.v] at       *)
(* init's mknod; this file is the two of them at [AppFile]'s deed.        *)
(*                                                                       *)
(*   section 1  THE FRACTION.  A move needs the deed's whole half         *)
(*              ([AppFile.file_step_park] joins it with the claim's to    *)
(*              make the in-flight arm); a READ needs only a positive     *)
(*              fraction -- agreement settles the exact arm and validity  *)
(*              refutes the in-flight one.  That is what lets ONE deed    *)
(*              answer the two independent pieces a read-only open owes   *)
(*              (the walk's hops and the terminal observation), which is  *)
(*              the wall [PinnedObs.v] section 12 records for a live      *)
(*              claim.                                                    *)
(*   section 2  the claim read at the era's record, and the FREE step.    *)
(*   section 3  open(O_CREATE)'s bundle at `f`, at a length-0 parent      *)
(*              prefix: the arm, the unarm and the dlookup free, the      *)
(*              parent leg the two-phase move.                            *)
(*   section 4  the read commit at `f`'s inum, and its arms.              *)
(*                                                                       *)
(* WHAT IS NOT HERE, and section 5 says exactly why: the O_TRUNC leg of   *)
(* the create bundle.  It is a SECOND claim-moving piece in one syscall   *)
(* and the deed pays for one.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.       (* [bioslotG] *)
Require Import Xv6G.             (* [xv6G] *)
Require Import FdSlots.          (* [fdslotG] *)
Require Import IrefSlots.        (* [irefslotG] *)
Require Import ProcAvail.        (* [pavG] *)
Require Import FileInvDefs.      (* [fileG], and its [appcfg] field [file_app] *)
Require Import FsCfg.            (* [fsc_fs] *)
Require Import PathElems.        (* [path_elems] *)
Require Import FsTree.           (* [fname] *)
Require Import FsImg.            (* [ROOTINO] *)
Require Import FsImgCheck.       (* [fname_f] *)
Require Import FsBlocks.         (* [fs_names] *)
Require Import FsBytesGamma.     (* [fs_gamma_L] *)
Require Import OffGv.            (* [off_gv] *)
Require Import AppCfg.           (* [app_pred] / [app_run] / [MkAppcfg] *)
Require Import AppInv.           (* [app_inv], [app_body], [app_step], [appE] *)
Require Import FsAbsDelta.       (* [cre_pre], the legs *)
Require Import PieceFam.         (* [pfam] / [pf_at] *)
Require Import FsAbsCreateFire.  (* create's four commits, [cre_arm_fired] *)
Require Import UserPtTree.       (* [uptd] / [uva_wmapped]: the read's -1 arm's
                                    table and its reason *)
Require Import FsAbsReadFire.    (* [aread_commit_at] / [read_arms] *)
Require Import FsAbsEra.         (* [ep_start], [np_elems], [um_start_of] *)
Require Import SysMknodDefs.     (* [npar_cur], [npar_elems] *)
Require Import ArgPath.          (* [arg_path_of], [arg_path_of_uniq] *)
Require Import SysOpenDefs.      (* [open_au_create_at], [open_trunc_piece] *)
Require Import SpecSysOpen.      (* [open_receipt_plain] *)
Require Import PinnedObs.        (* the pinned walk and the linear cursor *)
Require Import PinnedOpen.       (* [pinned_open_bundle_dead_lin] (lane F-OPEN-2) *)
Require Import SysReadDefs.      (* [ard_count] / [ard_pre] *)
Require Import InodeInv.         (* [MAXFILE] *)
Require Import BioDefs.          (* [BSIZE] *)
Require Import UmodeArith.       (* [moi_small] *)
Require Import FsImg.            (* re-IMPORTED last: the three leaves above
                                    carry a [ROOTINO] of their own *)
Require Import ConsoleInv.
Require Import FsConsPin.        (* [cons_absent], [cons_present_at] *)
Require Import FileFsPure.
Require Import EchoDisc.         (* [line_ok] *)
Require Import EchoOut.          (* [echoOutG] *)
Require Import AppEcho.          (* [echo_taint] at the projection *)
Require Import AppFile.          (* the claim, the deed, the two phases *)
Require Import FileDeltas.       (* the pure legs *)
Require Import FsAbs.            (* [γtop] (FsAbs's own rule: LAST but one) *)
Require Import FsAbsDefs.        (* [aview] / [anode] / [arow_at] *)
Import Defs.

Local Open Scope Z_scope.

Section FileOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* =================================================================== *)
  (*  1.  THE DEED AT A FRACTION                                          *)
  (* =================================================================== *)

  (* [AppFile.fdeed] is the holder's HALF; this is the same ghost at any
     fraction.  A MOVE needs the half on the nose ([file_step_park] joins
     it with the claim's to make [fdeed_whole]); a READ needs only a
     positive fraction, and that is the whole content of this section. *)
  Definition fdq (r : file_names) (q : Qp) (s : dst) : iProp Σ :=
    ghost_var (fn_deed r) q s.

  Global Instance fdq_timeless r q s : Timeless (fdq r q s).
  Proof using . rewrite /fdq. apply _. Qed.

  Lemma fdq_deed (r : file_names) (s : dst) : fdeed r s ⊣⊢ fdq r (1/2) s.
  Proof using . reflexivity. Qed.

  Lemma fdq_split (r : file_names) (q1 q2 : Qp) (s : dst) :
    fdq r (q1 + q2) s -∗ fdq r q1 s ∗ fdq r q2 s.
  Proof using . rewrite /fdq. iIntros "H". by iApply ghost_var_split. Qed.

  Lemma fdq_join (r : file_names) (q1 q2 : Qp) (s s' : dst) :
    fdq r q1 s -∗ fdq r q2 s' -∗ fdq r (q1 + q2) s.
  Proof using .
    rewrite /fdq. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %<-.
    iCombine "H1 H2" as "H". iExact "H".
  Qed.

  (* the two readings a fraction buys *)
  Lemma fdq_agree (r : file_names) (q q' : Qp) (s s' : dst) :
    fdq r q s -∗ fdq r q' s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /fdq. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  Lemma fdq_whole_excl (r : file_names) (q : Qp) (s s' : dst) :
    fdq r q s -∗ fdeed_whole r s' -∗ False.
  Proof using .
    rewrite /fdq /fdeed_whole. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    iPureIntro. rewrite Qp.add_comm in Hq. exact (Qp.not_add_le_l _ _ Hq).
  Qed.

  (* THE READING LAW AT A FRACTION: [AppFile.file_deed_law] with the half
     weakened to any [q].  A holder of a fraction meets no in-flight arm
     ([fdq_whole_excl]) and agrees with the exact one. *)
  Lemma file_deed_law_q (c : file_fixed) (r : file_names) (q : Qp) :
    ⊢ □ (∀ (v : aview) (s : dst),
           fdq r q s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdq r q s ∗
           ((⌜f_ok v s /\ file_fs_pure v⌝) ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v s) "Hd Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iFrame "Hd". by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hw & _ & _ & _)".
      iDestruct (fdq_whole_excl with "Hd Hw") as %[]. }
    iDestruct "Hf" as (s') "(Hd' & Ht & #Hty & %Hok)".
    iDestruct (fdq_agree r q (1/2) s s' with "Hd Hd'") as %<-.
    iSplitL "Hc Hd' Ht".
    { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc". iLeft. iExists s.
      iFrame "Hd' Ht Hty". by iPureIntro. }
    iFrame "Hd". iLeft. by iPureIntro.
  Qed.

  (* ...and the same at the HALF, which is what a mover holds *)
  Lemma file_deed_law_pins (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (s : dst),
           fdeed r s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdeed r s ∗
           ((⌜f_ok v s /\ file_fs_pure v⌝) ∨ file_taint c)).
  Proof using . iApply (file_deed_law_q c r (1/2)). Qed.

  (* =================================================================== *)
  (*  2.  THE CLAIM READ AT THE ERA'S RECORD, AND THE FREE STEP           *)
  (* =================================================================== *)

  (* THE CONSOLE'S PIN, AT THE FILE CLAIM.  [AppEcho.echo_cons_law] read
     through [AppFile.file_pred_cons]: the era's FLAG -- persistent, minted
     by /init's own mknod and carried down the process chain -- says the
     console is at a FIXED inum at every view the claim admits.  It is what
     the create's UNARM leg spends: a row [ialloc] just armed is not the
     console's, and nothing in the FILE deed says so (the deed is about
     `f`). *)
  Lemma file_cons_law (c : file_fixed) (r : file_names) (jc : Z) :
    cons_made (fn_cons r) jc -∗
    □ (∀ v : aview, file_pred c r v -∗
         file_pred c r v ∗ (⌜cons_present_at jc v⌝ ∨ file_taint c)).
  Proof using .
    iIntros "#Hm". iDestruct (echo_cons_law c.1 (fn_cons r) jc with "Hm") as "#Hl".
    iIntros "!>" (v) "Hp".
    iDestruct (file_pred_cons c r v with "Hp") as "[He Hback]".
    iDestruct ("Hl" $! v with "He") as "[He Hc]".
    iSplitL "He Hback"; [ iApply ("Hback" with "He") | ].
    rewrite /file_taint. iExact "Hc".
  Qed.

  (* everything a leg of the create reads off the claim at one view *)
  Definition fclaim_facts (jc : Z) (s : dst) (v : aview) : Prop :=
    f_ok v s /\ file_fs_pure v /\ cons_present_at jc v.

  Lemma file_claim_read (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (q : Qp) (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fdq r q s -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗ fdq r q s ∗
      (⌜fclaim_facts jc s (abs_view I)⌝ ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm Hd Hka".
    iDestruct (file_deed_law_q c r q) as "#Hlaw".
    iDestruct (file_cons_law c r jc with "Hm") as "#Hcl".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iAssert (▷ (file_pred c r (abs_view I) ∗ fdq r q s
                ∗ (⌜f_ok (abs_view I) s /\ file_fs_pure (abs_view I)⌝
                   ∨ file_taint c)))%I with "[Hp Hd]" as "Hpc".
    { iNext. iApply ("Hlaw" with "Hd Hp"). }
    iDestruct "Hpc" as "[Hp [Hd Hc1]]". iMod "Hc1". iMod "Hd".
    iAssert (▷ (file_pred c r (abs_view I)
                ∗ (⌜cons_present_at jc (abs_view I)⌝ ∨ file_taint c)))%I
      with "[Hp]" as "Hpd".
    { iNext. iApply ("Hcl" with "Hp"). }
    iDestruct "Hpd" as "[Hp Hc2]". iMod "Hc2".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hd".
    iDestruct "Hc1" as "[%H1 | #HT]"; [| by iRight ].
    iDestruct "Hc2" as "[%H2 | #HT]"; [| by iRight ].
    iLeft. iPureIntro. rewrite /fclaim_facts. split_and!;
      [ exact (proj1 H1) | exact (proj2 H1) | exact H2 ].
  Qed.

  (* THE FREE STEP at the era's record: [AppFile.file_step_free] wrapped in
     [AppInv.app_step]'s shape.  [file_app_step_park]'s twin, with no
     resource at all. *)
  Lemma file_app_step_free_at (c : file_fixed) (r : file_names)
      (i : Z) (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (file_fs_pure (abs_view I) -> file_fs_pure av') ->
    (cons_absent (abs_view I) -> cons_absent av') ->
    (forall j, cons_present_at j (abs_view I) -> cons_present_at j av') ->
    (forall s : dst, f_ok (abs_view I) s -> f_ok av' s) ->
    ⊢ app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. rewrite /app_step.
    iIntros (n') "%Hav Hp". rewrite Heq. cbn [app_pred app_run app_names].
    rewrite Hav. iModIntro. iNext.
    iApply (file_step_free c r _ _ Hpins Hab Hpr Hok with "Hp").
  Qed.

  (* =================================================================== *)
  (*  3.  open(O_CREATE)'s BUNDLE AT `f`                                  *)
  (*                                                                      *)
  (*  [TreeMove.tree_open_create_au]'s mould at the FILE deed, and         *)
  (*  [UInitCons.init_cons_mknod_bundle]'s at a FILE child: the parent     *)
  (*  prefix of `f` is EMPTY, so the walk is the start cursor alone and    *)
  (*  the cursor is the pure [⌜d = ROOTINO⌝]; the ARM and the UNARM and    *)
  (*  the dlookup observation are FREE; and the deed goes into exactly one *)
  (*  leg -- the ARM's -- and comes out through whichever of the parent    *)
  (*  leg and the unarm actually fired (the permit's own discipline,       *)
  (*  [FsAbsCreateFire.acre_commit_at_gen]'s note).                        *)
  (* =================================================================== *)

  (* ---- 3a.  THE FAMILIES ---- *)

  Definition file_arm_fam (c : file_fixed) (r : file_names) (jc : Z) (s : dst)
      : pfam Σ (aview -> Z -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : Z) =>
              ((⌜fclaim_facts jc s av⌝ ∗ fown r s) ∨ file_taint c)%I)
           (fown r s).

  Definition file_unarm_fam (c : file_fixed) (r : file_names) (s : dst)
      : pfam Σ (aview -> Z -> iProp Σ) :=
    MkPfam (fun (_ : aview) (_ : Z) => (fown r s ∨ file_taint c)%I) True%I.

  (* the parent leg's receipt: at `f`'s own create the deed AT THE NEW
     STATE -- present, empty, at the inum the arm chose -- at any other
     name the deed back, or the taint *)
  (* THE FIRST ARM CARRIES THE CLAIM'S READING AT THE LEG'S OWN VIEW
     (lane F-OPEN-2).  A create at any name but `f` leaves the deed alone,
     and the three pure facts it read there are what the O_TRUNC leg
     downstream spends to identify the row the truncate reaches: the child
     is [AFile []] at nlink 1 ([cre_pre]), so it is none of the four pinned
     binaries by LENGTH, and it is `f`'s own inum only if `f` is empty. *)
  Definition file_cre_recv (c : file_fixed) (r : file_names) (jc : Z)
      (s : dst) : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (av : aview) (d : Z) (nm : fname) (i : Z) =>
      ((⌜nm <> fname_f /\ fclaim_facts jc s av⌝ ∗ fown r s)
       ∨ (⌜s = None /\ d = ROOTINO /\ nm = fname_f⌝ ∗ fown r (Some (i, [])))
       ∨ file_taint c)%I.

  Definition file_cre_fam (c : file_fixed) (r : file_names) (jc : Z)
      (s : dst) : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (file_cre_recv c r jc s) True%I.

  (* ---- 3b.  THE ARM LEG: free, and it MINTS THE PERMIT ---- *)

  Lemma file_arm_commit (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (bsc : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fown r s -∗
    aarm_commit_at (fs_gamma_L γfs) appE (AFile bsc)
      (file_arm_fam c r jc s).(pf_recv).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm [Hd Ht]".
    assert (Hnd : forall e : gmap fname Z, AFile bsc <> ADir e)
      by (intros e Hc; discriminate Hc).
    rewrite /aarm_commit_at. iIntros (I i) "%Hnone %Hsome Hka".
    iMod (file_claim_read γfs c r jc s (1/2) I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf as (Hok & Hpure & Hcons).
    iModIntro. iFrame "Hka". iSplitR "Hd Ht".
    { iApply (file_app_step_free_at c r i I _ Heq).
      - intros _. exact (file_fs_pure_arm i (AFile bsc) (abs_view I) Hnone Hpure).
      - exact (cons_absent_arm_nd i (AFile bsc) (abs_view I) Hnd).
      - intros j. exact (cons_present_arm_nd j i (AFile bsc) (abs_view I) Hnone).
      - intros s'. exact (f_ok_arm i (AFile bsc) (abs_view I) s' Hnone Hnd). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
    iLeft. iFrame "Hd Ht". iPureIntro. by rewrite /fclaim_facts.
  Qed.

  (* ---- 3c.  THE UNARM LEG: free, and it SPENDS THE PERMIT ----

     The two inequalities [FsConsPin]'s unarm lemmas ask -- the armed inum
     is neither the root nor the pinned row's -- come off the ARM's own
     receipt: [FsAbsCreateFire.cre_arm_fired] says the row was ABSENT at
     the arm's view, and the receipt says what the claim held THERE.  The
     console's is the flag's ([file_cons_law]); `f`'s is the DEED'S OWN
     INUM, which is why the deed's state carries it. *)
  Lemma file_unarm_commit (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗
    aunarm_of_arm (fs_gamma_L γfs) appE (file_arm_fam c r jc s)
      (file_unarm_fam c r s).(pf_recv).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm". rewrite /aunarm_of_arm.
    iIntros (i) "Harm". rewrite /cre_arm_fired.
    iDestruct "Harm" as (av0) "[%Hfree Hrec]". cbn [pf_recv].
    rewrite /aunarm_commit_at. iIntros (I c0) "%Hrow Hka".
    iDestruct "Hrec" as "[[%Hf0 [Hd Ht]] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf0 as (Hok0 & Hpure0 & Hcons0).
    iMod (file_claim_read γfs c r jc s (1/2) I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf as (Hok & Hpure & Hcons).
    iModIntro. iFrame "Hka". iSplitR "Hd Ht".
    { iApply (file_app_step_free_at c r i I _ Heq).
      - intros _.
        exact (file_fs_pure_unarm_fresh i av0 (abs_view I) Hfree Hpure0 Hpure).
      - exact (cons_absent_unarm i (abs_view I)).
      - intros j Hj.
        (* the console is at ONE inum, so [j] is the flag's *)
        assert (Hjc : j = jc).
        { pose proof (cons_present_astep j (abs_view I) Hj) as H1.
          pose proof (cons_present_astep jc (abs_view I) Hcons) as H2.
          congruence. }
        subst j.
        exact (cons_present_unarm_fresh_nd jc i av0 (abs_view I) Hfree
                 Hcons0 Hj).
      - intros s' Hs'. rewrite (f_ok_det (abs_view I) s' s Hs' Hok).
        exact (f_ok_unarm_fresh i av0 (abs_view I) s Hfree Hok0 Hok). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
    iLeft. iFrame "Hd Ht".
  Qed.

  (* ---- 3d.  THE PARENT LEG: the two-phase move, at `f` ---- *)

  (* The name the create reached decides the leg: at `f` in the root the
     claim moves ABSENT -> present-and-empty (phase 1 parks the deed,
     phase 2 resyncs it at the new content); at any other name the claim is
     carried and the deed comes straight back.  The deed's own state
     decides which of the two is even possible -- [cre_pre] says `f` was
     ABSENT when the leg fired, so at a PRESENT deed the `f` case is
     refuted outright. *)
  Lemma file_acre_commit (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (ls : list wordline) (ws : wordline) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    acre_commit_at_gen (fs_gamma_L γfs) appE (fun _ _ => AFile [])
      (fun d : Z => ⌜d = ROOTINO⌝%I)
      (file_arm_fam c r jc s) (file_cre_fam c r jc s).(pf_recv).
  Proof using .
    intros Heq Hin Hok. iIntros "#Hinv #Hm #Hlb".
    assert (Hnd : forall e : gmap fname Z, AFile [] <> ADir e)
      by (intros e Hc; discriminate Hc).
    rewrite /acre_commit_at_gen.
    iIntros (I d i nm ents nl) "%Hpre %Hdots Harm %Hd Hka". subst d.
    rewrite /cre_arm_fired. iDestruct "Harm" as (av0) "[%Hfree Hrec]".
    cbn [pf_recv].
    iDestruct "Hrec" as "[[%Hf0 [Hd Ht]] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitR.
      { iApply (file_app_step_taint c r ROOTINO I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iRight. iRight. iExact "HT". }
    iMod (file_claim_read γfs c r jc s (1/2) I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitR.
      { iApply (file_app_step_taint c r ROOTINO I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iRight. iRight. iExact "HT". }
    destruct Hf as (Hokv & Hpure & Hcons).
    destruct (decide (nm = fname_f)) as [-> | Hne].
    - (* THE CREATE AT `f`: the deed must be ABSENT, and it moves *)
      pose proof (cre_pre_f_absent (abs_view I) ents nl i (AFile []) Hpre)
        as HNone.
      assert (Hs : s = None)
        by exact (eq_sym (f_ok_det (abs_view I) None s HNone Hokv)).
      subst s.
      destruct (file_create_at_f (abs_view I) ents nl i Hpre Hpure)
        as (Hp1 & Hp2 & Hp3 & Hp4).
      iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitL "Hd".
      { iApply (file_app_step_park c r ROOTINO I _ None (Some (i, [])) Heq
                  (fun _ => Hp1) Hp2 Hp3 (fun _ => Hp4) with "Hd []").
        rewrite -(subseq_nil (echo_chunks ws)).
        iApply (f_typed_some c ls ws [] i Hin Hok
                  (sel_ok_nil (echo_chunks ws)) with "Hlb"). }
      iIntros (I') "%Hav Hka'".
      iMod (file_resync γfs c r None (Some (i, [])) I' appE
              ltac:(set_solver) Heq
              ltac:(rewrite -(f_ok_fcontent (abs_view I') (Some (i, [])));
                    [ reflexivity | rewrite Hav; exact Hp4 ])
              ltac:(discriminate) with "Hinv Ht Hka'") as "(Hka' & Hres)".
      iModIntro. iFrame "Hka'".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iDestruct "Hres" as "[Hown | [_ #HT]]".
      + iRight. iLeft. iFrame "Hown". iPureIntro. split_and!; reflexivity.
      + iRight. iRight. iExact "HT".
    - (* ANY OTHER NAME: the claim is carried, the deed comes back *)
      assert (Hnc : nm <> fname_console).
      { intros ->. destruct Hpre as (Hdr & Hfr & _).
        pose proof (cons_present_astep jc (abs_view I) Hcons) as Hst.
        rewrite /astep /aents Hdr /= /anode_ents /= in Hst. congruence. }
      iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitR.
      { iApply (file_app_step_free_at c r ROOTINO I _ Heq).
        - exact (file_fs_pure_create ROOTINO nm ents nl i (AFile [])
                   (abs_view I) Hpre Hnd).
        - apply (cons_absent_create_nd ROOTINO nm ents nl i (AFile [])
                   (abs_view I) Hpre Hnd). by right.
        - intros j. exact (cons_present_create_nd j ROOTINO nm ents nl i
                             (AFile []) (abs_view I) Hpre Hnd).
        - intros s'. exact (f_ok_create_other ROOTINO nm ents nl i (AFile [])
                              (abs_view I) s' Hpre Hnd (or_intror Hne)). }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iLeft. iFrame "Hd Ht". iPureIntro. split; [ exact Hne | ].
      rewrite /fclaim_facts. split_and!;
        [ exact Hokv | exact Hpure | exact Hcons ].
  Qed.


  (* ---- 3e'.  WHAT THE CLAIM SAYS AT A VIEW NOBODY HOLDS A FRACTION AT

     The truncate's EXISTS disjunct has to identify a row at the view
     create's own [dirlookup] read, which is EARLIER than the [itrunc]'s
     own instant and which no deed fraction reaches: the deed's half is in
     the ARM's piece, where the create leg needs it WHOLE (its park at `f`
     joins it with the claim's), and the pieces of a bundle are
     [∗]-separated.  What IS readable there costs no fraction at all:
     [file_pred]'s non-taint arm carries [⌜file_fs_pure av⌝] and, in BOTH
     arms of [f_state], the TYPED witness of whatever state the claim is
     at ([AppFile.f_typed]'s pure part).  Together they say: if the root
     has an `f` at this view, its row is a file of FEWER THAN
     [EchoDisc.line_max] bytes -- which is exactly the premise
     [FileDeltas.f_inum_not_pinned] wants, so the truncate at that inum
     cannot be one of the four era-0 binaries.  That is the whole content
     of the dlookup family below, and it is why nothing LINEAR rides in
     it. *)

  Definition fclaim_free (v : aview) : Prop :=
    file_fs_pure v /\
    forall i : Z, astep v FsImg.ROOTINO fname_f = Some i ->
      exists bs : list (bv 8),
        v !! i = Some (MkAnode (AFile bs) 1%nat)
        /\ (length bs < EchoDisc.line_max)%nat.

  Lemma file_claim_read_free (γfs : fs_names) (c : file_fixed) (r : file_names)
      (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
      (⌜fclaim_free (abs_view I)⌝ ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iAssert (file_pred c r (abs_view I)
             ∗ (⌜fclaim_free (abs_view I)⌝ ∨ file_taint c))%I
      with "[Hp]" as "[Hp Hres]".
    { rewrite /file_pred.
      iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
      { iSplitR; [ by iLeft |]. by iRight. }
      iAssert (f_state c r (abs_view I)
               ∗ ⌜fclaim_free (abs_view I)⌝)%I with "[Hf]" as "[Hf %Hfree]".
      { rewrite /f_state.
        iDestruct "Hf" as "[Hf | Hf]".
        - iDestruct "Hf" as (s') "(Hd & Htk & #Hty & %Hok)".
          iAssert (⌜fclaim_free (abs_view I)⌝)%I as "%Hfree".
          { destruct s' as [[i0 bs0] |].
            - rewrite /f_typed.
              iDestruct "Hty" as (ls) "[_ %Hbt]". iPureIntro.
              split; [ exact Hpins |]. intros i Hst.
              destruct Hok as (Hst0 & Hrow0). rewrite Hst0 in Hst.
              injection Hst as <-. exists bs0. split; [ exact Hrow0 |].
              exact (f_bytes_typed_short ls bs0 Hbt).
            - iPureIntro. split; [ exact Hpins |]. intros i Hst.
              assert (Hab : astep (abs_view I) FsImg.ROOTINO fname_f = None)
                by exact Hok.
              rewrite Hab in Hst. discriminate. }
          iSplitL; [| by iPureIntro ].
          iLeft. iExists s'. iFrame "Hd Htk Hty". by iPureIntro.
        - iDestruct "Hf" as (s0 s1) "(Hw & Htk & #Hty & %Hok)".
          iAssert (⌜fclaim_free (abs_view I)⌝)%I as "%Hfree".
          { destruct s1 as [[i0 bs0] |].
            - rewrite /f_typed.
              iDestruct "Hty" as (ls) "[_ %Hbt]". iPureIntro.
              split; [ exact Hpins |]. intros i Hst.
              destruct Hok as (Hst0 & Hrow0). rewrite Hst0 in Hst.
              injection Hst as <-. exists bs0. split; [ exact Hrow0 |].
              exact (f_bytes_typed_short ls bs0 Hbt).
            - iPureIntro. split; [ exact Hpins |]. intros i Hst.
              assert (Hab : astep (abs_view I) FsImg.ROOTINO fname_f = None)
                by exact Hok.
              rewrite Hab in Hst. discriminate. }
          iSplitL; [| by iPureIntro ].
          iRight. iExists s0, s1. iFrame "Hw Htk Hty". by iPureIntro. }
      iSplitL "Hc Hf".
      - iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc Hf".
      - iLeft. by iPureIntro. }
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hres".
  Qed.

  (* THE EXISTS OBSERVATION'S FAMILY: the pure reading above, at the view
     create's [dirlookup] fired at.  Nothing linear -- see the note. *)
  Definition file_dlk_recv (c : file_fixed)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (av : aview) (_ : Z) (_ : fname) (_ : Z) =>
      (⌜fclaim_free av⌝ ∨ file_taint c)%I.

  Definition file_dlk_fam (c : file_fixed)
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (file_dlk_recv c) True%I.

  Lemma file_dlk_piece (γfs : fs_names) (c : file_fixed) (r : file_names) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗
    pf_at (dlookup_commit_at (fs_gamma_L γfs) appE) (file_dlk_fam c).
  Proof using .
    intros Heq. iIntros "#Hinv". rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| done ].
    rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Hka".
    iMod (file_claim_read_free γfs c r I Heq with "Hinv Hka") as "[Hka Hres]".
    iModIntro. iFrame "Hka". rewrite /file_dlk_fam /file_dlk_recv.
    cbn [pf_recv]. iExact "Hres".
  Qed.

  (* ---- 3f.  THE O_TRUNC LEG, KEYED TO THE CREATE'S OWN RECEIPT ----

     Lane F-OPEN stopped here and priced the seam; this is its
     APPLICATION half, landed.  [SysOpenDefs.atrunc_of_permit] is the
     shape -- the truncate's commit AT ONE INUM, produced from a PERMIT
     naming that inum, on [FsAbsCreateFire.aunarm_of_arm]'s mould -- and
     [SysOpenDefs.trunc_permit_cre] is the permit the FRESH arm holds: the
     create's own fired receipt, which for this claim carries the deed.

     THE TRUNCATE IS THEN FREE AT BOTH DEED VALUES, and that is the whole
     content: the row the call reached is the CHILD the create just made,
     so [cre_pre] says it is [AFile []] at nlink 1, and
       - it is none of the four pinned binaries, because a pinned row's
         content is an ELF and this one is EMPTY
         ([FileDeltas.f_inum_not_pinned] at length 0);
       - it is `f`'s own inum only if `f` was already EMPTY, because the
         two rows are the same row -- and truncating an empty `f` is the
         identity ([FileDeltas.f_ok_trunc_nil]);
       - and at every other inum the leg is [f_ok_trunc_ne].
     So the deed comes back UNMOVED on both arms: at a create under
     another name at the state it had, and at `f`'s own create at
     [Some (i, [])], which is where the parent leg already put it. *)

  (* THE RECEIPT.  Three arms and they are the three runs: the deed did
     not move (the truncate reached a row this claim does not name), the
     deed is at `f` PRESENT AND EMPTY at the row the truncate reached
     (create's own child on the FRESH run, `f`'s own row on the EXISTS
     one), or the taint. *)
  Definition file_trunc_recv (c : file_fixed) (r : file_names) (s : dst)
      : aview -> Z -> list (bv 8) -> iProp Σ :=
    fun (_ : aview) (i : Z) (_ : list (bv 8)) =>
      (fown r s
       ∨ fown r (Some (i, []))
       ∨ file_taint c)%I.

  Definition file_trunc_fam (c : file_fixed) (r : file_names) (s : dst)
      : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ) :=
    MkPfam (file_trunc_recv c r s) True%I.

  (* the pure heart: at the row [cre_pre] describes, the truncate carries
     the claim whatever the deed's state is *)
  Lemma file_trunc_free (av0 av : aview) (i : Z) (s : dst) (jc : Z) :
    av0 !! i = Some (MkAnode (AFile []) 1%nat) ->
    file_fs_pure av0 ->
    f_ok av0 s ->
    file_fs_pure av -> f_ok av s -> cons_present_at jc av ->
    file_fs_pure (delta_trunc i av)
    /\ (cons_absent av -> cons_absent (delta_trunc i av))
    /\ (forall j, cons_present_at j av -> cons_present_at j (delta_trunc i av))
    /\ f_ok (delta_trunc i av) s.
  Proof using .
    intros Hrow0 Hpure0 Hok0 Hpure Hok Hcons.
    destruct (f_inum_not_pinned av0 i [] Hpure0 Hrow0
                ltac:(rewrite /EchoDisc.line_max; cbn [length]; lia))
      as (N1 & N2 & N3 & N4).
    split_and!.
    - exact (file_fs_pure_trunc_ne i av N1 N2 N3 N4 Hpure).
    - exact (cons_absent_trunc_any i av).
    - intros j. exact (cons_present_trunc_any j i av).
    - destruct s as [[i0 bs] |]; last first.
      { apply (f_ok_trunc_ne i av None); [| exact Hok].
        intros j bs' Hc. discriminate Hc. }
      destruct (decide (i = i0)) as [Heq | Hne].
      + (* the same row: the create's child IS `f`, so `f` was empty *)
        subst i0.
        assert (Hbs : bs = []).
        { destruct Hok0 as (_ & Hrowf). rewrite Hrow0 in Hrowf. congruence. }
        subst bs. exact (f_ok_trunc_nil i i av Hok).
      + apply (f_ok_trunc_ne i av (Some (i0, bs))); [| exact Hok].
        intros j bs' Hc. injection Hc as Hj _. rewrite -Hj. exact Hne.
  Qed.

  Lemma file_trunc_of_cre (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (i : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗
    trunc_permit_cre (file_cre_fam c r jc s) i -∗
    atrunc_commit_i (fs_gamma_L γfs) appE i (file_trunc_recv c r s).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm Hperm".
    rewrite /trunc_permit_cre /cre_acre_fired.
    iDestruct "Hperm" as (d nm av0 ents nl0) "[%Hpre Hrec]".
    cbn [pf_recv]. rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
    rewrite /atrunc_commit_i. iIntros (I bs0 nl) "%Hrow Hka".
    (* the child's row, off [cre_pre] *)
    destruct Hpre as (_ & _ & Hrow0).
    iDestruct "Hrec" as "[[%Hfa [Hd Ht]] | [Hfb | #HT]]"; last first.
    { (* the taint: the step is free and the receipt is the taint *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iRight. iExact "HT". }
    - (* THE CREATE AT `f`: the deed is at [Some (i, [])] and the truncate
         is the identity there *)
      iDestruct "Hfb" as "[%Hfb [Hd Ht]]".
      destruct Hfb as (Hs & _ & _). subst s.
      iMod (file_claim_read γfs c r jc (Some (i, [])) (1/2) I Heq
              with "Hinv Hm Hd Hka") as "(Hka & Hd & [%Hf | #HT])"; last first.
      { iModIntro. iFrame "Hka". iSplitR.
        { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
        iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
        rewrite /file_trunc_recv. iRight. iRight. iExact "HT". }
      destruct Hf as (Hok & Hpure & Hcons).
      destruct (file_trunc_free (abs_view I) (abs_view I) i (Some (i, []))
                  jc (proj2 Hok) Hpure Hok Hpure Hok Hcons)
        as (Hp1 & Hp2 & Hp3 & Hp4).
      iModIntro. iFrame "Hka". iSplitR "Hd Ht".
      { iApply (file_app_step_free_at c r i I _ Heq).
        - intros _. exact Hp1.
        - exact Hp2.
        - exact Hp3.
        - intros s' Hs'.
          rewrite (f_ok_det (abs_view I) s' (Some (i, [])) Hs' Hok). exact Hp4. }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iLeft. iFrame "Hd Ht".
    - (* ANY OTHER NAME: the deed is at [s] and stays there *)
      destruct Hfa as (_ & Hf0). destruct Hf0 as (Hok0 & Hpure0 & _).
      iMod (file_claim_read γfs c r jc s (1/2) I Heq
              with "Hinv Hm Hd Hka") as "(Hka & Hd & [%Hf | #HT])"; last first.
      { iModIntro. iFrame "Hka". iSplitR.
        { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
        iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
        rewrite /file_trunc_recv. iRight. iRight. iExact "HT". }
      destruct Hf as (Hok & Hpure & Hcons).
      destruct (file_trunc_free av0 (abs_view I) i s jc Hrow0 Hpure0 Hok0
                  Hpure Hok Hcons) as (Hp1 & Hp2 & Hp3 & Hp4).
      iModIntro. iFrame "Hka". iSplitR "Hd Ht".
      { iApply (file_app_step_free_at c r i I _ Heq).
        - intros _. exact Hp1.
        - exact Hp2.
        - exact Hp3.
        - intros s' Hs'. rewrite (f_ok_det (abs_view I) s' s Hs' Hok).
          exact Hp4. }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iLeft. iFrame "Hd Ht".
  Qed.

  (* ...AND THE PIECE, as a bundle would carry it: the keyed AU beside a
     refund of [True] -- a create that fired and then failed past the
     truncate hands the deed back through the CREATE's receipt
     ([SpecSysOpen.open_post_fail_create] arm (a)), so this piece owes
     nothing on that path. *)
  (* ---- 3f'.  THE EXISTS DISJUNCT: `f` WAS THERE AND THE TRUNCATE MOVES IT

     What the permit hands on this run is the exists observation's receipt
     -- the pure reading of section 3e' at the view create's [dirlookup]
     fired at -- BESIDE THE ARM PIECE THE RUN NEVER FIRED (create found
     the name, so [ialloc] never ran), and [pf_at] is a conjunction, so
     the piece's REFUND is the deed's whole half.  With the tie
     ([d = ROOTINO] off the cursor, [nm = f] off the path's last element)
     the lookup's view says the root's `f` is the row the truncate
     reached, and the typed bound says that row is none of the four era-0
     binaries.  The rest is the two-phase move at the deed's own value. *)
  Lemma file_trunc_of_exists (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (ls : list wordline) (ws : wordline)
      (i : Z) (avx : aview) (entsx : gmap fname Z) (nlx : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    avx !! FsImg.ROOTINO = Some (MkAnode (ADir entsx) nlx) ->
    entsx !! fname_f = Some i ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    (⌜fclaim_free avx⌝ ∨ file_taint c) -∗
    fown r s -∗
    atrunc_commit_i (fs_gamma_L γfs) appE i (file_trunc_recv c r s).
  Proof using .
    intros Heq Hrowx Hentx Hin Hokw. iIntros "#Hinv #Hm #Hlb Hfree [Hd Ht]".
    rewrite /atrunc_commit_i. iIntros (I bs0 nl) "%Hrow Hka".
    (* the lookup's view, read: the root's `f` is [i], and its row is a
       SHORT file, so [i] is none of the four pinned binaries *)
    iDestruct "Hfree" as "[%Hfree | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iRight. iExact "HT". }
    assert (Hstx : astep avx FsImg.ROOTINO fname_f = Some i)
      by (rewrite /astep /aents Hrowx /= /anode_ents /=; exact Hentx).
    destruct Hfree as (Hpurex & Hrowf).
    destruct (Hrowf i Hstx) as (bsx & Hrowi & Hlenx).
    destruct (f_inum_not_pinned avx i bsx Hpurex Hrowi Hlenx)
      as (N1 & N2 & N3 & N4).
    iMod (file_claim_read γfs c r jc s (1/2) I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iRight. iExact "HT". }
    destruct Hf as (Hok & Hpure & Hcons).
    (* the three legs the truncate at a NON-PINNED row always carries *)
    assert (Hp1 : file_fs_pure (delta_trunc i (abs_view I)))
      by exact (file_fs_pure_trunc_ne i (abs_view I) N1 N2 N3 N4 Hpure).
    assert (Hp2 : cons_absent (abs_view I) ->
                  cons_absent (delta_trunc i (abs_view I)))
      by exact (cons_absent_trunc_any i (abs_view I)).
    assert (Hp3 : forall j, cons_present_at j (abs_view I) ->
                  cons_present_at j (delta_trunc i (abs_view I)))
      by (intros j; exact (cons_present_trunc_any j i (abs_view I))).
    destruct s as [[j bs] |]; last first.
    - (* THE DEED SAYS `f` IS ABSENT: nothing of this claim is at [i], so
         the truncate is free and the deed comes back unmoved. *)
      iModIntro. iFrame "Hka". iSplitR "Hd Ht".
      { iApply (file_app_step_free_at c r i I _ Heq).
        - intros _. exact Hp1.
        - exact Hp2.
        - exact Hp3.
        - intros s' Hs'. rewrite (f_ok_det (abs_view I) s' None Hs' Hok).
          apply (f_ok_trunc_ne i (abs_view I) None); [| exact Hok].
          intros j' bs' Hc. discriminate Hc. }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iLeft. iFrame "Hd Ht".
    - destruct (decide (j = i)) as [-> | Hne]; last first.
      { (* the truncate reached some OTHER row: free, deed unmoved *)
        iModIntro. iFrame "Hka". iSplitR "Hd Ht".
        { iApply (file_app_step_free_at c r i I _ Heq).
          - intros _. exact Hp1.
          - exact Hp2.
          - exact Hp3.
          - intros s' Hs'.
            rewrite (f_ok_det (abs_view I) s' (Some (j, bs)) Hs' Hok).
            apply (f_ok_trunc_ne i (abs_view I) (Some (j, bs))); [| exact Hok].
            intros j' bs' Hc. injection Hc as Hj _. rewrite -Hj.
            exact (not_eq_sym Hne). }
        iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
        rewrite /file_trunc_recv. iLeft. iFrame "Hd Ht". }
      (* THE ROW IS `f`'s OWN: the claim moves to the empty content *)
      destruct (decide (bs = [])) as [-> | Hbs].
      { (* it was empty already: the delta is the identity on the claim *)
        iModIntro. iFrame "Hka". iSplitR "Hd Ht".
        { iApply (file_app_step_free_at c r i I _ Heq).
          - intros _. exact Hp1.
          - exact Hp2.
          - exact Hp3.
          - intros s' Hs'.
            rewrite (f_ok_det (abs_view I) s' (Some (i, [])) Hs' Hok).
            exact (f_ok_trunc_nil i i (abs_view I) Hok). }
        iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
        rewrite /file_trunc_recv. iRight. iLeft. iFrame "Hd Ht". }
      assert (Hp4 : f_ok (delta_trunc i (abs_view I)) (Some (i, [])))
        by exact (f_ok_trunc_f i bs (abs_view I) Hok).
      iModIntro. iFrame "Hka". iSplitL "Hd".
      { iApply (file_app_step_park c r i I _ (Some (i, bs)) (Some (i, []))
                  Heq (fun _ => Hp1) Hp2 Hp3 (fun _ => Hp4) with "Hd []").
        rewrite -(subseq_nil (echo_chunks ws)).
        iApply (f_typed_some c ls ws [] i Hin Hokw
                  (sel_ok_nil (echo_chunks ws)) with "Hlb"). }
      iIntros (I') "%Hav Hka'".
      iMod (file_resync γfs c r (Some (i, bs)) (Some (i, [])) I' appE
              ltac:(set_solver) Heq
              ltac:(rewrite -(f_ok_fcontent (abs_view I') (Some (i, [])));
                    [ reflexivity | rewrite Hav; exact Hp4 ])
              ltac:(congruence)
              with "Hinv Ht Hka'") as "(Hka' & Hres)".
      iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv.
      iDestruct "Hres" as "[Hown | [_ #HT]]".
      + iRight. iLeft. iExact "Hown".
      + iRight. iRight. iExact "HT".
  Qed.

  (* ---- 3f''.  THE PIECE, AT THE PERMIT THE O_CREATE BUNDLE CARRIES ---- *)

  Lemma file_trunc_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (ls : list wordline) (ws : wordline)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    pf_at (atrunc_of_permit (fs_gamma_L γfs) appE
             (trunc_permit_of (fs_gamma_L γfs)
                (trunc_tie_arg M pv (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I))
                (file_arm_fam c r jc s) (file_cre_fam c r jc s)
                (file_dlk_fam c)))
      (file_trunc_fam c r s).
  Proof using .
    intros Heq Hpath Hlast Hin Hokw. iIntros "#Hinv #Hm #Hlb".
    rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| done ].
    rewrite /atrunc_of_permit. iIntros (i) "Hperm".
    rewrite /trunc_permit_of.
    iDestruct "Hperm" as (d nm) "[Htie Hrest]".
    iEval (rewrite /trunc_tie_arg) in "Htie".
    iDestruct "Htie" as "[Hnm Hcur]".
    (* THE TIE, READ: the name is `f` and the parent is the root *)
    iDestruct ("Hnm" $! pl with "[%]") as "%Hl"; [ exact Hpath |].
    assert (Hnmf : nm = fname_f) by (rewrite Hlast in Hl; by injection Hl).
    subst nm.
    iDestruct (npar_cur_elim M pv pl
                 (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I) d Hpath
                 with "Hcur") as "%Hd". subst d.
    iDestruct "Hrest" as "[Hfresh | [Hex Harm]]".
    - (* THE FRESH RUN: create's own receipt, as lane F-OPEN-2 landed it *)
      iApply (file_trunc_of_cre γfs c r jc s i Heq with "Hinv Hm [Hfresh]").
      rewrite /trunc_permit_cre. iExists ROOTINO, fname_f. iExact "Hfresh".
    - (* THE EXISTS RUN: the observation's pure reading beside the arm
         piece's refund, which is the deed's whole half *)
      rewrite /cre_ex_fired. iDestruct "Hex" as (avx entsx nlx) "(%Hrx & %Hex & Hrec)".
      rewrite /file_dlk_fam. cbn [pf_recv].
      rewrite /pf_at. iDestruct "Harm" as "[_ Harm]".
      rewrite /file_arm_fam. cbn [pf_refund].
      iApply (file_trunc_of_exists γfs c r jc s ls ws i avx entsx nlx
                Heq Hrx Hex Hin Hokw with "Hinv Hm Hlb Hrec Harm").
  Qed.

  (* ---- 3e.  ...AND THE WHOLE BUNDLE, FROM ONE DEED ---- *)

  (* [SysOpenDefs.open_au_create_at] at the path `f`, whose parent prefix
     is EMPTY: the walk is the start cursor alone ([ep_hops_done] over the
     empty list) and the cursor is the pure [⌜d = ROOTINO⌝], which is
     duplicable and returns itself in phase 1 -- [TreeMove.tree_mknod_au]'s
     reason, at this path.

     THE TRUNCATION PIECE IS THE CLAIM'S OWN (lane F-OPEN-3), at ANY mode:
     the bundle carries it at the permit create pays, and section 3f''
     supplies it.  The path's LAST ELEMENT is a premise because the tie is
     what identifies the truncated row -- the redirect child opens `f`, and
     that is the sentence saying so. *)
  Lemma file_open_create_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (ls : list wordline) (ws : wordline)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    fown r s -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jc s) (file_unarm_fam c r s)
      (file_cre_fam c r jc s)
      (file_dlk_fam c)
      (pfam_triv (fun _ _ _ => True%I))
      (file_trunc_fam c r s).
  Proof using .
    intros Heq Hpath Hnp Hstart Hlast Hin Hok.
    iIntros "#Hinv #Hm #Hlb Hown".
    rewrite /open_au_create_at. iSplitR.
    { (* THE WALK: no hops at all, and the start cursor is pure *)
      iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      rewrite /ep_start. iIntros (r0) "%Hr0". iModIntro. iSplitR.
      - iPureIntro. rewrite Hr0 Hstart //.
      - iApply (ep_hops_done γfs _ _ pl 0%nat). rewrite Hnp /=. lia. }
    iSplitR "Hown"; last first.
    { iSplitR.
      { iApply (file_dlk_piece γfs c r Heq with "Hinv"). }
      iSplitR.
      { (* the open observation is READ-ONLY and the file claim asks
           nothing of it: the deed is spent in the create's own legs *)
        iApply pf_at_triv. rewrite /aopen_commit_at.
        iIntros (I i a) "%Hrow Hka". iModIntro. by iFrame "Hka". }
      iSplitR.
      { (* THE TRUNCATE, at the permit create pays (section 3f'') *)
        rewrite /open_trunc_piece. destruct (om_trunc vom); [| done].
        iApply (file_trunc_piece γfs c r jc s ls ws M pv pl
                  Heq Hpath Hlast Hin Hok with "Hinv Hm Hlb"). }
      (* THE CHILD'S TWO LEGS: the deed goes in HERE and comes back out
         through whichever of the parent leg and the unarm fired *)
      rewrite /cre_child_unfired. iSplitL "Hown".
      - rewrite /pf_at /file_arm_fam /=. iSplit; [| iExact "Hown"].
        iApply (file_arm_commit γfs c r jc s [] Heq with "Hinv Hm Hown").
      - rewrite /pf_at /file_unarm_fam /=. iSplit; [| done].
        iApply (file_unarm_commit γfs c r jc s Heq with "Hinv Hm"). }
    (* THE PARENT LEG, at the guarded cursor: the move between the two
       readings is the ISO, and it costs nothing at this prefix *)
    rewrite /pf_at /file_cre_fam /=. iSplit; [| done].
    rewrite /acre_commit_at.
    iApply (acre_commit_at_gen_mono (fs_gamma_L γfs) appE
              (fun _ _ => AFile [])
              (fun d : Z => ⌜d = ROOTINO⌝%I)
              (npar_cur M pv (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I))
              (file_arm_fam c r jc s)
              (file_cre_fam c r jc s).(pf_recv)
              with "[] [] []").
    - iIntros "!>" (d) "H". rewrite /npar_cur.
      iApply ("H" $! pl). iPureIntro. exact Hpath.
    - iIntros "!>" (d) "%Hd". rewrite /npar_cur. iIntros (pl0) "_".
      by iPureIntro.
    - iApply (file_acre_commit γfs c r jc s ls ws Heq Hin Hok
                with "Hinv Hm Hlb").
  Qed.

  (* ...and at [om_trunc vom = false], where the truncate is never owed.
     SUBSUMED by the lemma above (lane F-OPEN-3): the bundle now supplies
     its own piece at every mode, so this is the same statement under one
     more premise, kept only so a caller at 0x201 need not read the
     guard. *)
  Lemma file_open_create_au_notrunc (γfs : fs_names) (c : file_fixed)
      (r : file_names) (jc : Z) (s : dst) (ls : list wordline) (ws : wordline)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    om_trunc vom = false ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    fown r s -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jc s) (file_unarm_fam c r s)
      (file_cre_fam c r jc s)
      (file_dlk_fam c)
      (pfam_triv (fun _ _ _ => True%I))
      (file_trunc_fam c r s).
  Proof using .
    intros Heq Hpath Hnp Hstart Hlast Htr Hin Hok.
    iIntros "#Hinv #Hm #Hlb Hown".
    iApply (file_open_create_au γfs c r jc s ls ws cw M pv vom pl
              Heq Hpath Hnp Hstart Hlast Hin Hok with "Hinv Hm Hlb Hown").
  Qed.

  (* ---- 3g.  THE RECEIPT, READ: WHAT THE REDIRECT CHILD GETS BACK ----

     [SpecSysOpen.open_receipt_create] at the families above, folded into
     the two payloads lane SH-ROUND instantiates
     [UkShRedirAns.ush_open_call2] with.  Every arm hands the deed back
     and the lemma says through WHICH: a fired truncate through its own
     receipt, a create that fired and then failed through the KEYED
     PIECE'S REFUND (the permit, [SysOpenDefs.cre_ft_kept] -- this is
     F-OPEN's "third arm"), and everything else through the arm piece's
     refund or the create leg's receipt.

     THREE OUTCOMES AND NOT TWO, and the third is the honest one: create's
     F-OK admits a found DEVICE, and this claim cannot refute it (the
     row's type is reported at the OPEN's observation instant and the tie
     is at the lookup's -- section 6's second hole).  A caller that wants
     "the descriptor is on `f`'s own inode" closes that first. *)

  (* what the deed is worth on an arm that did not settle at `f`: F-OPEN-2's
     [Kf], with the taint *)
  Definition file_open_pay (c : file_fixed) (r : file_names) (s : dst)
      : iProp Σ :=
    (fown r s ∨ (∃ i : Z, fown r (Some (i, []))) ∨ file_taint c)%I.

  (* the permit, read back off a piece that never fired.  THE TIE IS NOT
     READ here -- identifying the row is the truncate's business, and an
     unfired permit is worth only what was parked in it -- so the lemma is
     at any tie. *)
  Lemma file_permit_pay (c : file_fixed) (r : file_names) (jc : Z) (s : dst)
      (T : Z -> fname -> iProp Σ) (i : Z) (Γ : fs_view_names Σ) :
    trunc_permit_of Γ T
      (file_arm_fam c r jc s) (file_cre_fam c r jc s) (file_dlk_fam c) i -∗
    file_open_pay c r s.
  Proof using .
    iIntros "H". rewrite /trunc_permit_of.
    iDestruct "H" as (d nm) "[_ [Hfresh | [_ Harm]]]".
    - rewrite /cre_acre_fired.
      iDestruct "Hfresh" as (av ents nl) "[_ Hrec]".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iDestruct "Hrec" as "[[_ Hown] | [[_ Hown] | #HT]]".
      + rewrite /file_open_pay. by iLeft.
      + rewrite /file_open_pay. iRight. iLeft. iExists i. iExact "Hown".
      + rewrite /file_open_pay. iRight. iRight. iExact "HT".
    - rewrite /pf_at. iDestruct "Harm" as "[_ Hown]".
      rewrite /file_arm_fam. cbn [pf_refund].
      rewrite /file_open_pay. by iLeft.
  Qed.

  (* ...and off the keyed piece, whose refund carries it *)
  Lemma file_kept_pay (c : file_fixed) (r : file_names) (jc : Z) (s : dst)
      (γfs : fs_names) (vom : mword 64) (pl : list (bv 8)) (i : Z) :
    om_trunc vom = true ->
    cre_trunc_kept (fs_gamma_L γfs) vom pl
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (file_arm_fam c r jc s) (file_cre_fam c r jc s) (file_dlk_fam c)
      i (file_trunc_fam c r s) -∗
    file_open_pay c r s.
  Proof using .
    intros Htr. iIntros "H".
    rewrite /cre_trunc_kept /open_trunc_at Htr /pf_at /cre_ft_kept.
    cbn [pf_refund]. iDestruct "H" as "[_ [_ Hk]]".
    rewrite /cre_permit.
    iApply (file_permit_pay c r jc s _ i (fs_gamma_L γfs) with "Hk").
  Qed.

  (* the deed off create's own child legs, which every arm that fired
     nothing hands back *)
  Lemma file_legs_pay (c : file_fixed) (r : file_names) (jc : Z) (s : dst)
      (Γ : fs_view_names Σ) :
    (cre_child_unfired Γ (AFile []) (file_arm_fam c r jc s)
       (file_unarm_fam c r s)
     ∨ ∃ ic : Z, cre_child_pair (file_arm_fam c r jc s)
                   (file_unarm_fam c r s) ic) -∗
    file_open_pay c r s.
  Proof using .
    iIntros "[Hch | Hp]".
    - rewrite /cre_child_unfired. iDestruct "Hch" as "[Harm _]".
      iDestruct (pf_at_refund with "Harm") as "Hown".
      rewrite /file_arm_fam. cbn [pf_refund]. rewrite /file_open_pay.
      by iLeft.
    - iDestruct "Hp" as (ic) "Hp". rewrite /cre_child_pair /cre_unarm_fired.
      iDestruct "Hp" as (av0 c0) "[_ Hrec]".
      rewrite /file_unarm_fam. cbn [pf_recv].
      iDestruct "Hrec" as "[Hown | #HT]"; rewrite /file_open_pay.
      + by iLeft.
      + iRight. iRight. iExact "HT".
  Qed.

  (* ---- THE FAILURE FOLD, PAID.  Five shapes and every one of them hands
     the deed back: through the arm piece's refund where nothing fired,
     and through the KEYED PIECE'S REFUND -- the permit -- where the
     create fired and the call failed past it. *)
  Lemma file_open_create_fail_pay (γfs : fs_names) (c : file_fixed)
      (r : file_names) (jc : Z) (s : dst) (cw : Z) (M : gmap Z (bv 8))
      (pv vom : mword 64) :
    om_trunc vom = true ->
    open_post_fail_create (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jc s) (file_unarm_fam c r s)
      (file_cre_fam c r jc s) (file_dlk_fam c)
      (pfam_triv (fun _ _ _ => True%I))
      (file_trunc_fam c r s) -∗
    file_open_pay c r s.
  Proof using .
    intros Htr. rewrite /open_post_fail_create /open_au_create_at.
    iIntros "[Hau | H]".
    - iDestruct "Hau" as "(_ & _ & _ & _ & _ & Hch)".
      iApply (file_legs_pay c r jc s _ with "[Hch]"). by iLeft.
    - iDestruct "H" as (pl0) "[_ [Hd | Hc]]".
      + iDestruct "Hd" as "(_ & _ & _ & _ & _ & Hch)".
        iApply (file_legs_pay c r jc s _ with "[Hch]"). by iLeft.
      + iDestruct "Hc" as (d) "[_ [Ha | [Hb | Hc]]]".
        * (* (a) the create FIRED and the open failed past it: the deed is
               in the permit, which the keyed piece's refund carries *)
          iDestruct "Ha" as (av i nm ents nl)
            "(_ & _ & _ & _ & _ & _ & Hkept & _)".
          iApply (file_kept_pay c r jc s γfs vom pl0 i Htr with "Hkept").
        * (* (b) the name existed *)
          iDestruct "Hb" as (av i nm ents nl) "(_ & _ & _ & _ & _ & Hfk & _)".
          rewrite /cre_fail_kept Htr.
          iDestruct "Hfk" as "[[Hkept _] | [_ Hlegs]]".
          { iApply (file_kept_pay c r jc s γfs vom pl0 i Htr with "Hkept"). }
          iApply (file_legs_pay c r jc s _ with "Hlegs").
        * (* (c) nothing was observed at all *)
          iDestruct "Hc" as "(_ & _ & _ & _ & Hlegs)".
          iApply (file_legs_pay c r jc s _ with "Hlegs").
  Qed.

  (* ---- THE WHOLE RECEIPT, at the redirect child's own mode.  Three
     outcomes, and the second is the one the round runs on: a descriptor on
     an INODE, with `f` present and EMPTY at that inode -- or, on the run
     an absent deed makes unreachable and the statement cannot refute, the
     deed unmoved (section 6's first hole).  The third is the found DEVICE
     create's F-OK admits (section 6's second). *)
  Lemma file_open_create_recv (γfs : fs_names) (c : file_fixed)
      (r : file_names) (jc : Z) (s : dst) (cw : Z) (M : gmap Z (bv 8))
      (pv vom : mword 64) (sts : list fdstate) (rv : mword 64)
      (fdv' : list fdstate) :
    om_trunc vom = true ->
    open_receipt_create (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jc s) (file_unarm_fam c r s)
      (file_cre_fam c r jc s) (file_dlk_fam c)
      (pfam_triv (fun _ _ _ => True%I))
      (file_trunc_fam c r s) sts rv fdv' -∗
      ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝
        ∗ file_open_pay c r s)
       ∨ (∃ (i : Z) (γo : gname),
            ⌜open_fd_rcpt (om_readable vom) (om_writable vom)
               (FdInode i γo OffParked) sts rv fdv'⌝
            ∗ (fown r (Some (i, [])) ∨ fown r s ∨ file_taint c))
       ∨ (∃ ma : Z,
            ⌜open_fd_rcpt (om_readable vom) (om_writable vom)
               (FdDevice ma) sts rv fdv'⌝
            ∗ file_open_pay c r s)).
  Proof using .
    intros Htr. rewrite /open_receipt_create.
    iIntros "[(%Hr & %Hfdv & Hf) | Hok]".
    { iLeft. iSplitR; [ by iPureIntro |]. iSplitR; [ by iPureIntro |].
      iApply (file_open_create_fail_pay γfs c r jc s cw M pv vom Htr
                with "Hf"). }
    iDestruct "Hok" as (pl0 d i nm) "(_ & _ & _ & [Hfresh | Hex])".
    - (* FRESH: create made `f` and the truncate fired at the empty child *)
      iDestruct "Hfresh" as (av ents nl)
        "(_ & _ & _ & _ & _ & Htrc & _ & Hfd)".
      iEval (rewrite Htr) in "Htrc".
      iDestruct "Htrc" as (av' nl') "[_ Hrec]".
      rewrite /file_trunc_fam /file_trunc_recv. cbn [pf_recv].
      iDestruct "Hfd" as (γo) "%Hrcpt".
      iRight. iLeft. iExists i, γo. iSplitR; [ by iPureIntro |].
      iDestruct "Hrec" as "[Hown | [Hown | #HT]]".
      + iRight. iLeft. iExact "Hown".
      + iLeft. iExact "Hown".
      + iRight. iRight. iExact "HT".
    - (* THE NAME WAS THERE *)
      iDestruct "Hex" as (avx entsx nlx) "(_ & _ & _ & _ & _ & Hrest)".
      iDestruct "Hrest" as (av nl) "[Hfile | Hdev]".
      + (* ...on a FILE: the truncate fired there *)
        iDestruct "Hfile" as (bs0) "(_ & _ & Htrc & Hfd)".
        iEval (rewrite Htr) in "Htrc".
        iDestruct "Htrc" as (av') "[_ Hrec]".
        rewrite /file_trunc_fam /file_trunc_recv. cbn [pf_recv].
        iDestruct "Hfd" as (γo) "%Hrcpt".
        iRight. iLeft. iExists i, γo. iSplitR; [ by iPureIntro |].
        iDestruct "Hrec" as "[Hown | [Hown | #HT]]".
        * iRight. iLeft. iExact "Hown".
        * iLeft. iExact "Hown".
        * iRight. iRight. iExact "HT".
      + (* ...or on a DEVICE: nothing fired, and the deed comes home out
             of the permit the keyed piece kept *)
        iDestruct "Hdev" as (ma mi) "(_ & _ & _ & Hkept & %Hrcpt)".
        iRight. iRight. iExists ma. iSplitR; [ by iPureIntro |].
        iApply (file_kept_pay c r jc s γfs vom pl0 i Htr with "Hkept").
  Qed.

  (* =================================================================== *)
  (*  4.  THE READ AT `f`'s INUM                                          *)
  (*                                                                      *)
  (*  [UkTreeRead.tree_read_piece] at the FILE deed, and its arms.  The    *)
  (*  tree's supplier runs on a [□] claim law (a FROZEN deed); this one    *)
  (*  runs on a FRACTION of the live deed, which is all a READ needs --    *)
  (*  the fraction goes into the commit's fupd and comes back out through  *)
  (*  the receipt, and through the piece's own refund if the read never    *)
  (*  fires.                                                              *)
  (* =================================================================== *)

  Definition file_read_recv (c : file_fixed) (r : file_names) (q : Qp)
      (jc : Z) (s : dst) : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : nat) (_ : anode) (_ : nat) =>
              ((⌜fclaim_facts jc s av⌝ ∗ fdq r q s)
               ∨ (fdq r q s ∗ file_taint c))%I)
           (fdq r q s).

  Lemma file_read_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (jc : Z) (s : dst) (i : Z) (γo : gname) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fdq r q s -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo)
      (file_read_recv c r q jc s).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm Hd". rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| iExact "Hd" ].
    rewrite /aread_commit_at. iIntros (I off a d) "%Hpre Hka Hoff".
    iMod (file_claim_read γfs c r jc s q I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & Hc)".
    iModIntro. iFrame "Hka Hoff".
    iDestruct "Hc" as "[%Hf | #HT]".
    - iLeft. iFrame "Hd". by iPureIntro.
    - iRight. iFrame "Hd". iExact "HT".
  Qed.

  (* ...AND THE ARMS, READ: [UkTreeRead.read_arms_tree_learn] with the
     frozen pin replaced by the deed's own reading -- the observed row is
     `f`'s because the CLAIM says so at the very view the kernel read it
     in, and the deed's state names both the inum and the bytes. *)
  (* THE OK ARM ON ITS OWN, so the mapped corollary below -- which REFUTES
     the other one -- does not have to re-prove it. *)
  Lemma file_read_post_ok_learn (c : file_fixed) (r : file_names) (q : Qp)
      (jc : Z) (i : Z) (bs : list (bv 8)) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_post_ok (fs_gamma_L fsc_fs) i n
      (file_read_recv c r q jc (Some (i, bs))) rv M' addr -∗
    (((∃ off : nat,
            ⌜Z.to_nat (bv_unsigned rv)
             = ard_count (Z.to_nat n) off (length bs)⌝ ∗
            ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
               g j = bs !!! (off + j)%nat⌝)
      ∗ fdq r q (Some (i, bs)))
     ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)).
  Proof using .
    intros Hlin Himg Hnk.
    rewrite /read_post_ok.
    iIntros "Hok".
    iDestruct "Hok" as (av off a d) "(%Hpre & %Hn & %Htie & %Hdr & %Hbytes & Hc)".
    rewrite /file_read_recv. cbn [pf_recv].
    iDestruct "Hc" as "[[%Hf Hd] | [Hd #HT]]"; last first.
    { iRight. iFrame "Hd". iExact "HT". }
    destruct Hf as (Hok & _ & _). destruct Hok as (_ & Hav).
    destruct Hpre as (Hrow & _ & Hsz).
    assert (Hab : a = MkAnode (AFile bs) 1%nat)
      by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    subst a. cbn [an_node] in Htie, Hbytes.
    cbn [anode_size_ok an_node] in Hsz.
    apply Nat2Z.inj_le in Hsz. rewrite Nat2Z.inj_mul in Hsz.
    change (Z.of_nat InodeInv.MAXFILE) with 268 in Hsz.
    change (Z.of_nat BioDefs.BSIZE) with 1024 in Hsz.
    iLeft. iFrame "Hd". iExists off.
    assert (Hdc : d = ard_count (Z.to_nat n) off (length bs)).
    { assert (Hbu : bv_unsigned rv
                    = Z.of_nat (ard_count (Z.to_nat n) off (length bs))).
      { rewrite Htie. apply moi_small.
        pose proof (ard_count_sub (Z.to_nat n) off (length bs)) as Hle.
        unfold Z64. lia. }
      lia. }
    iPureIntro. split.
    { rewrite -Hdr Nat2Z.id. exact Hdc. }
    intros j Hj.
    assert (Hjd : (j < d)%nat) by (rewrite -Hdr Nat2Z.id in Hj; lia).
    assert (Hdk : (d <= k)%nat).
    { pose proof (ard_count_le (Z.to_nat n) off (length bs)) as Hle. lia. }
    pose proof (Hbytes ltac:(intros i0 Hi0; apply Hlin; lia) j Hjd) as HM.
    pose proof (Himg j ltac:(lia)) as HG.
    rewrite HM in HG. by injection HG.
  Qed.

  Lemma file_read_arms_learn (c : file_fixed) (r : file_names) (q : Qp)
      (jc : Z) (i : Z) (bs : list (bv 8)) (γo : gname) (P : uptd) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_arms (fs_gamma_L fsc_fs) i γo P n
      (file_read_recv c r q jc (Some (i, bs))) rv M' addr -∗
    (((⌜rv = (mword_of_int (-1) : mword 64)⌝
       ∨ (∃ off : nat,
            ⌜Z.to_nat (bv_unsigned rv)
             = ard_count (Z.to_nat n) off (length bs)⌝ ∗
            ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
               g j = bs !!! (off + j)%nat⌝))
      ∗ fdq r q (Some (i, bs)))
     ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)).
  Proof using .
    intros Hlin Himg Hnk.
    rewrite /read_arms /read_post_fail.
    iIntros "[Hok | [%Hm1 Hf]]"; last first.
    { (* the sign guard hands the piece back whole; the copyout-fault arm
         hands the FIRED receipt.  Either way the fraction comes home. *)
      iDestruct "Hf" as "[[_ Hpf] | [_ [_ Hfired]]]".
      - iDestruct (pf_at_refund with "Hpf") as "Hd".
        rewrite /file_read_recv. cbn [pf_refund].
        iLeft. iFrame "Hd". iLeft. by iPureIntro.
      - iDestruct "Hfired" as (av off a) "(_ & Hc)".
        rewrite /file_read_recv. cbn [pf_recv].
        iDestruct "Hc" as "[[_ Hd] | [Hd #HT]]".
        + iLeft. iFrame "Hd". iLeft. by iPureIntro.
        + iRight. iFrame "Hd". iExact "HT". }
    iDestruct (file_read_post_ok_learn c r q jc i bs n rv M' addr k g
                 Hlin Himg Hnk with "Hok") as "[[H Hd] | [Hd HT]]".
    - iLeft. iFrame "Hd". iRight. iExact "H".
    - iRight. iFrame "Hd". iExact "HT".
  Qed.

  (* ...AND AT A MAPPED DESTINATION BUFFER THE -1 ARM IS GONE (lane
     READ-RELAY, deliverable 2).  One line: the relay carried the copyout's
     reason from [SpecCopyout] to [FsAbsReadFire.read_post_fail], and a
     program that owns its destination run refutes it there. *)
  Lemma file_read_arms_learn_mapped (c : file_fixed) (r : file_names) (q : Qp)
      (jc : Z) (i : Z) (bs : list (bv 8)) (γo : gname) (P : uptd) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (0 <= n)%Z ->
    (Z.to_nat n <= k)%nat ->
    (forall j : nat, (j < k)%nat ->
       uva_wmapped P (uint (add_vec_int addr (Z.of_nat j)))) ->
    read_arms (fs_gamma_L fsc_fs) i γo P n
      (file_read_recv c r q jc (Some (i, bs))) rv M' addr -∗
    (((∃ off : nat,
         ⌜Z.to_nat (bv_unsigned rv)
          = ard_count (Z.to_nat n) off (length bs)⌝ ∗
         ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
            g j = bs !!! (off + j)%nat⌝)
      ∗ fdq r q (Some (i, bs)))
     ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)).
  Proof using .
    intros Hlin Himg Hn Hnk Hmap. iIntros "H".
    iApply (file_read_post_ok_learn c r q jc i bs n rv M' addr k g
              Hlin Himg Hnk).
    iApply (read_arms_mapped (fs_gamma_L fsc_fs) i γo P n
              (file_read_recv c r q jc (Some (i, bs))) rv M' addr k
              Hn Hnk Hmap with "H").
  Qed.

  (* =================================================================== *)
  (*  5.  THE O_RDONLY OPEN AT `f` (cat's)                                *)
  (*                                                                      *)
  (*  [PinnedObs.v] section 12 records the wall a LIVE claim meets here:   *)
  (*  a read-only open owes TWO independent pieces that must each read the *)
  (*  claim -- the walk's hops and the terminal observation -- and a       *)
  (*  linear deed sits in only one.  THE FILE DEED WALKS ROUND IT: a READ  *)
  (*  needs no move, so the holder SPLITS its half in two and pays each    *)
  (*  piece with a fraction (section 1).  Both come home -- the walk's     *)
  (*  through the terminal cursor, the observation's through its own       *)
  (*  receipt -- and [fdq_join] puts them back together.                   *)
  (* =================================================================== *)

  (* ---- 5a.  THE PIN, AT THE DEED'S OWN INUM ---- *)

  Lemma f_pin_walks (i : Z) (bs : list (bv 8)) (cw : Z) (pl : list (bv 8)) :
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    pin_walks_at (fun v : aview => f_ok v (Some (i, bs))) cw pl
      [ROOTINO; i] i.
  Proof using .
    intros Hel Hst. rewrite /pin_walks_at Hel. cbn [length].
    split_and!; [ exact Hst | reflexivity |].
    intros v (Hstep & _). cbn [list_lookup_total].
    eapply ARun_cons; [ exact Hstep | apply ARun_nil ].
  Qed.

  Lemma f_pin_resolves (i : Z) (bs : list (bv 8)) (cw : Z) (pl : list (bv 8)) :
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    pin_resolves_abs (fun v : aview => f_ok v (Some (i, bs))) cw pl
      [ROOTINO; i] i (AFile bs).
  Proof using .
    intros Hel Hst. split; [ exact (f_pin_walks i bs cw pl Hel Hst) |].
    intros v (_ & Hrow). by exists 1%nat.
  Qed.

  (* ---- 5b.  THE CLAIM LAW AT THE ERA'S RECORD, LINEAR IN A FRACTION -- *)

  Lemma file_pin_law_q (c : file_fixed) (r : file_names) (q : Qp) (s : dst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    ⊢ □ (∀ v : aview, fdq r q s -∗ app_pred app_run v -∗
           app_pred app_run v ∗ fdq r q s ∗ (⌜f_ok v s⌝ ∨ file_taint c)).
  Proof using .
    intros Heq. iDestruct (file_deed_law_q c r q) as "#Hlaw".
    iIntros "!>" (v) "Hd Hp".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct ("Hlaw" $! v s with "Hd Hp") as "(Hp & Hd & Hc)".
    iSplitL "Hp".
    { rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iFrame "Hd". iDestruct "Hc" as "[%Hf | #HT]";
      [ iLeft; iPureIntro; exact (proj1 Hf) | by iRight ].
  Qed.

  (* ---- 5c.  THE OBSERVATION, WITH THE FRACTION IN THE RECEIPT -------- *)

  (* [PinnedObs.pobs_aopen_lin]'s three lines, with [K] put in the RECEIPT
     as well as in the refund: the caller must have its fraction back on
     BOTH paths, and a fired observation returns it only through [Φ]. *)
  Definition file_open_recv (c : file_fixed) (r : file_names) (q : Qp)
      (s : dst) : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    MkPfam (fun (av : aview) (i : Z) (a : anode) =>
              (⌜arow_at av i a⌝ ∗ fdq r q s
               ∗ (⌜f_ok av s⌝ ∨ file_taint c))%I)
           (fdq r q s).

  Lemma file_aopen_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (s : dst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ fdq r q s -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (file_open_recv c r q s).
  Proof using .
    intros Heq. iIntros "#Hinv Hd".
    iDestruct (file_deed_law_q c r q) as "#Hlaw".
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [| iExact "Hd" ].
    rewrite /aopen_commit_at. iIntros (I i a) "%Hrow Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iAssert (▷ (file_pred c r (abs_view I) ∗ fdq r q s
                ∗ (⌜f_ok (abs_view I) s /\ file_fs_pure (abs_view I)⌝
                   ∨ file_taint c)))%I with "[Hp Hd]" as "Hpc".
    { iNext. iApply ("Hlaw" with "Hd Hp"). }
    iDestruct "Hpc" as "[Hp [Hd Hc]]". iMod "Hc". iMod "Hd".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hd". iSplitR; [ by iPureIntro |].
    iDestruct "Hc" as "[%Hf | #HT]";
      [ iLeft; iPureIntro; exact (proj1 Hf) | by iRight ].
  Qed.

  (* ---- 5d.  THE BUNDLE ---- *)

  Lemma file_open_plain_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    om_trunc vom = false ->
    app_inv γfs -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    open_au_plain_at (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_lin (file_taint c) [ROOTINO; i] (fdq r q1 (Some (i, bs))))
      (pobs_Pmiss (file_taint c))
      (file_open_recv c r q2 (Some (i, bs))) Ft.
  Proof using .
    intros Heq Hpath Hel Hst Htr. iIntros "#Hinv Hd1 Hd2".
    iDestruct (file_pin_law_q c r q1 (Some (i, bs)) Heq) as "#Hcl1".
    rewrite /open_au_plain_at. iSplitL "Hd1".
    { iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      iApply (pobs_walk_w_lin γfs (fun v : aview => f_ok v (Some (i, bs)))
                (file_taint c) (fdq r q1 (Some (i, bs)))
                (pobs_Pmiss (file_taint c)) cw pl [ROOTINO; i] i
                (f_pin_walks i bs cw pl Hel Hst)
                with "[] Hcl1 Hinv Hd1").
      iApply pobs_miss_taint_Pmiss. }
    iSplitL "Hd2".
    { iApply (file_aopen_piece γfs c r q2 (Some (i, bs)) Heq with "Hinv Hd2"). }
    iApply (open_trunc_piece_none _ vom _ Ft Htr).
  Qed.

  (* ---- 5e.  THE RECEIPT, READ AT THE DEED ----

     [UkTreeRead.tree_open_recv_file]'s three-way collapse at the file
     claim: the device and directory arms are refuted by the terminal
     identification, and the file arm's descriptor is on THE DEED'S OWN
     INUM.  BOTH fractions come home. *)
  Lemma file_open_recv_file (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (rv : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv pl ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    open_receipt_plain (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_lin (file_taint c) [ROOTINO; i] (fdq r q1 (Some (i, bs))))
      (pobs_Pmiss (file_taint c))
      (file_open_recv c r q2 (Some (i, bs))) Ft sts rv fdv' -∗
      ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝)
       ∨ (∃ γo : gname,
            ⌜open_fd_rcpt (om_readable vom) (om_writable vom)
               (FdInode i γo OffParked) sts rv fdv'⌝
            ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
       ∨ file_taint c).
  Proof using .
    intros Hpath Hel Hst. iIntros "Hrc".
    pose proof (f_pin_resolves i bs cw pl Hel Hst) as Hres.
    pose proof Hres as [(_ & Hfin & _) Hpinr].
    rewrite /open_receipt_plain.
    iDestruct "Hrc" as "[(%Hr & %Hfd & _) | Hok]".
    { iLeft. iPureIntro. exact (conj Hr Hfd). }
    iDestruct "Hok" as (pl' av j) "(%Hpath' & HP & Harm)".
    rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
    (* the terminal cursor names the deed's inum and hands the walk's
       fraction back *)
    rewrite /pobs_P_lin Hel. cbn [length].
    iDestruct "HP" as "[[%Hj Hd1] | #HT]"; last first.
    { iRight. iRight. iExact "HT". }
    cbn [list_lookup_total] in Hj. subst j.
    iDestruct "Harm" as "[Hdev | [Hfile | Hdir]]".
    - (* DEVICE: refuted -- the deed says the row is a FILE *)
      iDestruct "Hdev" as (ma mi nl) "(%Hrow & _ & Hrecv & _ & _)".
      rewrite /file_open_recv. cbn [pf_recv].
      iDestruct "Hrecv" as "(%Hra & Hd2 & [%Hf | #HT])"; last first.
      { iRight. iRight. iExact "HT". }
      exfalso. destruct Hf as (_ & Hav).
      pose proof (arow_at_pinned _ _ _ _ Hra Hav) as Hab. discriminate Hab.
    - (* FILE: the descriptor is on the deed's own inum *)
      iDestruct "Hfile" as (bs0 nl) "(%Hrow & Hrecv & _ & %Hfdr)".
      rewrite /file_open_recv. cbn [pf_recv].
      iDestruct "Hrecv" as "(%Hra & Hd2 & [%Hf | #HT])"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hfdr as (γo & Hfdr).
      iRight. iLeft. iExists γo. iFrame "Hd1 Hd2". by iPureIntro.
    - (* DIRECTORY: refuted the same way *)
      iDestruct "Hdir" as (ents nl) "(%Hrow & _ & Hrecv & _ & _)".
      rewrite /file_open_recv. cbn [pf_recv].
      iDestruct "Hrecv" as "(%Hra & Hd2 & [%Hf | #HT])"; last first.
      { iRight. iRight. iExact "HT". }
      exfalso. destruct Hf as (_ & Hav).
      pose proof (arow_at_pinned _ _ _ _ Hra Hav) as Hab. discriminate Hab.
  Qed.

End FileOpen.

(* ===================================================================== *)
(*  6.  WHAT IS *NOT* HERE, AND EXACTLY WHY (the lane's STOP rule)        *)
(*                                                                       *)
(*  (a) THE O_TRUNC LEG OF THE CREATE BUNDLE -- CLOSED (lane F-OPEN-3),   *)
(*      WITH ONE HOLE NAMED AT THE END.                                   *)
(*                                                                       *)
(*      WHAT LANDED.  [SysOpenDefs.open_trunc_piece] now carries the      *)
(*      permit [SysOpenDefs.trunc_permit_of]: the WALK'S TIE (the arg     *)
(*      path's last element is [nm], and the walk's terminal directory is *)
(*      [d] -- the two facts [SysMknodDefs.npar_cur] carries, guarded the *)
(*      same way) beside the DISJUNCTION the kernel pays from whichever   *)
(*      of create's arms ran: the create leg's fired receipt on the FRESH *)
(*      run, the exists observation's receipt BESIDE THE UNFIRED ARM      *)
(*      PIECE on the EXISTS one.  [file_trunc_piece] supplies it at both  *)
(*      ([file_trunc_of_cre] and [file_trunc_of_exists]), and             *)
(*      [file_open_create_au] no longer takes the truncate as a premise   *)
(*      at any mode -- the 0x601 bundle is one deed.                      *)
(*                                                                       *)
(*      THE RULING SAID THE EXISTS DISJUNCT NEEDS A DEED FRACTION INSIDE  *)
(*      [Fex]'s RECEIPT (lane F-OPEN-2's finding 2) AND IT DOES NOT.      *)
(*      What the disjunct must establish at the truncate is that the row  *)
(*      the call reached is not one of the four era-0 binaries, and the   *)
(*      claim says that at the LOOKUP's view with NOTHING LINEAR: its     *)
(*      non-taint arm carries [⌜file_fs_pure av⌝], and both arms of       *)
(*      [AppFile.f_state] carry the TYPED witness of whatever state the   *)
(*      claim is at, whose pure part bounds the content by               *)
(*      [EchoDisc.line_max].  That is [fclaim_free] and                   *)
(*      [file_claim_read_free], and it is why [file_dlk_fam]'s receipt    *)
(*      holds no fraction at all -- which is what makes the whole half    *)
(*      available in the ARM piece, where the create leg needs it.        *)
(*      Lane F-OPEN-2's finding 3 (the split is impossible at             *)
(*      [s = None]) was therefore never on the critical path, and no      *)
(*      third kernel seam was needed.                                     *)
(*                                                                       *)
(*      WHAT IS STILL OPEN, and it is the ONE thing a redirect round      *)
(*      needs next: THE EXISTS DISJUNCT AT [s = None] IS DISCHARGED AND   *)
(*      NOT REFUTED.  At an absent deed a run in which create's           *)
(*      [dirlookup] FINDS `f` is unreachable, but the SUPPLY must still   *)
(*      cover it; [file_trunc_of_exists] covers it by stepping FREELY     *)
(*      (the row is not pinned, [f_ok av None] is preserved) and handing  *)
(*      the deed back UNMOVED, so [file_trunc_recv]'s first arm           *)
(*      ([fown r s]) is reachable in the statement though not on any run. *)
(*      REFUTING it needs the claim read AT THE LOOKUP'S VIEW -- the      *)
(*      entry fact [ents !! f = Some i] is at [avx], and between [avx]    *)
(*      and the [itrunc] the parent is unlocked, so no later view carries *)
(*      it -- and reading the claim's OWN VALUE there (rather than the    *)
(*      determined one) needs a positive deed fraction inside the [Fex]   *)
(*      piece, which at [s = None] the create's parent leg has already    *)
(*      claimed in full ([AppFile.file_step_park] at `f` wants            *)
(*      [fdeed_whole], and the bundle's pieces are [∗]-separated).  So    *)
(*      the choice is exactly two: (i) lane F-OPEN-2's restatement 3 --   *)
(*      [FsAbsCreateFire.acre_commit_at_gen] takes the UNFIRED [Fex]      *)
(*      piece beside the arm's receipt, making the two exclusive in the   *)
(*      logic and letting the parent leg reassemble [q1 + q2]; or (ii) an *)
(*      APPLICATION-SIDE ESCROW -- the deed's half in an invariant of the *)
(*      claim's own, with the arm's piece holding the one-shot that says  *)
(*      it has not fired, so [Fex] may read it and the arm may take it.   *)
(*      (ii) costs no kernel restatement and is this file's business; it  *)
(*      is what lane SH-ROUND needs if its round is to read the redirect  *)
(*      child's fd arm as [fown r (Some (i, []))] ALONE.                  *)
(*                                                                       *)
(*      THE SAME SHAPE ONCE MORE, SMALLER: create's F-OK admits a found   *)
(*      DEVICE, and this claim cannot refute that either -- the row's     *)
(*      type is reported at the OPEN's observation instant and the tie is *)
(*      at the lookup's.  [file_open_create_recv] therefore has THREE     *)
(*      outcomes and not two; closing (i) or (ii) closes this one too,    *)
(*      since both give the lookup's view a readable claim.               *)
(*                                                                       *)
(*  (b) THE O_RDONLY OPEN AT AN ABSENT `f` -- CLOSED (lane F-OPEN-2,      *)
(*      seam 2).  [file_open_miss_au] / [file_open_miss_recv] below are    *)
(*      the bundle and its receipt at [f_pin_misses], and the fraction     *)
(*      comes home.  What F-OPEN priced as two fixes turned out to be      *)
(*      one: put [K] ON THE CURSOR ([PinnedObs.pobs_P_dead_lin], section   *)
(*      11a's construction one list shorter) and BOTH arms of              *)
(*      [SysOpenDefs.namei_walk_dead_era] refund without that definition   *)
(*      moving -- the `hop never fired` arm hands back [P k d] and the     *)
(*      `fired and missed` arm hands back [Pmiss k d], and at              *)
(*      [pobs_Pmiss_ref] both carry [K].  The walk piece did NOT have to   *)
(*      become a [pf_at].                                                  *)
(* ===================================================================== *)

Section FileOpenMiss.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* the pin an ABSENT `f` gives the walk: the first hop misses *)
  Lemma f_pin_misses (cw : Z) (pl : list (bv 8)) :
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    pin_misses_at (fun v : aview => f_ok v None) cw pl ROOTINO.
  Proof using .
    intros Hel Hst. split; [ exact Hst |].
    intros v s Hp Hs. rewrite Hel in Hs. cbn in Hs.
    injection Hs as <-. exact Hp.
  Qed.
  (* ---- THE BUNDLE, AND IT REFUNDS THE FRACTION ----

     [PinnedOpen.pinned_open_bundle_dead_lin] at the ABSENT pin: the walk
     dies at its first hop, the success fold collapses to the taint, and
     the deed fraction the hop was paid with rides the CURSOR and comes
     home through whichever arm of the failure fold the receipt hands
     back ([PinnedObs] section 8a).  That is the whole of what lane
     F-OPEN's STOP item (b) was waiting on. *)
  Lemma file_open_miss_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64)
      (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    om_create vom = false ->
    om_trunc vom = false ->
    app_inv γfs -∗
    fdq r q None -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin (file_taint c) (fdq r q None) ROOTINO)
      (pobs_Pmiss_ref (file_taint c) (fdq r q None))
      Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof using .
    intros Heq Hpath Hel Hst Hcr Htr. iIntros "#Hinv Hd".
    iApply (pinned_open_bundle_dead_lin γfs
              (fun v : aview => f_ok v None) (file_taint c)
              (fdq r q None)
              (pobs_Pmiss_ref (file_taint c) (fdq r q None))
              cw pl ROOTINO M pv vom Ft Farm Fun Fok Fex
              Hcr Htr (f_pin_misses cw pl Hel Hst) Hpath
              with "[] [] [] Hinv Hd").
    - iApply (file_pin_law_q c r q None Heq).
    - iApply pobs_miss_taint_ref.
    - iApply pobs_miss_hold_ref.
  Qed.

  (* ...AND THE RECEIPT: the open failed and the table did not move AND
     THE FRACTION IS BACK, or the application is tainted.  There is no
     third arm -- cat's `cannot open` branch is a THEOREM at an absent
     deed, not an arm it has to carry. *)
  Lemma file_open_miss_recv (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64)
      (pl : list (bv 8))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (rv : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv pl ->
    path_elems pl = [fname_f] ->
    open_receipt_plain (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin (file_taint c) (fdq r q None) ROOTINO)
      (pobs_Pmiss_ref (file_taint c) (fdq r q None)) Fo Ft sts rv fdv'
    ={⊤}=∗ ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝
             ∗ fdq r q None)
            ∨ file_taint c).
  Proof using .
    intros Hpath Hel. iIntros "Hrc".
    iApply (pinned_open_dead_lin γfs (file_taint c) (fdq r q None)
              cw pl ROOTINO M pv vom Fo Ft sts rv fdv' Hpath
              ltac:(rewrite Hel; discriminate) with "Hrc").
  Qed.

End FileOpenMiss.
