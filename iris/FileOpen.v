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
  Definition file_cre_recv (c : file_fixed) (r : file_names) (s : dst)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (_ : aview) (d : Z) (nm : fname) (i : Z) =>
      ((⌜nm <> fname_f⌝ ∗ fown r s)
       ∨ (⌜s = None /\ d = ROOTINO /\ nm = fname_f⌝ ∗ fown r (Some (i, [])))
       ∨ file_taint c)%I.

  Definition file_cre_fam (c : file_fixed) (r : file_names) (s : dst)
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (file_cre_recv c r s) True%I.

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
      (file_arm_fam c r jc s) (file_cre_fam c r s).(pf_recv).
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
      iLeft. iFrame "Hd Ht". by iPureIntro.
  Qed.

  (* ---- 3e.  ...AND THE WHOLE BUNDLE, FROM ONE DEED ---- *)

  (* [SysOpenDefs.open_au_create_at] at the path `f`, whose parent prefix
     is EMPTY: the walk is the start cursor alone ([ep_hops_done] over the
     empty list) and the cursor is the pure [⌜d = ROOTINO⌝], which is
     duplicable and returns itself in phase 1 -- [TreeMove.tree_mknod_au]'s
     reason, at this path.

     THE TRUNCATION PIECE IS A PREMISE, and section 5 says why it cannot be
     anything else. *)
  Lemma file_open_create_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jc : Z) (s : dst) (ls : list wordline) (ws : wordline)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = ROOTINO ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    open_trunc_piece (fs_gamma_L γfs) vom Ft -∗
    fown r s -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jc s) (file_unarm_fam c r s)
      (file_cre_fam c r s)
      (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I))
      Ft.
  Proof using .
    intros Heq Hpath Hnp Hstart Hin Hok.
    iIntros "#Hinv #Hm #Hlb Htr Hown".
    rewrite /open_au_create_at. iSplitR.
    { (* THE WALK: no hops at all, and the start cursor is pure *)
      iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      rewrite /ep_start. iIntros (r0) "%Hr0". iModIntro. iSplitR.
      - iPureIntro. rewrite Hr0 Hstart //.
      - iApply (ep_hops_done γfs _ _ pl 0%nat). rewrite Hnp /=. lia. }
    iSplitR "Htr Hown"; last first.
    { iSplitR.
      { iApply pf_at_triv. iApply dlookup_commit_at_unit. }
      iSplitR.
      { (* the open observation is READ-ONLY and the file claim asks
           nothing of it: the deed is spent in the create's own legs *)
        iApply pf_at_triv. rewrite /aopen_commit_at.
        iIntros (I i a) "%Hrow Hka". iModIntro. by iFrame "Hka". }
      iSplitL "Htr"; [ iExact "Htr" |].
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
              (file_cre_fam c r s).(pf_recv)
              with "[] [] []").
    - iIntros "!>" (d) "H". rewrite /npar_cur.
      iApply ("H" $! pl). iPureIntro. exact Hpath.
    - iIntros "!>" (d) "%Hd". rewrite /npar_cur. iIntros (pl0) "_".
      by iPureIntro.
    - iApply (file_acre_commit γfs c r jc s ls ws Heq Hin Hok
                with "Hinv Hm Hlb").
  Qed.

  (* ...at [om_trunc vom = false], where nothing is owed for the truncate
     and the bundle costs exactly the deed. *)
  Lemma file_open_create_au_notrunc (γfs : fs_names) (c : file_fixed)
      (r : file_names) (jc : Z) (s : dst) (ls : list wordline) (ws : wordline)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = ROOTINO ->
    om_trunc vom = false ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ cons_made (fn_cons r) jc -∗ fl_lb c ls -∗
    fown r s -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jc s) (file_unarm_fam c r s)
      (file_cre_fam c r s)
      (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I))
      Ft.
  Proof using .
    intros Heq Hpath Hnp Hstart Htr Hin Hok.
    iIntros "#Hinv #Hm #Hlb Hown".
    iApply (file_open_create_au γfs c r jc s ls ws cw M pv vom pl Ft
              Heq Hpath Hnp Hstart Hin Hok with "Hinv Hm Hlb [] Hown").
    iApply (open_trunc_piece_none _ vom Ft Htr).
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
  Lemma file_read_arms_learn (c : file_fixed) (r : file_names) (q : Qp)
      (jc : Z) (i : Z) (bs : list (bv 8)) (γo : gname) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_arms (fs_gamma_L fsc_fs) i γo n
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
    rewrite /read_arms /read_post_ok /read_post_fail.
    iIntros "[Hok | [%Hm1 Hf]]"; last first.
    { (* the sign guard hands the piece back whole; the copyout-fault arm
         hands the FIRED receipt.  Either way the fraction comes home. *)
      iDestruct "Hf" as "[[_ Hpf] | [_ Hfired]]".
      - iDestruct (pf_at_refund with "Hpf") as "Hd".
        rewrite /file_read_recv. cbn [pf_refund].
        iLeft. iFrame "Hd". iLeft. by iPureIntro.
      - iDestruct "Hfired" as (av off a) "(_ & Hc)".
        rewrite /file_read_recv. cbn [pf_recv].
        iDestruct "Hc" as "[[_ Hd] | [Hd #HT]]".
        + iLeft. iFrame "Hd". iLeft. by iPureIntro.
        + iRight. iFrame "Hd". iExact "HT". }
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
    iLeft. iFrame "Hd". iRight. iExists off.
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
    iApply (open_trunc_piece_none _ vom Ft Htr).
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
(*  (a) THE O_TRUNC LEG OF THE CREATE BUNDLE.  [file_open_create_au]      *)
(*      takes [SysOpenDefs.open_trunc_piece] as a PREMISE and             *)
(*      [file_open_create_au_notrunc] discharges it at [om_trunc vom =    *)
(*      false].  At [om_trunc vom = true] -- sh's redirect mode 0x601 --   *)
(*      it cannot be supplied from this deed, and the obstruction is      *)
(*      STRUCTURAL rather than proof effort:                              *)
(*                                                                       *)
(*        [open_au_create_at] joins [open_trunc_piece Γ vom Ft] and       *)
(*        [cre_child_unfired Γ (AFile []) Farm Fun] under one [∗].  The   *)
(*        create's parent leg MOVES the claim ([file_step_park] in phase  *)
(*        1, [file_resync] in phase 2), and those take the deed's half    *)
(*        and the ticket's half ON THE NOSE -- the in-flight arm of       *)
(*        [AppFile.f_state] holds [fdeed_whole], so no proper fraction    *)
(*        parks.  The truncate piece then has NOTHING left to read the    *)
(*        claim with, and it must: [FsAbsReadFire]-style determinacy      *)
(*        settles every case but one, namely `[i] is the deed's own inum  *)
(*        and its content is non-empty`, which is exactly the case that    *)
(*        needs the MOVE.                                                 *)
(*                                                                       *)
(*        Splitting the deed does not help: a fraction READS              *)
(*        ([file_deed_law_q]) but does not PARK, and the create leg's     *)
(*        phase 2 cannot be deferred to the truncate either -- sys_open's *)
(*        [itrunc] runs AFTER [filealloc]/[fdalloc], so                    *)
(*        [SpecSysOpen.open_post_fail_create]'s arm (a) (create fired,     *)
(*        the descriptor table was full) hands the truncate piece back     *)
(*        UNFIRED, and a claim left in flight there can never be resynced  *)
(*        (a resync needs the map authority, i.e. a later fire).           *)
(*                                                                       *)
(*      THE FIX IS A KERNEL-TIER SEAM, and it is the one [PinnedObs.v]    *)
(*      section 12 already prices in another place: the truncate piece    *)
(*      must be KEYED, as the unarm is keyed to its arm                    *)
(*      ([FsAbsCreateFire.aunarm_of_arm]).  With                           *)
(*      [open_trunc_piece] handed in as [∀ i, <permit i> -∗                *)
(*      atrunc_commit_at Γ appE i Φ] at the create's own receipt, the      *)
(*      deed rides the create's [Fok] into the truncate and the whole      *)
(*      0x601 bundle is one more instance of section 3.                    *)
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
