(* ProofSysOpenCreArm.v -- the O_CREATE arm's ARM BUILDERS: the SHIM that
   lets the landed plain blocks (+0x4a downward: [ProofSysOpenJoin],
   [ProofSysOpenAlloc], [ProofSysOpenStores], [ProofSysOpenPub]) run
   UNDER the create arm, and the conversion of what they deliver into
   [SpecSysOpen.open_arms_create].

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover), create arm.  Nothing below it moves: not the four blocks below
   the join, not [ProofSysOpen]'s plain walk.

   ==== THE SHIM, AND WHY IT IS THE WHOLE DESIGN =======================

   The blocks from the join down are stated at [open_arms_plain] -- but
   they are PARAMETRIC in the four caller predicates [P], [Pmiss], [Phio],
   [Phit], and that is the seam.  The create arm runs them at SHIM
   predicates and converts the armed post afterwards:

     [socr_P R i0]   the create-side residue [R], carried inert through
                     the whole plain tail, TAGGED with the inum so the
                     post's existential [i] is pinned back to the created
                     (or found) node.  [socr_Pm R] is the same without the
                     tag, for the miss side no block below the join ever
                     touches.
     [socr_Phio_*]   the terminal observation, in the arm's two flavours.

   AND THE FLAVOUR IS DECIDED BY create's OWN [made] BIT, which is why the
   arm needs no lookahead:

     made = true (FRESH).  [SysOpenDefs]'s FRESH arms REFUND the terminal
       observation, so the real [Phio] is never fired: it rides inside [R]
       and the plain tail runs at the PURE [socr_Phio_pure] (a row
       equation, no resource).  The pure receipt is what refutes the tail's
       DEVICE and DIRECTORY arms -- create was called with T_FILE, so the
       row is an [AFile] -- and, since the create arm names the child's
       bytes as [[]], it is also what identifies the tail's [bs0] with the
       empty list.  THE TRUNC COMMIT IS THE CALLER'S OWN AND FIRES: the
       tail runs at [Phit] itself, and its receipt comes back at [[]]
       because itrunc's delta on an empty file is the identity.  It used to
       run at a throw-away [True] piece this file conjured, which was the
       last fire in the tree payable only out of the application's parked
       license.
     made = false (EXISTS-OPENS).  The spec's arms want the real [Phio]
       FIRED at the found node and the real trunc behaviour, which is
       exactly what the plain tail does.  So the tail runs at
       [socr_Phio_tag] -- the real [Phio] with the row equation stapled on
       -- and the staple is what refutes the DIRECTORY arm (ARM F-OK
       admits only [T_FILE] and [T_DEVICE]).

   THE ONE FUPD.  [open_post_fail_plain]'s first two disjuncts are
   unreachable below the join (every failure there is
   [ProofSysOpenShared.so_arm_fail]'s third), but the statement is a
   disjunction and all three have to be converted.  The first two return
   the residue inside the walk one-shot / the death receipt, so recovering
   it costs one [={T}=>] -- which the consumer pays under [fupd_wp].

   BINDERS: [ProofSysOpenShared]'s list verbatim. *)

From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
(* the payload's own vocabulary, IMPORTED BEFORE [FsBlocks] on purpose --
   durable-notes' rule ("the last import wins"). *)
Require Import LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecItrunc.
Require Import ConsoleInv.
Require Import ProofSysOpenShared.  (* [so_obs] *)
Require Import PathElems.
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SysMknodDefs.
Require Import ArgPath.         (* [arg_path_of]: the reading of trapframe
                                   argument 0, which the walk is at *)
Require Import SysOpenDefs.
Require Import SpecSysOpen.   (* the arms this block builds *)
Require Import FsAbsCreateFire.   (* [acre_commit_at], [dlookup_commit_at]   *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.       (* [pfam]/[pf_at]: the one-shot piece's pair *)
Require Import FsAbsDefs.            (* LAST (FsAbs's own rule) *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import CtxIdDefs.

Local Open Scope Z_scope.

Set Printing Depth 40.

Section ProofSysOpenCreArm.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.

  (* ================================================================== *)
  (*  1.  THE SHIM PREDICATES                                            *)
  (* ================================================================== *)

  (* the cursor slot, TAGGED: everything below the join threads [P] and
     hands it back at the inum it walked to, so the tag comes home with the
     post's own existential and pins it. *)
  Definition socr_P (R : iProp Σ) (i0 : Z) : nat -> Z -> iProp Σ :=
    fun (_ : nat) (x : Z) => (⌜x = i0⌝ ∗ R)%I.

  Definition socr_Pm (R : iProp Σ) : nat -> Z -> iProp Σ :=
    fun (_ : nat) (_ : Z) => R.

  (* the FRESH flavour: a PURE row receipt, so the arm spends no commit *)
  Definition socr_Phio_pure (i0 : Z) (a0 : anode)
      : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    pfam_triv (fun (_ : aview) (x : Z) (a : anode) => (⌜x = i0 /\ a = a0⌝)%I).

  (* ...and the EXISTS flavour: the caller's own receipt with the row
     equation stapled on *)
  (* THE REFUND IS THE CALLER'S OWN, unchanged: the tag is on the RECEIPT
     side only, so the arm that hands this piece back hands back exactly
     what the caller invested. *)
  Definition socr_Phio_tag (i0 : Z) (a0 : anode)
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    MkPfam (fun (av : aview) (x : Z) (a : anode) =>
              (⌜x = i0 /\ a = a0⌝ ∗ Phio.(pf_recv) av x a)%I)
           Phio.(pf_refund).

  (* ================================================================== *)
  (*  2.  THE TWO RESIDUES (create's payout, held for the tail)          *)
  (* ================================================================== *)

  (* ARM C-OK's payout, plus the two commits [SysOpenDefs]'s FRESH arms
     refund and the inum bound they assert. *)
  (* THE RESIDUE IS AT THE CALLER'S OWN MODE (lane F-OPEN-3), because a
     TRUNCATING open pays the truncate's permit out of exactly these: the
     walk's terminal cursor and create's own fired receipt.  At
     [om_trunc vom = false] the residue is what it always was. *)
  Definition socr_fresh (vom : mword 64) (P : nat -> Z -> iProp Σ)
      (Phiarm Phiun : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (pl : list (bv 8)) (i0 : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜cre_pre av d nm ents nl i0 (AFile [])⌝ ∗
       ⌜0 < i0 < 16 * Z.of_nat icfg_nib⌝ ∗
       cre_cur_kept vom P (length (npar_elems pl)) d ∗
       cre_rcpt_kept vom Phiok av d nm i0 ∗
       pf_at (dlookup_commit_at (fs_gamma_L fsc_fs) appE) Phiex ∗
       pf_at (aopen_commit_at (fs_gamma_L fsc_fs) appE) Phio ∗
       (* THE TRUNC COMMIT DOES NOT RIDE HERE ANY MORE: the tail runs at the
          CALLER'S OWN [Phit] and fires it over the [itrunc], which is the
          honest reading and is what removed the one piece this proof used
          to conjure. *)
       (* ...and create's CHILD leg (round E2, lane E2-C): the unarm comes
          home; the arm's permit was SPENT by the create leg
          ([FsAbsCreateFire.acre_commit_at_gen]'s note) *)
       pf_at (aunarm_of_arm (fs_gamma_L fsc_fs) appE Phiarm) Phiun)%I.

  (* ARM F-OK's payout: the exists observation fired, the create commit
     refunded.  Both of open's own commits are SPENT by the tail on this
     flavour, so neither rides here. *)
  Definition socr_exists (vom : mword 64) (P : nat -> Z -> iProp Σ)
      (Phiarm Phiun : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) (i0 : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
       ⌜ents !! nm = Some i0⌝ ∗
       cre_cur_kept vom P (length (npar_elems pl)) d ∗
       cre_rcpt_kept vom Phiex av d nm i0 ∗
       pf_at (acre_commit_at (fs_gamma_L fsc_fs) appE (AFile [])
                (P (length (npar_elems pl))) Phiarm) Phiok ∗
       (* the name was already there: create's child legs are whole -- and
          at a TRUNCATING open the ARM's went into the permit *)
       cre_child_kept (fs_gamma_L fsc_fs) vom Phiarm Phiun)%I.

  (* THE FAMILY THE TAIL RUNS AT on this surface: the caller's own, with
     the permit kept on the refund side, so an arm that does not fire the
     truncate hands back what the permit was paid with
     ([SysOpenDefs.cre_ft_kept]). *)
  Definition socr_ft (pl : list (bv 8)) (P : nat -> Z -> iProp Σ)
      (Phiarm : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i0 : Z) (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ) :=
    cre_ft_kept (cre_permit (fs_gamma_L fsc_fs) pl P Phiarm Phiok Phiex)
      i0 Phit.

  (* the tail's family and the caller's are the same RECEIPT, and the
     piece at it is the post's own slot: both by [reflexivity], and both
     named because the definitions are sealed for [iFrame]'s sake *)
  Lemma socr_ft_recv (pl : list (bv 8)) (P : nat -> Z -> iProp Σ)
      (Phiarm : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i0 : Z) (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    (socr_ft pl P Phiarm Phiok Phiex i0 Phit).(pf_recv) = Phit.(pf_recv).
  Proof using . reflexivity. Qed.

  Lemma socr_ft_kept (vom : mword 64) (pl : list (bv 8))
      (P : nat -> Z -> iProp Σ)
      (Phiarm : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i0 : Z) (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    open_trunc_at (fs_gamma_L fsc_fs) vom i0
      (socr_ft pl P Phiarm Phiok Phiex i0 Phit)
    = cre_trunc_kept (fs_gamma_L fsc_fs) vom pl P Phiarm Phiok Phiex i0 Phit.
  Proof using . reflexivity. Qed.

  (* ================================================================== *)
  (*  2b.  PAYING THE TRUNCATE'S PERMIT (lane F-OPEN-3)                   *)
  (*                                                                     *)
  (*  This is the ONE place the permit is paid, and it is the only place  *)
  (*  that can pay it: create has just returned a node, so the walk's     *)
  (*  terminal cursor, the tie and whichever of the two arms ran are all  *)
  (*  in hand, and everything below the join only ever needs the commit   *)
  (*  AT THAT INUM ([SysOpenDefs.open_trunc_at]).  What the permit takes  *)
  (*  is exactly what the residue then stops carrying, which is why the   *)
  (*  two are built by one lemma.                                        *)
  (* ================================================================== *)

  Lemma socr_fresh_key `{GEN : GenId} (vom : mword 64) (P : nat -> Z -> iProp Σ)
      (Phiarm Phiun : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (pl : list (bv 8)) (i0 d : Z) (nm : fname) (av : aview)
      (ents : gmap fname Z) (nl : nat) :
    list_basics.last (path_elems pl) = Some nm ->
    cre_pre av d nm ents nl i0 (AFile []) ->
    0 < i0 < 16 * Z.of_nat icfg_nib ->
    P (length (npar_elems pl)) d -∗
    Phiok.(pf_recv) av d nm i0 -∗
    pf_at (dlookup_commit_at (fs_gamma_L fsc_fs) appE) Phiex -∗
    pf_at (aopen_commit_at (fs_gamma_L fsc_fs) appE) Phio -∗
    pf_at (aunarm_of_arm (fs_gamma_L fsc_fs) appE Phiarm) Phiun -∗
    open_trunc_piece (fs_gamma_L fsc_fs) vom
      (trunc_permit_of (fs_gamma_L fsc_fs) (trunc_tie_at pl P)
         Phiarm Phiok Phiex) Phit -∗
    socr_fresh vom P Phiarm Phiun Phiok Phiex Phio pl i0
    ∗ open_trunc_at (fs_gamma_L fsc_fs) vom i0
        (socr_ft pl P Phiarm Phiok Phiex i0 Phit).
  Proof using .
    intros Hl Hpre Hib. iIntros "HP HPhi Hdl Hoc Hun Htc".
    rewrite /socr_ft.
    iAssert (socr_fresh vom P Phiarm Phiun Phiok Phiex Phio pl i0
             ∗ (if om_trunc vom
                then cre_permit (fs_gamma_L fsc_fs) pl P Phiarm Phiok Phiex i0
                else emp))%I with "[HP HPhi Hdl Hoc Hun]" as "[HR Hk]".
    { rewrite /socr_fresh /cre_cur_kept /cre_rcpt_kept.
      destruct (om_trunc vom).
      - iSplitR "HP HPhi".
        { iExists d, nm, av, ents, nl.
          iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
          iSplitR; [by iPureIntro |]. iSplitR; [done |]. iSplitR; [done |].
          iFrame "Hdl Hoc Hun". }
        rewrite /cre_permit /trunc_permit_of /trunc_tie_at. iExists d, nm.
        iSplitL "HP"; [ iSplitR; [by iPureIntro | iExact "HP"] |].
        iLeft. rewrite /cre_acre_fired. iExists av, ents, nl.
        iSplitR; [by iPureIntro |]. iExact "HPhi".
      - iSplitL; [| done]. iExists d, nm, av, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |]. iFrame "HP HPhi Hdl Hoc Hun". }
    iFrame "HR".
    iApply (open_trunc_at_of_permit (fs_gamma_L fsc_fs) vom
              (cre_permit (fs_gamma_L fsc_fs) pl P Phiarm Phiok Phiex) i0 Phit
              with "Htc Hk").
  Qed.

  Lemma socr_exists_key `{GEN : GenId} (vom : mword 64) (P : nat -> Z -> iProp Σ)
      (Phiarm Phiun : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (pl : list (bv 8)) (i0 d : Z) (nm : fname) (av : aview)
      (ents : gmap fname Z) (nl : nat) :
    list_basics.last (path_elems pl) = Some nm ->
    av !! d = Some (MkAnode (ADir ents) nl) ->
    ents !! nm = Some i0 ->
    P (length (npar_elems pl)) d -∗
    Phiex.(pf_recv) av d nm i0 -∗
    pf_at (acre_commit_at (fs_gamma_L fsc_fs) appE (AFile [])
             (P (length (npar_elems pl))) Phiarm) Phiok -∗
    cre_child_unfired (fs_gamma_L fsc_fs) (AFile []) Phiarm Phiun -∗
    open_trunc_piece (fs_gamma_L fsc_fs) vom
      (trunc_permit_of (fs_gamma_L fsc_fs) (trunc_tie_at pl P)
         Phiarm Phiok Phiex) Phit -∗
    socr_exists vom P Phiarm Phiun Phiok Phiex pl i0
    ∗ open_trunc_at (fs_gamma_L fsc_fs) vom i0
        (socr_ft pl P Phiarm Phiok Phiex i0 Phit).
  Proof using .
    intros Hl Hrow Hent. iIntros "HP HPhi Hac Hcl Htc".
    rewrite /socr_ft /cre_child_unfired.
    iDestruct "Hcl" as "[Harm Hun]".
    iAssert (socr_exists vom P Phiarm Phiun Phiok Phiex pl i0
             ∗ (if om_trunc vom
                then cre_permit (fs_gamma_L fsc_fs) pl P Phiarm Phiok Phiex i0
                else emp))%I with "[HP HPhi Hac Harm Hun]" as "[HR Hk]".
    { rewrite /socr_exists /cre_cur_kept /cre_rcpt_kept /cre_child_kept.
      destruct (om_trunc vom).
      - iSplitR "HP HPhi Harm".
        { iExists d, nm, av, ents, nl.
          iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
          iSplitR; [by iPureIntro |]. iSplitR; [done |]. iSplitR; [done |].
          iFrame "Hac Hun". }
        rewrite /cre_permit /trunc_permit_of /trunc_tie_at. iExists d, nm.
        iSplitL "HP"; [ iSplitR; [by iPureIntro | iExact "HP"] |].
        iRight. iSplitR "Harm"; [| iExact "Harm" ].
        rewrite /cre_ex_fired. iExists av, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iExact "HPhi".
      - iSplitL; [| done]. iExists d, nm, av, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |]. iFrame "HP HPhi Hac Harm Hun". }
    iFrame "HR".
    iApply (open_trunc_at_of_permit (fs_gamma_L fsc_fs) vom
              (cre_permit (fs_gamma_L fsc_fs) pl P Phiarm Phiok Phiex) i0 Phit
              with "Htc Hk").
  Qed.

  (* ================================================================== *)
  (*  3.  THE TWO OBSERVATION SEEDS                                      *)
  (* ================================================================== *)

  (* the FRESH tail's receipt costs NOTHING: it is a row equation, and the
     singleton map is its witness. *)
  Lemma socr_obs_pure (i0 : Z) (n0 : fs_node) :
    ⊢ so_obs (socr_Phio_pure i0 (abs_row n0)) i0 n0.
  Proof using .
    rewrite /so_obs /socr_Phio_pure.
    iExists (if decide (an_nlink (abs_row n0) = 0%nat) then ∅
             else {[ i0 := abs_row n0 ]} : aview).
    iSplitR; [iPureIntro; apply arow_at_witness |].
    iPureIntro. split; reflexivity.
  Qed.

  (* ...and the EXISTS tail's is the real fire, tagged. *)
  Lemma socr_obs_tag (i0 : Z) (n0 : fs_node)
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ)) :
    (∃ av : aview, ⌜arow_at av i0 (abs_row n0)⌝ ∗ Phio.(pf_recv) av i0 (abs_row n0))
    -∗ so_obs (socr_Phio_tag i0 (abs_row n0) Phio) i0 n0.
  Proof using .
    iIntros "H". iDestruct "H" as (av) "[%Hav HP]".
    rewrite /so_obs /socr_Phio_tag. cbn [pf_recv pf_refund]. iExists av.
    iSplitR; [by iPureIntro |]. iFrame "HP".
    iPureIntro. split; reflexivity.
  Qed.

  (* ================================================================== *)
  (*  4.  RECOVERING THE RESIDUE FROM THE PLAIN FOLD                     *)
  (* ================================================================== *)

  (* THE READING IS A PREMISE, and it is what fires the walk's wand on the
     "nothing happened" arm: the bundle owes the walk at the string argument
     0 names ([SysOpenDefs.open_au_plain_at]), and create's own argstr has
     already answered by the time this conversion runs.  Which path it is
     does not matter here -- only [R] is wanted of the cursor. *)
  Lemma socr_res_of_fail (cw : Z) (R : iProp Σ) (i0 : Z)
      (Mim : gmap Z (bv 8)) (pvv vom : mword 64) (pl0 : list (bv 8))
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of Mim pvv pl0 ->
    open_post_fail_plain (fs_gamma_L fsc_fs) fsc_fs cw Mim pvv vom
      (socr_P R i0) (socr_Pm R) Phio Phit
    ={⊤}=∗ R
           ∗ (pf_at (aopen_commit_at (fs_gamma_L fsc_fs) appE) Phio
              ∨ (∃ (i : Z) (av : aview) (a : anode),
                   ⌜arow_at av i a⌝ ∗ Phio.(pf_recv) av i a))
           (* the piece comes home KEYED at the node the call reached: the
              two arms above the join carry the plain surface's own
              (trivially permitted) piece, which keys for nothing *)
           ∗ open_trunc_at (fs_gamma_L fsc_fs) vom i0 Phit.
  Proof using .
    intros Hpl0.
    rewrite /open_post_fail_plain /socr_P /socr_Pm.
    iIntros "H". iDestruct "H" as "[Hpre | H]".
    - rewrite /open_au_plain_at. iDestruct "Hpre" as "(Hwp & Hoc & Htc)".
      (* the walk's wand fires at the path argument 0 names, and the
         one-shot then at that path's own start; only [R] is wanted *)
      iDestruct ("Hwp" $! pl0 with "[%]") as "Hst"; [exact Hpl0 |].
      rewrite /FsAbsEra.ex_start.
      iMod ("Hst" $! (FsAbsEra.um_start_of cw pl0) with "[//]") as "[HP _]".
      iDestruct "HP" as "[_ HR]".
      iDestruct (open_trunc_at_of_triv (fs_gamma_L fsc_fs) vom i0 Phit
                   with "Htc") as "Htc".
      iModIntro. iFrame "HR Htc". by iLeft.
    - iDestruct "H" as (pl) "[_ [Hd | Hf]]".
      + iDestruct "Hd" as "(Hdead & Hoc & Htc)".
        rewrite /namei_walk_dead_era.
        iDestruct (open_trunc_at_of_triv (fs_gamma_L fsc_fs) vom i0 Phit
                     with "Htc") as "Htc".
        iDestruct "Hdead" as (k d) "(_ & [[HP _] | [HPm _]])".
        * iDestruct "HP" as "[_ HR]".
          iModIntro. iFrame "HR Htc". by iLeft.
        * iModIntro. iFrame "HPm Htc". by iLeft.
      + iDestruct "Hf" as (i) "(HP & Hobs & Htc)".
        iDestruct "HP" as "[%Hii HR]". subst i.
        iDestruct "Hobs" as (av a) "[%Hav HPhi]".
        iModIntro. iFrame "HR Htc". iRight.
        iExists i0, av, a. iSplitR; [by iPureIntro |]. iExact "HPhi".
  Qed.

  (* ================================================================== *)
  (*  5.  RECOVERING THE RESIDUE AND THE DESCRIPTOR FROM THE PLAIN OK    *)
  (* ================================================================== *)

  (* THE FRESH READING.  The tail's DEVICE and DIRECTORY arms are refuted
     by the pure receipt: create ran at T_FILE, so the observed row is an
     [AFile]. *)
  (* ...AND THE TRUNC COMPONENT COMES OUT WITH IT, at the caller's own
     [Phit]: the tail's FILE arm delivers the receipt iff O_TRUNC, and the
     pure observation receipt is what identifies the bytes it is at with
     the [bs] the create arm named. *)
  Lemma socr_ok_fresh_arm `{GEN : GenId}
      (R : iProp Σ) (i0 : Z) (bs : list (bv 8)) (nl0 : nat)
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (gf : gname) (pj : mword 64) (pidv : mword 32)
      (Mim : gmap Z (bv 8)) (pvv vom : mword 64)
      (U : ustate) (sts : list fdstate) (r : mword 64) :
    open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv Mim pvv vom
      (socr_P R i0) (socr_Phio_pure i0 (MkAnode (AFile bs) nl0))
      Phit sts U r
    ⊢ R
      ∗ (if om_trunc vom
         then ∃ (av' : aview) (nl' : nat),
                ⌜arow_at av' i0 (MkAnode (AFile bs) nl')⌝ ∗
                Phit.(pf_recv) av' i0 bs
         else emp)
      ∗ ∃ γo : gname,
            open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
              (FdInode i0 γo OffParked) sts r.
  Proof using .
    rewrite /open_post_ok_plain /socr_P /socr_Phio_pure.
    cbn [pf_recv pf_refund].
    iIntros "H". iDestruct "H" as (pl av i) "[_ [[%Hi HR] Harm]]".
    subst i.
    iDestruct "Harm" as "[Hdev | [Hfil | Hdir]]".
    - iDestruct "Hdev" as (ma mi nl) "(_ & _ & %Hbad & _)".
      destruct Hbad as [_ Hbad]. inversion Hbad.
    - iDestruct "Hfil" as (bs0 nl) "(%Hrow & %Heq & Htr & Hfd)".
      destruct Heq as [_ Heq]. injection Heq as Hbs Hnl.
      subst bs0. iFrame "HR Hfd".
      destruct (om_trunc vom).
      + iDestruct "Htr" as (av') "[%Hrow' HP]".
        iExists av', nl. iSplitR; [by iPureIntro |]. iExact "HP".
      + iExact "Htr".
    - iDestruct "Hdir" as (ents nl) "(_ & _ & %Hbad & _)".
      destruct Hbad as [_ Hbad]. inversion Hbad.
  Qed.

  (* THE EXISTS READING.  The DIRECTORY arm is refuted by the staple: ARM
     F-OK admits only [T_FILE] and [T_DEVICE], so the observed row is not
     an [ADir]; the other two arms ARE [open_post_ok_create]'s EXISTS
     sub-arms, verbatim. *)
  Lemma socr_ok_exists_arm `{GEN : GenId}
      (R : iProp Σ) (i0 : Z) (a0 : anode)
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (gf : gname) (pj : mword 64) (pidv : mword 32)
      (Mim : gmap Z (bv 8)) (pvv vom : mword 64)
      (U : ustate) (sts : list fdstate) (r : mword 64) :
    (forall (ents : gmap fname Z) (nl : nat), a0 <> MkAnode (ADir ents) nl) ->
    open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv Mim pvv vom
      (socr_P R i0) (socr_Phio_tag i0 a0 Phio) Phit sts U r
    ⊢ R ∗ ∃ (av : aview) (nl : nat),
        ((∃ bs0 : list (bv 8),
            ⌜arow_at av i0 (MkAnode (AFile bs0) nl)⌝ ∗
            Phio.(pf_recv) av i0 (MkAnode (AFile bs0) nl) ∗
            (if om_trunc vom
             then ∃ av' : aview,
                    ⌜arow_at av' i0 (MkAnode (AFile bs0) nl)⌝ ∗
                    Phit.(pf_recv) av' i0 bs0
             else emp) ∗
            ∃ γo : gname,
              open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
                (FdInode i0 γo OffParked) sts r)
         ∨ (∃ ma mi : Z,
              ⌜arow_at av i0 (MkAnode (ADev ma mi) nl)⌝ ∗
              ⌜0 <= ma <= NDEV_max⌝ ∗
              Phio.(pf_recv) av i0 (MkAnode (ADev ma mi) nl) ∗
              open_trunc_at (fs_gamma_L fsc_fs) vom i0 Phit ∗
              open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
                (FdDevice ma) sts r)).
  Proof using .
    intros Hnd.
    rewrite /open_post_ok_plain /socr_P /socr_Phio_tag.
    cbn [pf_recv pf_refund].
    iIntros "H". iDestruct "H" as (pl av i) "[_ [[%Hi HR] Harm]]".
    subst i. iFrame "HR".
    iDestruct "Harm" as "[Hdev | [Hfil | Hdir]]".
    - iDestruct "Hdev" as (ma mi nl) "(%Hrow & %Hmb & [_ HPhi] & Htc & Hfd)".
      iExists av, nl. iRight. iExists ma, mi.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HPhi Htc Hfd".
    - iDestruct "Hfil" as (bs0 nl) "(%Hrow & [_ HPhi] & Htr & Hfd)".
      iExists av, nl. iLeft. iExists bs0.
      iSplitR; [by iPureIntro |]. iFrame "HPhi Htr Hfd".
    - iDestruct "Hdir" as (ents nl) "(_ & _ & [%Hbad _] & _)".
      destruct Hbad as [_ Hbad]. exfalso. exact (Hnd ents nl (eq_sym Hbad)).
  Qed.

  (* ================================================================== *)
  (*  6.  THE TWO ARM CONVERSIONS                                        *)
  (* ================================================================== *)

  Lemma socr_arms_fresh `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32)
      (Mim : gmap Z (bv 8)) (pvv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phiarm Phiun : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (U : ustate) (sts : list fdstate) (r : mword 64) (pl : list (bv 8)) (i0 : Z)
      (nl0 : nat) :
    arg_path_of Mim pvv pl ->
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv
      Mim pvv vom
      (socr_P (socr_fresh vom P Phiarm Phiun Phiok Phiex Phio pl i0) i0)
      (socr_Pm (socr_fresh vom P Phiarm Phiun Phiok Phiex Phio pl i0))
      (socr_Phio_pure i0 (MkAnode (AFile []) nl0))
      (socr_ft pl P Phiarm Phiok Phiex i0 Phit) sts U r
    ={⊤}=∗ open_arms_create (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv
             Mim pvv vom
             P Pmiss Phiarm Phiun Phiok Phiex Phio Phit sts U r.
  Proof using .
    intros Hpl.
    rewrite /open_arms_plain /open_arms_create.
    iIntros "[Harms $]".
    iDestruct "Harms" as "[Hfail | Hok]".
    - iDestruct "Hfail" as "(%Hr & Hpriv & Hfrag & Hf)".
      (* THE FAIL SIDE IS UNCHANGED BY B-TRUNC: every post-walk failure sits
         BEFORE the [itrunc] (the two table-full arms return at +0x...,
         above it), so the caller's trunc piece comes home unfired and arm
         (a) is stated at the piece exactly as it was. *)
      iMod (socr_res_of_fail _ _ _ _ _ _ pl _ _ Hpl with "Hf") as "(HR & _ & Htc)".
      iModIntro. iLeft. iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
      rewrite /open_post_fail_create /socr_fresh.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hpre & %Hib & HP & HPhi & Hdl & Hoc & Hun)".
      iRight. iExists pl. iSplitR; [by iPureIntro |].
      iRight. iExists d. iFrame "HP".
      iLeft. iExists av, i0, nm, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iEval (rewrite /socr_ft) in "Htc". rewrite /cre_trunc_kept.
      iFrame "HPhi Hdl Hoc Htc Hun".
    - iDestruct (socr_ok_fresh_arm with "Hok") as "(HR & Htr & Hfd)".
      iEval (rewrite socr_ft_recv) in "Htr".
      rewrite /socr_fresh.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hpre & %Hib & HP & HPhi & Hdl & Hoc & Hun)".
      iModIntro. iRight. rewrite /open_post_ok_create.
      iExists pl, d, i0, nm.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iFrame "HP".
      iLeft. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HPhi Hdl Hoc Htr Hun Hfd".
  Qed.

  Lemma socr_arms_exists `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32)
      (Mim : gmap Z (bv 8)) (pvv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phiarm Phiun : pfam Σ (aview -> Z -> iProp Σ))
      (Phiok Phiex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Phio : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Phit : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (U : ustate) (sts : list fdstate) (r : mword 64) (pl : list (bv 8)) (i0 : Z) (a0 : anode) :
    arg_path_of Mim pvv pl ->
    (forall (ents : gmap fname Z) (nl : nat), a0 <> MkAnode (ADir ents) nl) ->
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv
      Mim pvv vom
      (socr_P (socr_exists vom P Phiarm Phiun Phiok Phiex pl i0) i0)
      (socr_Pm (socr_exists vom P Phiarm Phiun Phiok Phiex pl i0))
      (socr_Phio_tag i0 a0 Phio)
      (socr_ft pl P Phiarm Phiok Phiex i0 Phit) sts U r
    ={⊤}=∗ open_arms_create (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv
             Mim pvv vom
             P Pmiss Phiarm Phiun Phiok Phiex Phio Phit sts U r.
  Proof using .
    intros Hpl Hnd.
    rewrite /open_arms_plain /open_arms_create.
    iIntros "[Harms $]".
    iDestruct "Harms" as "[Hfail | Hok]".
    - iDestruct "Hfail" as "(%Hr & Hpriv & Hfrag & Hf)".
      iMod (socr_res_of_fail _ _ _ _ _ _ pl _ _ Hpl with "Hf") as "(HR & Hob & Htc)".
      iModIntro. iLeft. iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
      rewrite /open_post_fail_create /socr_exists.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hrow & %Hent & HP & HPhi & Hac & Hcl)".
      iRight. iExists pl. iSplitR; [by iPureIntro |].
      iRight. iExists d. iFrame "HP".
      iRight. iLeft. iExists av, i0, nm, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iFrame "HPhi Hac".
      iSplitL "Htc Hcl".
      { iEval (rewrite /socr_ft) in "Htc".
        iApply (cre_fail_kept_of_at with "Htc Hcl"). }
      iDestruct "Hob" as "[Hoc | Hfired]".
      + (* THE TAG COMES OFF THE RECEIPT AND THE REFUND IS UNTOUCHED: both
           pairs carry [Phio]'s own refund, so the equation is [eq_refl]
           and only the AU side is re-proved. *)
        iLeft.
        iApply (pf_at_mono_pair (aopen_commit_at (fs_gamma_L fsc_fs) appE)
                  (aopen_commit_at (fs_gamma_L fsc_fs) appE)
                  (socr_Phio_tag i0 a0 Phio) Phio eq_refl with "[] Hoc").
        iIntros "Hoc".
        rewrite /aopen_commit_at /socr_Phio_tag. cbn [pf_recv].
        iIntros (I ix a) "%Hix Ha".
        iMod ("Hoc" $! I ix a with "[//] Ha") as "[Ha [_ HP2]]".
        iModIntro. iFrame "Ha HP2".
      + iRight. rewrite /socr_Phio_tag. cbn [pf_recv pf_refund].
        iDestruct "Hfired" as (ix avx ax) "(%Hax & [%Heq HP2])".
        destruct Heq as [Hix _]. subst ix.
        iExists avx, ax. iSplitR; [by iPureIntro |]. iExact "HP2".
    - iDestruct (socr_ok_exists_arm (socr_exists vom P Phiarm Phiun Phiok Phiex pl i0)
                   i0 a0 Phio (socr_ft pl P Phiarm Phiok Phiex i0 Phit)
                   gf pj pidv Mim pvv vom U sts r Hnd with "Hok")
        as "[HR Hrest]".
      iEval (rewrite socr_ft_recv socr_ft_kept) in "Hrest".
      rewrite /socr_exists.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hrow & %Hent & HP & HPhi & Hac & Hcl)".
      iModIntro. iRight. rewrite /open_post_ok_create.
      iExists pl, d, i0, nm.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iFrame "HP".
      iRight. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HPhi Hac Hcl Hrest".
  Qed.

End ProofSysOpenCreArm.

Global Typeclasses Opaque socr_fresh socr_exists socr_ft.
