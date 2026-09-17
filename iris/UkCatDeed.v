(* ===================================================================== *)
(* UkCatDeed.v -- cat's SYSCALL STUBS AT THE FILE APPLICATION'S DEED      *)
(* (lane CAT-WALK, W3).                                                  *)
(*                                                                       *)
(* [UkCat.v] states what each of cat's calls SPENDS -- [UkCat.kcat_r] for *)
(* the read, [UkCat.kcat_o] for the open, [UkCat.kcat_w] for the write -- *)
(* and proves the FREE instance of each over the flagged deposits.  This  *)
(* file proves the DEED instance of the read: the same three             *)
(* instructions, over [UkFileOpen.wp_uk_read_deed_learns_mapped] instead  *)
(* of [UkRunSys.wp_uk_ecall_read], at [FileOpen]'s deposit instead of     *)
(* [UkRun.udepw_law 5], and with an output that says WHICH BYTES landed   *)
(* in the buffer.                                                        *)
(*                                                                       *)
(* WHY IT IS A SEPARATE FILE.  [UkCat.v] sits below the file system and   *)
(* names no application; the deed leaf is above [AppFile] and drags the   *)
(* whole FS tower in.  Keeping the two apart is what stops ten thousand   *)
(* lines of cat's walk from depending on [FileOpen]                       *)
(* (design/code-organization.md, import discipline).                     *)
(*                                                                       *)
(* AND WHY THE `cat: read error` ARM IS NOT HERE.  Lane READ-RELAY's      *)
(* [wp_uk_read_deed_learns_mapped] has NO [rv = -1] disjunct at a buffer  *)
(* the caller owns, so the payer that builds a round out of this          *)
(* discharges [UkCatCat.kcat_round]'s read-error arm VACUOUSLY: the       *)
(* count it gets back is an [ard_count], which is not negative.          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import VcGen.            (* [trunc32_mword_of_int] -- a0 read as a C [int] *)
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UCodeCat.
Require Import CtxIdDefs.
Require User.CatSyms User.CatInstrs.
Require Import ChildTok.
Require Import FdSlots PipeNames ProcGeom UserFd UserCwd.
Require Import UexecSG UexecSlot UexecRet UsysMemOk.
Require Import UexecExecInst.  (* THE INSTANCES: [uexecSG_xv6], [uprogSG_gen] *)
Require Import UkCat.
Require Import UkFileOpen.
Require Import AppCfg AppInv AppFile FileOpen FsCfg FsImgCheck.
Require Import ArgPath.          (* [arg_path_of] -- the open's path row *)
Require Import PathElems.        (* [path_elems] *)
Require Import SysOpenDefs.      (* [om_create] / [om_readable] *)
Require Import FsAbsEra.         (* [um_start_of] *)
Require Import FsImg.            (* [FsImg.ROOTINO] *)
Require Import ProcGeom.         (* [NOFILE] *)
Require Import ConsoleInv.
Require Import SysReadDefs.     (* [ard_count] -- what a read of a parked row delivers *)
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs BioDefs.
Require Import EchoOut AppEcho.
Import Defs.

Local Open Scope Z_scope.

Section UkCatDeed.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  (* NO SEPARATE [ghost_varG] / [ctokG] CONTEXTS.  [Xv6G.xv6G] carries
     both ([xv6_uch], [xv6_ctok]), and declaring a second copy here gives
     [UkRun.urun] a DIFFERENT instance in this file's own statements from
     the one [UkFileOpen]'s lemmas were proved at -- two propositions that
     PRINT identically and do not unify.  That is what cost this file two
     builds. *)
  (* ...AND NO [uexecSG] OR [uprogSG] VARIABLE EITHER (lane CAT-WALK-2,
     K2).  This is the SAME defect one class further out, and it is what
     made lane CAT-WALK's [iApply] diverge.  [UkFileOpen.v] declares
     neither, so every [UkRun.urun] in its statements is at the AMBIENT
     pair that resolution finds -- [UexecExecInst.uexecSG_xv6] and
     [uprogSG_gen].  A section variable of either class here is a SECOND
     instance, local hypotheses win resolution, and this file's [urun]
     would then be a different proposition from the one the leaf's
     statement is about -- printing identically, and sending unification
     into [UexecSG.sbundle]'s tower after a match that cannot be made.
     [UEchoOut.v]'s header records the [uexecSG] half of the same rule;
     the [uprogSG] half is this lane's, and it PINS these corollaries to
     the generic-slot instance, exactly as [UkFileOpen]'s own are. *)
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (* read @0x3c4 AT THE DEED.                                            *)
  (*                                                                     *)
  (* [UkCat.wp_kcat_read]'s three instructions, with the ecall taken at   *)
  (* the deed-aware leaf.  The statement is the landed stub's with two    *)
  (* changes and no more: the flagged deposit is replaced by the deed's   *)
  (* own premises (the handle on the deed's inum, the claim's console     *)
  (* flag, the application invariant, the fraction), and the buffer comes *)
  (* back with the bytes NAMED.                                          *)
  (* =================================================================== *)
  Lemma wp_kcat_read_deed (a : Z) (cnt : nat) (f : nat -> bv 8)
      (h : CpuId) (m : regfile) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jc : Z)
      (bs : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    0 <= a -> a < Z64 ->
    m !!! Regidx a1_idx = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
      = Z.of_nat cnt ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    cat_code γt -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    fdq r q (Some (i, bs)) -∗
    ubytes γd a cnt f -∗
    urun N h m (mword_of_int CatSyms.read) avail -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       (((∃ off : nat,
            ⌜Z.to_nat (bv_unsigned rv)
             = ard_count cnt off (length bs)⌝ ∗
            ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
               gb j = bs !!! (off + j)%nat⌝)
         ∗ fdq r q (Some (i, bs)))
        ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)) -∗
       ubytes γd a cnt gb -∗
       urun N h'
         (<[Regidx a0_idx := rv]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Ha0 Hahi Ha1 Hcnt Hfdv Hfdlt.
    iIntros "#Hcode Hufdh #Hm #Hinv Hd Hbs Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hread & _ & _ & _ & _).
    rewrite Hread.
    (* ---- 0x3c4  c.li a7,5 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3c4)
              (mword_of_int 5 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3c4 with "Hcode"). }
    assert (E0r : add_vec_int (mword_of_int 0x3c4 : mword 64) 2
                  = mword_of_int 0x3c6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emr : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 5 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0r Emr.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int a : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcntr : bv_signed (subrange_vec_dec (m1 !!! Regidx a2_idx) 31 0
                               : mword 32) = Z.of_nat cnt).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hcnt. }
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hfdv. }
    assert (Hua : uint (m1 !!! Regidx a1_idx) = a)
      by (rewrite Ha1r; apply uint_moi; unfold Z64 in *; lia).
    (* ---- 0x3c6  ecall -- THE DEED'S OWN LEAF ---- *)
    iEval (rewrite <- Hua) in "Hbs".
    iDestruct (uis_cat_3c6 with "Hcode") as "#Hi3c6".
    assert (Hnum : usysno m1 = USYS_read).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hcapk : (Z.to_nat (Z.of_nat cnt) <= cnt)%nat)
      by (rewrite Nat2Z.id; lia).
    assert (Hcnt0 : (0 <= Z.of_nat cnt)%Z) by lia.
    (* HOISTED, not spliced as an inline [ltac:] in argument position.
       optimization.md's "Inline [ltac:] in argument position" and
       durable-notes' "Inline [ltac:] and evar-typed holes" are about the
       COST and the divergence; this site adds a third symptom, which is
       worth knowing: at a twenty-five-argument application the spliced
       tactic can make the whole [iApply ( … with "…")] mis-elaborate, and
       what comes out is [iSpecialize: cannot instantiate <the remaining
       wands> with <the type of the first hypothesis>] -- a message that
       points at the spec list and not at the argument that caused it. *)
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int 0x3c6 : mword 64) 4))
                     2 = true)
      by (vm_compute; reflexivity).
    (* THE UNSHELVE HOIST (lane CAT-WALK-2, K2).  The application above --
       twenty-five arguments elaborated together with a seven-hypothesis
       spec list -- DID NOT TERMINATE: three compiles ran to tens of
       minutes with no error and no [.vo] (lane CAT-WALK's W3).  Hoisting
       the two inline [ltac:] closers into named [assert]s was not enough,
       because the cost is not the closers: it is that [iApply] elaborates
       the Coq arguments and unifies the whole spec list in ONE pass, so
       every hypothesis is matched against a conclusion whose fifteen
       parameters are still evars.
       The remedy is to SEPARATE the two.  [iPoseProof] at the explicit
       arguments is a pure Coq application: the fifteen parameters are
       given, the eight premises are checked, and what lands in the
       context is a closed chain of wands.  The [iApply] that follows
       then has nothing left to solve but the seven hypotheses, each
       against a wand whose type is already ground.  Cost: seconds. *)
    iPoseProof (wp_uk_read_deed_learns_mapped N h1 m1 (mword_of_int 0x3c6)
                  (Z.of_nat cnt) cnt f avail fd wb i γo c r q jc bs Heq
                  Hnum Hcntr Hcnt0 Hcapk Ha0r Hfdlt Hal4)
      as "Hleaf".
    iApply ("Hleaf" with "Hi3c6 Hrun Hufdh Hm Hinv Hd Hbs").
    assert (E1r : add_vec_int (mword_of_int 0x3c6 : mword 64) 4
                  = mword_of_int 0x3ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1r.
    iIntros (h2 rv gb) "Hufdh Hans Hrun Hbs".
    iEval (rewrite Hua) in "Hbs".
    iEval (rewrite Nat2Z.id) in "Hans".
    set (m2 := <[Regidx a0_idx := rv]> m1).
    (* ---- 0x3ca  c.jr ra ---- *)
    assert (Hrar : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) rv
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 5 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3ca) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ca with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 rv gb with "Hufdh Hans Hbs Hrun").
  Qed.

  (* =================================================================== *)
  (* ...AND THE OBLIGATION AT IT.                                        *)
  (*                                                                     *)
  (* [UkCat.kcat_r_of_law]'s twin: the read obligation cat's loop spends, *)
  (* at the deed.  The handle and the fraction ride in the obligation's   *)
  (* two halves (they are linear and the loop turns many times), and the  *)
  (* claim's console flag and the application invariant are persistent    *)
  (* and stay outside.                                                   *)
  (* =================================================================== *)
  Definition kcat_deed_hold (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (r : file_names) (q : Qp) (bs : list (bv 8)) : iProp Σ :=
    (UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked))
     ∗ fdq r q (Some (i, bs)))%I.

  Lemma kcat_r_of_deed (a : Z) (cnt : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jc : Z)
      (bs : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    0 <= a -> a < Z64 ->
    (fd < NOFILE)%nat ->
    cat_code γt -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    UkCat.kcat_r N (mword_of_int (Z.of_nat fd)) a cnt
      (kcat_deed_hold fd wb i γo r q bs)
      (fun (rv : mword 64) (gb : nat -> bv 8) =>
         (kcat_deed_hold fd wb i γo r q bs
          ∗ ((∃ off : nat,
                ⌜Z.to_nat (bv_unsigned rv)
                 = ard_count cnt off (length bs)⌝ ∗
                ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                   gb j = bs !!! (off + j)%nat⌝)
             ∨ file_taint c))%I).
  Proof using .
    intros Heq Ha0 Hahi Hfdlt.
    iIntros "#Hcode #Hm #Hinv" (h m avail f) "%Ha0v %Ha1 %Ha2 _ Hhold Hbs Hrun Hcont".
    iDestruct "Hhold" as "[Hufdh Hd]".
    assert (Hfdv : bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd).
    { rewrite Ha0v trunc32_mword_of_int.
      assert (Hr31 : (0 <= Z.of_nat fd < 2 ^ 31)%Z).
      { unfold NOFILE in Hfdlt.
        assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
        lia. }
      assert (Hbw : bv_wrap 32 (Z.of_nat fd) = Z.of_nat fd)
        by (apply bvw32_small; lia).
      unfold bv_signed. rewrite moi32_unsigned Hbw.
      apply bv_swrap_small.
      assert (Hh32 : bv_half_modulus 32 = 2147483648%Z)
        by (vm_compute; reflexivity).
      rewrite Hh32. lia. }
    iApply (wp_kcat_read_deed a cnt f h m avail fd wb i γo c r q jc bs
              Heq Ha0 Hahi Ha1 Ha2 Hfdv Hfdlt
              with "Hcode Hufdh Hm Hinv Hd Hbs Hrun").
    iIntros (h' rv gb) "Hufdh Hans Hbs Hrun".
    iApply ("Hcont" $! h' rv gb with "[Hufdh Hans] Hbs Hrun").
    iDestruct "Hans" as "[[Hok Hd] | [Hd HT]]".
    - iFrame "Hufdh Hd". by iLeft.
    - iFrame "Hufdh Hd". by iRight.
  Qed.

  (* =================================================================== *)
  (*  THE ORDERING, CONDITIONALLY (the designer's ruling for W3/W4).       *)
  (*                                                                     *)
  (*  At a PARKED row the leaf reports the bytes at SOME offset -- the    *)
  (*  [∃ off] above -- because [FdInode i γo OffParked] records no        *)
  (*  offset at all: the kernel holds the file's own [f->off] and the     *)
  (*  descriptor state says nothing about it.  So -- the bytes cat        *)
  (*  writes are the deed's content IN ORDER -- is NOT provable from the  *)
  (*  parked leaf, and nothing here tries.                                *)
  (*                                                                     *)
  (*  What the ordering needs is ONE premise, and this lemma names it     *)
  (*  exactly: every offset the read reports IS the one the caller        *)
  (*  expects.  At [OffParked] that is unprovable and a caller takes      *)
  (*  [kcat_r_of_deed] instead; at the HELD row lane OFF-HAND is landing  *)
  (*  ([FdInode i γo (OffHeld off)], advanced by each read) it is the     *)
  (*  descriptor state's own row, and the held leaf discharges it.        *)
  (*                                                                     *)
  (*  WITH IT THE LOOP'S ORDERING CLOSES ENTIRELY PAYER-SIDE.             *)
  (*  [UkCatCat.kcat_round] says nothing about offsets: the payer builds  *)
  (*  the round holding its own cursor [I], and at a turn whose cursor is *)
  (*  [p] it instantiates this lemma at [off0 := p].  The count comes     *)
  (*  back as [ard_count cnt p (length bs)], so the next turn's cursor is *)
  (*  [p + that], which is the chaining-from-zero the ordering wants --   *)
  (*  and the walk in [UkCatCat.v] never sees any of it.                  *)
  (* =================================================================== *)
  Lemma kcat_r_of_deed_at (a : Z) (cnt : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jc : Z)
      (bs : list (bv 8)) (off0 : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    0 <= a -> a < Z64 ->
    (fd < NOFILE)%nat ->
    (* THE PREMISE THE HELD LEAF MUST DISCHARGE, and the only one. *)
    □ (∀ (rv : mword 64) (gb : nat -> bv 8) (off : nat),
         ⌜Z.to_nat (bv_unsigned rv) = ard_count cnt off (length bs)⌝ -∗
         ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
            gb j = bs !!! (off + j)%nat⌝ -∗
         ⌜off = off0⌝) -∗
    cat_code γt -∗
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    UkCat.kcat_r N (mword_of_int (Z.of_nat fd)) a cnt
      (kcat_deed_hold fd wb i γo r q bs)
      (fun (rv : mword 64) (gb : nat -> bv 8) =>
         (kcat_deed_hold fd wb i γo r q bs
          ∗ ((⌜Z.to_nat (bv_unsigned rv)
               = ard_count cnt off0 (length bs)⌝
             ∗ ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                  gb j = bs !!! (off0 + j)%nat⌝)
             ∨ file_taint c))%I).
  Proof using .
    intros Heq Ha0 Hahi Hfdlt.
    iIntros "#Hoff #Hcode #Hm #Hinv".
    iApply (UkCat.kcat_r_mono_out N (mword_of_int (Z.of_nat fd)) a cnt
              _ _ _ with "[] []"); last first.
    { iApply (kcat_r_of_deed a cnt fd wb i γo c r q jc bs Heq Ha0 Hahi Hfdlt
                with "Hcode Hm Hinv"). }
    iIntros (rv gb) "[$ [Hok | HT]]"; [| by iRight ].
    iDestruct "Hok" as (off) "[%Hc %Hb]".
    iDestruct ("Hoff" $! rv gb off with "[%] [%]") as %Hoe;
      [ exact Hc | exact Hb | ].
    iLeft. rewrite <- Hoe. iPureIntro. exact (conj Hc Hb).
  Qed.


  (* =================================================================== *)
  (* open @0x3ec AT THE DEED (lane CAT-WALK-2, K2).                      *)
  (*                                                                     *)
  (* [UkCat.wp_kcat_open]'s three instructions, with the ecall taken at   *)
  (* the DATA-IMAGE deed leaf -- which is the whole reason lane CAT-WALK  *)
  (* could not write this: cat's path argument is [argv[1]], a run of     *)
  (* [ubyteq γd DfracDiscarded] bytes the exec crossing copied onto its   *)
  (* stack, and the landed open leaf read its caller's image off the TEXT *)
  (* half.  [UkFileOpen.wp_uk_ecall_open_read_deed_d] is that leaf at the *)
  (* data image; nothing else about the walk changes.                    *)
  (*                                                                     *)
  (* THE LEDGER STAYS AS [ualloc].  [wp_kcat_open] splits it into         *)
  (* [ustd ∗ ufd] with [ualloc_hi] because the free leaf's caller has     *)
  (* [fd_lowest_closed l = None] in hand; the deed arm hands the whole    *)
  (* allocation out and lets the payer decide, which is what a round that *)
  (* wants the descriptor's TYPE (an inode on the deed's own inum, hence  *)
  (* not a pipe, hence [UkCat.kcat_cldep_nopipe]) needs.                *)
  (* =================================================================== *)
  Lemma wp_kcat_open_read_deed (h : CpuId) (m : regfile) (l : list fdstate)
      (avail : nat) (c : file_fixed) (r : file_names) (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = (mword_of_int 0 : mword 64) ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    cat_code γt -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq γd DfracDiscarded a b) -∗
    app_inv fsc_fs -∗
    urun N h m (mword_of_int CatSyms.open) avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd γfd l -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    (∀ (h' : CpuId) (ret : mword 64),
       UserCwd.ucwd (ukn_cwd N) cw -∗
       ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l)
        ∨ (∃ (fd : nat) (γo : gname),
             ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc γfd l fd (FdOpen true false (FdInode i γo OffParked)) ∗
             fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        ∨ (ustd_any γfd ∗ file_taint c)) -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hpath Ha0 Ha1 Hel Hst.
    iIntros "#Hcode #Hdi #Hinv Hrun Hcwd Hstd Hd1 Hd2 Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hopen & _ & _).
    rewrite Hopen.
    (* ---- 0x3ec  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ec)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3ec with "Hcode"). }
    assert (E0open : add_vec_int (mword_of_int 0x3ec : mword 64) 2
                   = mword_of_int 0x3ee)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emopen : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 15 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0open Emopen.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    (* the two argument words survive the [c.li], and the MODE is 0: so
       the create and truncate bits are clear and the stored pair is
       read-only ([SysOpenDefs.om_rdonly_modes]'s two readings, closed) *)
    assert (Ha0r : m1 !!! Regidx a0_idx = pv).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcr : om_create (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Htr : om_trunc (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hrd : om_readable (m1 !!! Regidx a1_idx) = true)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hwr : om_writable (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hnum : usysno m1 = USYS_open).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int 0x3ee : mword 64) 4))
                     2 = true)
      by (vm_compute; reflexivity).
    (* ---- 0x3ee  ecall -- THE DEED'S OWN LEAF, AT THE DATA IMAGE ---- *)
    iDestruct (uis_cat_3ee with "Hcode") as "#Hi3ee".
    (* the hoist again: the Coq application first, the spec list after *)
    iPoseProof (wp_uk_ecall_open_read_deed_d N h1 m1 (mword_of_int 0x3ee) l
                  avail c r q1 q2 i bs cw Img pv pl Heq Hnum Hal4 Hpath
                  Ha0r Hcr Htr Hel Hst)
      as "Hleaf".
    iApply ("Hleaf" with "Hi3ee Hdi Hrun Hcwd Hstd Hinv Hd1 Hd2").
    assert (E1open : add_vec_int (mword_of_int 0x3ee : mword 64) 4
                   = mword_of_int 0x3f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1open.
    iIntros (h2 ret) "Hans Hcwd Hrun".
    iEval (rewrite Hrd Hwr) in "Hans".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f2  c.jr ra ---- *)
    assert (Hraopen : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraopen; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3f2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hcwd Hans Hrun").
  Qed.

  (* ...AND AT AN ABSENT DEED: the `cat: cannot open f` branch, as a
     theorem.  There is no descriptor arm at all -- the success fold
     collapses at [s = None] -- and the fraction comes home. *)
  Lemma wp_kcat_open_miss_deed (h : CpuId) (m : regfile) (l : list fdstate)
      (avail : nat) (c : file_fixed) (r : file_names) (q : Qp) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = (mword_of_int 0 : mword 64) ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    cat_code γt -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq γd DfracDiscarded a b) -∗
    app_inv fsc_fs -∗
    urun N h m (mword_of_int CatSyms.open) avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd γfd l -∗
    fdq r q None -∗
    (∀ (h' : CpuId) (ret : mword 64),
       UserCwd.ucwd (ukn_cwd N) cw -∗
       ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l ∗ fdq r q None)
        ∨ (ustd_any γfd ∗ file_taint c)) -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hpath Ha0 Ha1 Hel Hst.
    iIntros "#Hcode #Hdi #Hinv Hrun Hcwd Hstd Hd Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hopen & _ & _).
    rewrite Hopen.
    iApply (wp_uk_cli N h m (mword_of_int 0x3ec)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3ec with "Hcode"). }
    assert (E0open : add_vec_int (mword_of_int 0x3ec : mword 64) 2
                   = mword_of_int 0x3ee)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emopen : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 15 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0open Emopen.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0r : m1 !!! Regidx a0_idx = pv).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcr : om_create (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Htr : om_trunc (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hnum : usysno m1 = USYS_open).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int 0x3ee : mword 64) 4))
                     2 = true)
      by (vm_compute; reflexivity).
    iDestruct (uis_cat_3ee with "Hcode") as "#Hi3ee".
    iPoseProof (wp_uk_ecall_open_miss_deed_d N h1 m1 (mword_of_int 0x3ee) l
                  avail c r q cw Img pv pl Heq Hnum Hal4 Hpath
                  Ha0r Hcr Htr Hel Hst)
      as "Hleaf".
    iApply ("Hleaf" with "Hi3ee Hdi Hrun Hcwd Hstd Hinv Hd").
    assert (E1open : add_vec_int (mword_of_int 0x3ee : mword 64) 4
                   = mword_of_int 0x3f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1open.
    iIntros (h2 ret) "Hans Hcwd Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hraopen : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraopen; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3f2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hcwd Hans Hrun").
  Qed.

  (* =================================================================== *)
  (*  ...AND THE OBLIGATIONS AT THEM.                                     *)
  (*                                                                     *)
  (*  [UkCat.kcat_o_of_law]'s twins.  The ledger and the working          *)
  (*  directory ride in the obligation's two halves (both are linear:     *)
  (*  main's loop opens once per argument), the persistent application    *)
  (*  invariant and code stay outside, and what the PRESENT arm hands     *)
  (*  back is [ualloc] on the deed's own inum -- which is the whole       *)
  (*  point, because a descriptor whose type is [FdInode i γo _] is not   *)
  (*  a pipe and cat's close is then FREE ([UkCat.kcat_cldep_nopipe]).   *)
  (*  The ABSENT arm hands the ledger back UNTOUCHED at [-1], which is    *)
  (*  what the `cat: cannot open f` turn spends.                         *)
  (* =================================================================== *)
  Definition kcat_open_hold (l : list fdstate) (cw : Z) : iProp Σ :=
    (ustd γfd l ∗ UserCwd.ucwd (ukn_cwd N) cw)%I.

  Lemma kcat_o_of_deed (l : list fdstate) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8)) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    cat_code γt -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq γd DfracDiscarded a b) -∗
    app_inv fsc_fs -∗
    UkCat.kcat_o N pv
      (kcat_open_hold l cw
       ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
      (fun ret : mword 64 =>
         (UserCwd.ucwd (ukn_cwd N) cw
          ∗ ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l)
             ∨ (∃ (fd : nat) (γo : gname),
                  ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
                   /\ (fd < NOFILE)%nat⌝ ∗
                  ualloc γfd l fd
                    (FdOpen true false (FdInode i γo OffParked)) ∗
                  fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
             ∨ (ustd_any γfd ∗ file_taint c)))%I).
  Proof using .
    intros Heq Hpath Hel Hst.
    iIntros "#Hcode #Hdi #Hinv" (h m avail) "%Ha0 %Ha1 _ Hhold Hrun Hcont".
    iDestruct "Hhold" as "[[Hstd Hcwd] [Hd1 Hd2]]".
    iApply (wp_kcat_open_read_deed h m l avail c r q1 q2 i bs cw Img pv pl
              Heq Hpath Ha0 Ha1 Hel Hst
              with "Hcode Hdi Hinv Hrun Hcwd Hstd Hd1 Hd2").
    iIntros (h' ret) "Hcwd Hans Hrun".
    iApply ("Hcont" $! h' ret with "[Hcwd Hans] Hrun"). iFrame "Hcwd Hans".
  Qed.

  Lemma kcat_o_of_deed_miss (l : list fdstate) (c : file_fixed)
      (r : file_names) (q : Qp) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    cat_code γt -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq γd DfracDiscarded a b) -∗
    app_inv fsc_fs -∗
    UkCat.kcat_o N pv
      (kcat_open_hold l cw ∗ fdq r q None)
      (fun ret : mword 64 =>
         (UserCwd.ucwd (ukn_cwd N) cw
          ∗ ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l
              ∗ fdq r q None)
             ∨ (ustd_any γfd ∗ file_taint c)))%I).
  Proof using .
    intros Heq Hpath Hel Hst.
    iIntros "#Hcode #Hdi #Hinv" (h m avail) "%Ha0 %Ha1 _ Hhold Hrun Hcont".
    iDestruct "Hhold" as "[[Hstd Hcwd] Hd]".
    iApply (wp_kcat_open_miss_deed h m l avail c r q cw Img pv pl
              Heq Hpath Ha0 Ha1 Hel Hst
              with "Hcode Hdi Hinv Hrun Hcwd Hstd Hd").
    iIntros (h' ret) "Hcwd Hans Hrun".
    iApply ("Hcont" $! h' ret with "[Hcwd Hans] Hrun"). iFrame "Hcwd Hans".
  Qed.


End UkCatDeed.
