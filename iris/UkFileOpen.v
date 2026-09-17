(* ===================================================================== *)
(* UkFileOpen.v -- THE FILE APPLICATION'S U-TIER COROLLARIES (lane       *)
(* F-OPEN-2, deliverable 3).                                             *)
(*                                                                       *)
(* [UkTreeRead.v] is the mould at the TREE claim's frozen pin and         *)
(* [UkTreeCreate.v] at its owner's move; this file is the two of them at  *)
(* [AppFile]'s DEED, through [FileOpen.v]'s suppliers.  Nothing here      *)
(* opens a kernel invariant or holds a kernel ghost: every lemma is a     *)
(* landed U-tier leaf plus one of [FileOpen]'s bundles and one of its     *)
(* receipt readers.                                                      *)
(*                                                                       *)
(*   [wp_uk_ecall_open_read_deed]   open(`f`, O_RDONLY) at a PRESENT      *)
(*        deed: the descriptor that comes back is on the deed's OWN INUM  *)
(*        and BOTH fractions come home.  [FileOpen.file_open_plain_au] /  *)
(*        [file_open_recv_file].                                         *)
(*   [wp_uk_ecall_open_miss_deed]   the same call at an ABSENT deed: the  *)
(*        call returns -1, the ledger is untouched, and the fraction      *)
(*        comes home ([FileOpen.file_open_miss_au] / [_recv], lane        *)
(*        F-OPEN-2's seam 2).                                            *)
(*   [wp_uk_read_deed_learns]       read at that descriptor: what lands   *)
(*        in the buffer are EXACTLY the bytes the deed records.           *)
(*        [FileOpen.file_read_piece] / [file_read_arms_learn].            *)
(*                                                                       *)
(* THE LEAF IS A VISIBLE PARAMETER, deliberately.  Every corollary here   *)
(* is stated over [UkRunSys.wp_uk_ecall_open_recv_img] /                  *)
(* [UkReadFile.wp_uk_ecall_read_file], the PARKED-offset members; lane    *)
(* OFF-HAND's held-offset twins ([wp_uk_ecall_open_recv_img_held],        *)
(* [_read_file_held]) are the same statements with the leaf swapped and   *)
(* [UserOff.uoff] added to the post, so each corollary below is           *)
(* re-instantiated by changing exactly one application.                   *)
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
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserCwd.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import UmodeArith.         (* [moi_small] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.
Require Import UkReadRows.
Require Import UkReadFile.
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import UConsOpen.          (* [xfam_open] and the ledger arms *)
Require Import UkTreeRead.         (* [tree_open_fd_tie]: the ledger/receipt tie *)
Require Import SpecFileread.
Require Import SpecSysRead.
Require Import SysReadDefs.
Require Import SysOpenDefs.
Require Import SpecSysOpen.
Require Import ArgPath.
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import PathElems.
Require Import FsTree.
Require Import FsImgCheck.         (* [fname_f] *)
Require Import InodeInv.
Require Import BioDefs.
Require Import FsAbsReadFire.
Require Import FsAbsEra.
Require Import PinnedObs.
Require Import ConsoleInv.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FileDeltas.
Require Import FileOpen.
Require Import FsImg.              (* re-IMPORTED late, as FileOpen does *)
Require Import FsAbsDefs.
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

Section UkFileOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  open(`f`, O_RDONLY) AT A PRESENT DEED                           *)
  (* =================================================================== *)

  Definition file_open_fam (c : file_fixed) (r : file_names) (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (Q : Z -> iProp Σ) : sfam :=
    xfam_open
      (pobs_P_lin (file_taint c) [ROOTINO; i] (fdq r q1 (Some (i, bs))))
      (pobs_Pmiss (file_taint c))
      (file_open_recv c r q2 (Some (i, bs))) Q.

  Lemma file_open_sup (N : uk_names Σ) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    udepwf_at N m pc USYS_open (file_open_fam c r q1 q2 i bs (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hinv #Hro Hd1 Hd2".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_open_fam c r q1 q2 i bs (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    rewrite /open_in Hcr.
    iApply (file_open_plain_au fsc_fs c r q1 q2 i bs cw M pv
              (m !!! Regidx a1_idx) pl _ Heq (Hpath M Hsro) Hel Hst Htr
              with "Hinv Hd1 Hd2").
  Qed.

  (* ---- THE COROLLARY: "open `f` and the handle is on the inum MY DEED
     names, with both fractions back".  Three arms and no fourth. *)
  Lemma wp_uk_ecall_open_read_deed (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched, and so are both
           fractions *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l)
        (* ...OR THE HANDLE, ON THE DEED'S OWN INUM *)
        ∨ (∃ (fd : nat) (γo : gname),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx))
                       (FdInode i γo OffParked)) ∗
             fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...or the application is tainted, and SOME ledger comes back *)
        ∨ (ustd_any (ukn_fd N) ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv Hd1 Hd2 Hcont".
    iDestruct (file_open_sup N c r q1 q2 i bs Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Htr Hel Hst with "Hinv Hro Hd1 Hd2") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (file_open_fam c r q1 q2 i bs (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_open_fam c r q1 q2 i bs (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iDestruct (file_open_recv_file fsc_fs c r q1 q2 i bs cw (uvis_M W) pv
                 (m !!! Regidx a1_idx) pl _ (uvis_fd W) rv fdv'
                 (Hpath (uvis_M W) Himg) Hel Hst with "Hrc") as "Hans".
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[%Hr %Hfdv] | [Hok | #HT]]"; last first.
    { iRight. iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd". }
    - iDestruct "Hok" as (γo) "(%Hrcpt & Hd1 & Hd2)".
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        destruct Hrcpt as (fd0 & Hr0 & Hcl0 & _).
        assert (Hlt0 : (fd0 < NOFILE)%nat).
        { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr ty) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1).
      rewrite (tree_open_fd_tie l (uvis_fd W) fdv' rv
                 (om_readable (m !!! Regidx a1_idx))
                 (om_writable (m !!! Regidx a1_idx)) i γo fd rd wr ty
                 Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
      iRight. iLeft. iExists fd, γo. iFrame "Hal Hd1 Hd2". iPureIntro.
      exact (conj Hr1 Hlt1).
    - iLeft. iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  2.  open(`f`, O_RDONLY) AT AN ABSENT DEED                           *)
  (*                                                                      *)
  (*  cat's `cannot open` branch, as a THEOREM: at [s = None] the walk     *)
  (*  misses and the success fold collapses, so there is no descriptor     *)
  (*  arm at all -- and (lane F-OPEN-2's seam 2) the fraction the walk was *)
  (*  paid with comes home.                                               *)
  (* =================================================================== *)

  Definition file_miss_fam (c : file_fixed) (r : file_names) (q : Qp)
      (Q : Z -> iProp Σ) : sfam :=
    xfam_open
      (pobs_P_dead_lin (file_taint c) (fdq r q None) ROOTINO)
      (pobs_Pmiss_ref (file_taint c) (fdq r q None))
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Q.

  Lemma file_miss_sup (N : uk_names Σ) (c : file_fixed) (r : file_names)
      (q : Qp) (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile)
      (pc : mword 64) (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗
    fdq r q None -∗
    udepwf_at N m pc USYS_open (file_miss_fam c r q (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Htr Hel Hst. iIntros "#Hinv #Hro Hd".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_miss_fam c r q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_miss_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (file_open_miss_au fsc_fs c r q cw M pv (m !!! Regidx a1_idx) pl
              _ _ _ _ _ Heq (Hpath M Hsro) Hel Hst Hcr Htr with "Hinv Hd").
  Qed.

  Lemma wp_uk_ecall_open_miss_deed (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q None -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q None)
        ∨ (ustd_any (ukn_fd N) ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv Hd Hcont".
    iDestruct (file_miss_sup N c r q Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Htr Hel Hst with "Hinv Hro Hd") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (file_miss_fam c r q (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_miss_fam c r q (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_miss_fam xfam_open of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_miss_recv fsc_fs c r q cw (uvis_M W) pv
            (m !!! Regidx a1_idx) pl _ _ (uvis_fd W) rv fdv'
            (Hpath (uvis_M W) Himg) Hel with "Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hd) | #HT]".
    - iLeft. iFrame "Hd". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  3.  read AT THAT DESCRIPTOR: the bytes ARE the deed's               *)
  (* =================================================================== *)

  Lemma wp_uk_read_deed_learns (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jc : Z)
      (bs : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for reading on the deed's own inode" *)
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    (* THE DEED, at a fraction, and the console flag the claim's legs read *)
    cons_made (fn_cons r) jc -∗
    app_inv fsc_fs -∗
    fdq r q (Some (i, bs)) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       (((⌜rv = (mword_of_int (-1) : mword 64)⌝
          ∨ (∃ off : nat,
               ⌜Z.to_nat (bv_unsigned rv)
                = ard_count (Z.to_nat cnt) off (length bs)⌝ ∗
               ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                  gb j = bs !!! (off + j)%nat⌝))
         ∗ fdq r q (Some (i, bs)))
        ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k gb -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hcnt Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh #Hm #Hinv Hd Hbuf Hcont".
    iDestruct (file_read_piece fsc_fs c r q jc (Some (i, bs)) i γo Heq
                 with "Hinv Hm Hd") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo
                 (file_read_recv c r q jc (Some (i, bs))) with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N)
                 (file_read_recv c r q jc (Some (i, bs)))) fd
              (FdOpen true wb (FdInode i γo OffParked))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' rv dd gb W M' fdv' cw' cs')
      "%Hdd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N)
                    (file_read_recv c r q jc (Some (i, bs)))) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 rv M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(_ & _ & _ & Hcore)".
    rewrite Hkey.
    rewrite /fileread_extra_core /=.
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (file_read_arms_learn c r q jc i bs γo cnt rv M'
                 (m !!! Regidx a1_idx) k gb Hlin Himg ltac:(lia)
                 with "Hcore") as "Hlearn".
    iApply ("Hcont" $! h' rv gb with "Hufdh Hlearn Hrun Hbuf").
  Qed.

End UkFileOpen.
