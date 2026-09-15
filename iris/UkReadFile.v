(* ===================================================================== *)
(* UkReadFile.v -- THE FILE ARM OF THE GENERIC READ LEAF.                  *)
(*                                                                        *)
(* design/user-read.md section 3 is one leaf whose ARM is chosen by the    *)
(* caller's own descriptor knowledge and whose CONTENT post comes from the *)
(* kernel's AU spec at every arm.  [UkRunSys.wp_uk_ecall_read_recv] built  *)
(* the mechanism -- the window walk with the kernel's [spost_at] KEPT --   *)
(* and cut its CONSOLE member; this file cuts the INODE member out of the  *)
(* same walk.  What is shared is everything that made the receipt          *)
(* READABLE, and section 5 is right that it is arm-independent: the        *)
(* resume-image bytes, the destination's linearity, the writable-mapped    *)
(* row, the three trapframe-argument ties, the lazy bit and the live row   *)
(* are copied here unchanged.                                             *)
(*                                                                        *)
(* WHAT IS DIFFERENT IS THE DEPOSIT, and only the deposit.  A console read *)
(* is about a STANDARD stream, so [UkRun.udepwf_std] fixes the low [NSTD]  *)
(* slots and the leaf reads the arm off the caller's LEDGER.  A file read  *)
(* is about a descriptor the program OPENED, which is never a standard     *)
(* stream ([UserFd.ufd] carries [NSTD <= fd]), so the ledger says nothing  *)
(* about it: what fixes the arm here is the caller's own HANDLE, and the   *)
(* deposit is fixed at the STATE that handle names ([udepwf_st] below).    *)
(* That is section 3's [udepwf_at (kind)], at the one name still free --   *)
(* [UkRun.udepwf_at] is the CWD-fixed form and [udepwf_std] the            *)
(* ledger-fixed one, so this is the STATE-fixed third.                     *)
(*                                                                        *)
(* THE OFFSET IS REPORTED, NOT OWNED -- design/user-read.md section 3's    *)
(* R-c.  The RULED mode-in-state (a descriptor that records parked vs      *)
(* held) is not implementable without a parked-table discipline through    *)
(* the generic-safety tier; that finding, and the three routes out, are    *)
(* written up in that section's RD-2 AS-LANDED block.  What survives it    *)
(* untouched is the CONTENT row, because [FsAbsReadFire.read_post_ok]      *)
(* already names the offset EXISTENTIALLY and ties everything else to it:  *)
(*                                                                        *)
(*    exists av off a d,  ard_pre av i off a  /\  0 <= n                   *)
(*                     /\  ard_ret_tie n a off r                           *)
(*                     /\  Z.of_nat d = bv_unsigned r                      *)
(*                     /\  (on an AFile row) the d bytes at the            *)
(*                         destination ARE bs[off .. off+d)                *)
(*                     /\  the caller's own receipt at (av, off, a, d)     *)
(*                                                                        *)
(* So a program that pins its file learns exactly what it read, at a       *)
(* position the call TELLS it rather than one it predicted.  When R-a      *)
(* lands, this leaf's statement gains the [uoff] conjuncts and LOSES the   *)
(* [off] existential; nothing else about it moves.                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
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
Require Import UserPerm.           (* [perm_of] / [lazy_free] *)
Require Import ProcPtOwn.          (* [uptd] / [ud_um] / [proc_pt_wf] *)
Require Import UserPtTree.         (* [uva_wmapped] / [umem_write] *)
Require Import UserBits.           (* [uint_add_vec_int_small] -- no-wrap *)
Require Import UmodeArith.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import VcGen.              (* [trunc32] *)
Require Import PieceFam.           (* [pfam] / [pf_at] / [pfam_triv] *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkStep.             (* [wp_uk_ecall] / [uvb_x0] -- the walk *)
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6], [xfam] *)
Require Import SpecArgfd.          (* [fd_st_of_key] *)
Require Import SpecFileread.       (* [fileread_in] / [fileread_extra_core] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppInv.             (* [appE] -- the commit mask *)
Require Import BioDefs.            (* [BSIZE] *)
Require Import InodeInv.           (* [MAXFILE] -- the row size cap *)
Require Import SysReadDefs.        (* [ard_count] / [ard_pre] *)
Require Import FsAbsDefs.          (* [aview] / [anode] / [abs_row] *)
Require Import FsBytesGamma.       (* [fs_gamma_L] *)
Require Import FsAbsReadFire.      (* [aread_commit_at] / [read_arms] *)
Require Import FsAbs.              (* [nview] -- LAST (FsAbs's own rule) *)
Require Import FsCfg.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UkReadFile.
  (* [UShLine]'s binder list, minus the echo application's own cameras:
     nothing here is about an application, which is the point. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* [UexecExecInst.xfam] at the ONE field the inode arm's rows look at
     ([rf_F], the observation receipt), and the trivial ones everywhere
     else: a deposit is read at one number, so the rest of the record is
     inert.  [UShLine.xfam_rd] is the mold and this is it with [rf_F]
     real instead of trivial -- the console member names [rf_ret] /
     [rf_in] and leaves [rf_F] at the unit, the inode member does the
     reverse, and that difference IS the arm. *)
  Definition xfam_rdf (Q : Z -> iProp Σ)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := F;
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := fun _ _ => True%I;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       wf_Q     := fun _ => True%I;
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       kf_lend  := emp%I;
       kf_xpay  := Q;
       rf_ret   := fun _ _ => True%I;
       rf_in    := fun _ => True%I |}.

  (* AT THE CLASS'S OWN FAMILY TYPE ([UShLine.ush_read_fam_at]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument
     is checked before the instance evar is resolved and so does not
     convert. *)
  Definition read_file_fam (Q : Z -> iProp Σ)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) : sfam :=
    xfam_rdf Q F.

  (* =================================================================== *)
  (*  2.  THE STATE-FIXED DEPOSIT                                          *)
  (* =================================================================== *)
  (* [UkRun.udepwf_std]'s third sibling.  Its header's argument, one arm
     over: row 5's bundle is [SpecFileread.fileread_in] at
     [SpecArgfd.fd_st_of_key (xk_a W 0) (uvis_fd W)], so which ARM the
     supplier must answer is decided by the KEY's own descriptor table --
     and a supplier holding an observation commit at inode [i] and
     offset-shadow [γo] answers the INODE arm at THAT file and no other.
     [udepwf]'s own forall binds [fdv], so it cannot be told; the leaf,
     which has destructed [urun] and holds both the authority and the
     caller's HANDLE, can ([UserFd.ufd_agree]), and that is why the fact
     enters as a premise INSIDE the forall here.

     THE CWD IS STILL forall-BOUND, as in the ledger-fixed form: a read's
     bundle reads no path. *)
  Definition udepwf_st (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (st : fdstate) : iProp Σ :=
    (⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
       (pidv : mword 32),
       ⌜fd_st_of_key (m !!! Regidx a0_idx) fdv = st⌝ -∗
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep
         (uvis_of_run m pc M pm sz fdv cw gn cs pidv false))%I.

  (* =================================================================== *)
  (*  3.  THE TWO KEY-LEVEL ROWS, IN THE PROCESS'S DIRECTION               *)
  (* =================================================================== *)
  (* [UShLine]'s pair, at the state-fixed reading.  They are restated
     rather than imported because [UShLine.v] sits ABOVE this file (it is
     the echo application's own line lemma) and its copies are proved at
     the console arm's spelling; the proofs are three lines each. *)
  Local Ltac xv6_skip :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [Hc | _]; [ exfalso; by vm_compute in Hc | ]
    end.
  Local Ltac xv6_take :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [_ | Hc]; [ | exfalso; by apply Hc ]
    end.

  Lemma sbundle_at_read_intro_st (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 : mword 64) (sts : list fdstate) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 -> uvis_fd W = sts ->
    fileread_in (fd_st_of_key v0 sts) (rf_F f) (rf_ret f) (rf_in f) True%I -∗
    sbundle_at X USYS_read f W.
  Proof.
    intros H0 Hfd. iIntros "H".
    rewrite -H0 -Hfd.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_read_elim_st (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v1 v2 : mword 64) (sts : list fdstate)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = v1 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    spost_at X USYS_read f W r M' fdv' cw' cs' -∗
    ⌜fileread_ret (sys_rw_count v2) r⌝ ∗
    ∃ P : uptd,
      ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
      ⌜proc_pt_wf P⌝ ∗
      ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
      fileread_extra_core (uvis_gen W) P (fd_st_of_key v0 sts) (sys_rw_count v2)
        (rf_F f) (rf_ret f) (rf_in f) r M' v1.
  Proof.
    intros H0 H1 H2 Hfd. iIntros "H".
    rewrite -H0 -H1 -H2 -Hfd.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_take. iExact "H".
  Qed.

  (* THE DESCRIPTOR THE CALL WILL RUN ON, OUT OF THE CALLER'S OWN HANDLE.
     The console twin ([UShLine.ush_fd_st_console]) reads it out of the
     LEDGER, which can only speak of the low [NSTD] slots; a file
     descriptor is never one of those ([UserFd.ufd] carries the bound), so
     this is the same step at the handle instead. *)
  Lemma ufd_st_of_key (v0 : mword 64) (fdv : list fdstate) (fd : nat)
      (st : fdstate) :
    bv_signed (trunc32 v0) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    fdv !! fd = Some st ->
    fd_st_of_key v0 fdv = st.
  Proof.
    intros H0 Hlt Hlk. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat fd < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; lia ].
    rewrite Nat2Z.id Hlk. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  4.  THE LEAF                                                        *)
  (* =================================================================== *)
  (* [UkRunSys.wp_uk_ecall_read_recv]'s walk, at the FILE arm.  Every
     bridge row below is that leaf's, unchanged -- section 5's "the rows
     the recv leaf hands out are ARM-INDEPENDENT" is literally true, and
     this is the check of it.  The three differences are all in the
     descriptor:

       - the DEPOSIT is fixed at the STATE the caller's handle names
         ([udepwf_st]) rather than at the low [NSTD] ledger, because an
         opened file is never a standard stream;
       - what goes down and comes back is [UserFd.ufd] (one handle), not
         [UserFd.ustd] (the whole ledger);
       - what the caller is TOLD about the key is the arm itself --
         [fd_st_of_key (a0) (uvis_fd W) = st] -- which is what makes the
         post's inode arm readable: without it, row 5's receipt is about
         a descriptor the caller cannot identify with its own.

     A program spends this leaf's post through [spost_at_read_elim_st]
     above and lands in [SpecFileread.fileread_extra_core] at its own
     [st]; at [FdOpen true _ (FdInode i γo)] that IS
     [FsAbsReadFire.read_arms], and section 3's whole File row is inside
     it. *)
  Lemma wp_uk_ecall_read_file (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8)
      (avail : nat) (fdep : sfam) (fd : nat) (st : fdstate) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    (* THE DESCRIPTOR ARGUMENT IS THE ONE THE HANDLE NAMES.  a0 carries it
       as a C [int], so the reading is the signed low word -- the same one
       [SpecArgfd.fd_st_of_key] takes. *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_st N m pc USYS_read fdep st -∗
    UserFd.ufd (ukn_fd N) fd st -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (W : uvis) (M' : gmap Z (bv 8))
       (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       (* the destination run is linear, and the resume image holds the
          bytes -- the two rows that turn a receipt stated at [M'] into a
          fact about the buffer the program owns at a source function *)
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat i))
           = (uint (m !!! Regidx a1_idx) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (g j) ⌝ -∗
       (* ...and every byte of it is writable-mapped in any table the
          key's projection admits *)
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < k)%nat ->
           UserPtTree.uva_wmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       (* the trapping key's three argument words are the caller's own *)
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       (* ...AND THE ARM IS THE ONE THE HANDLE NAMES.  The console leaf's
          [take NSTD (uvis_fd W) = l], at a descriptor no ledger can
          reach. *)
       ⌜fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) = st⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜uexec_live_ok USYS_read (uvis_tf W) (uvis_fd W) r cs'⌝ -∗
       (* the handle comes straight back: read moves no descriptor *)
       UserFd.ufd (ukn_fd N) fd st -∗
       (* THE POST, AT THE TRAPPING KEY AND THE RESUME IMAGE *)
       spost_at uslot USYS_read fdep W r M' fdv' cw' cs' -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hcnt Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hsb Hufdh Hbuf Hcont".
    set (dst := m !!! Regidx a1_idx : mword 64).
    set (cap := Z.to_nat cnt).
    assert (Hwin : usyswin m USYS_read = Some (dst, cap)).
    { unfold usyswin.
      destruct (decide (USYS_read = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_read)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      rewrite Hcnt. reflexivity. }
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & Hb)".
    (* THE KEY'S ARM IS THE CALLER'S OWN HANDLE, which is both what the
       deposit is stated at and what makes row 5's arm readable *)
    iDestruct (ufd_agree (ukn_fd N) fdv fd st with "Hufd Hufdh") as %Hlk.
    assert (Hkey : fd_st_of_key (m !!! Regidx a0_idx) fdv = st)
      by exact (ufd_st_of_key _ fdv fd st Hfdv Hfdlt Hlk).
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs pidv with "[%] Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)"; [ exact Hkey | ].
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* THE NO-WRAP FACT, off the ownership rather than off a premise *)
    iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < k)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    iDestruct (uheap_ubytes_w (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hwacc.
    assert (Hnf : forall (P : uptd) (j : nat),
              ProcPtOwn.proc_pt_wf P -> perm_of (ud_um P) sz = pm ->
              lazy_free (ud_um P) sz -> (j < k)%nat ->
              UserPtTree.uva_wmapped P (uint (add_vec_int dst (Z.of_nat j)))).
    { intros P j Hwf Hpmp Hlf Hjk.
      rewrite (Hlin j Hjk).
      destruct (Hbnd j Hjk) as [_ Hrange].
      apply (UserHeap.lazy_free_uw_addr P sz (uint dst + Z.of_nat j)%Z Hwf Hlf);
        [ exact Hrange | rewrite Hpmp; exact (Hwacc j Hjk) ]. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)) = USYS_read).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    assert (Hw : usys_win USYS_read (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false))
                 = Some (dst, cap)).
    { cbn [uvis_tf uvis_of_run]. rewrite usyswin_tf_of. exact Hwin. }
    rewrite /uexec_pay_dep /upay_at.
    rewrite Hnum. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_read = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_wait)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_window USYS_read _ r _ _ _ _ _ _ _ _ dst cap Hw Hok)
      as ((d & bs & Hdcap & HM') & -> & ->).
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run] in HM' |- *.
    assert (Hg : exists g : nat -> bv 8,
              (forall j : nat, (j < d)%nat -> g j = bs j) /\
              (forall j : nat, (d <= j)%nat -> g j = f j)).
    { exists (fun j => if decide (j < d)%nat then bs j else f j).
      split; intros j Hj; case_decide as Hc;
        [ reflexivity | exfalso; lia | exfalso; lia | reflexivity ]. }
    destruct Hg as (g & Hgb & Hgf).
    assert (Hdk : (d <= k)%nat) by (unfold cap in Hdcap; lia).
    rewrite (umem_wr_ext M dst d bs g
               ltac:(intros i Hi; symmetry; exact (Hgb i Hi))) in HM'.
    rewrite (umem_wr_write M dst d g
               ltac:(intros i Hi; apply Hlin; lia)) in HM'.
    subst M'.
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) d g) pm pm sz sz
               fdv fdv cw cw' gn gn cs cs pidv false false r Hx0 Hal4).
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' %Hlzf' Hb'".
    iEval (rewrite (ubytes_split (ukn_d N) (uint dst) d k f Hdk)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (uint dst) d f g with "Hheap Hblo")
      as "[Hheap Hblo]".
    iDestruct (ubytes_ext (ukn_d N) (uint dst + Z.of_nat d) (k - d)
                 (fun j => f (d + j)%nat) (fun j => g (d + j)%nat)
                 ltac:(intros j _; symmetry; apply Hgf; lia) with "Hbhi")
      as "Hbhi".
    iAssert (ubytes (ukn_d N) (uint dst) k g) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split (ukn_d N) (uint dst) d k g Hdk). iFrame "Hblo Hbhi". }
    iDestruct (urun_close_upd N (umem_write M (uint dst) d g) pm m
                 (mword_of_int 10) r sz fdv cw' gn cs pidv (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep [Hcont Hbuf Hufdh Hpost]") as "Hkc".
    { iIntros (h'') "Hrun".
      iApply ("Hcont" $! h'' r d g (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
                _ _ _ _
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hufdh Hpost Hrun Hbuf").
      - exact Hdcap.
      - intros j Hj. apply Hgf; lia.
      - exact Hlin.
      - intros j Hj. rewrite (Hlin j Hj).
        destruct (decide (j < d)%nat) as [Hjd | Hjd].
        + exact (umem_write_lookup_in M (uint dst) d g j Hjd).
        + rewrite (umem_write_lookup_out M (uint dst) d g
                     (uint dst + Z.of_nat j)%Z
                     ltac:(intros i Hi; lia)).
          destruct (Hbnd j Hj) as [HMj _]. rewrite HMj.
          rewrite (Hgf j ltac:(lia)). reflexivity.
      - intros P j Hwf Hpmp Hlf Hjk.
        cbn [uvis_sz uvis_perm uvis_of_run] in Hpmp, Hlf.
        exact (Hnf P j Hwf Hpmp Hlf Hjk).
      - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc).
      - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc).
      - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc).
      - rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false). exact Hkey.
      - reflexivity.
      - exact Hliverow. }
    iDestruct (ukcq_ukc with "Hkc") as "Hkc".
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb'");
      [ exact Hlo' | exact Hpm' | exact Hlzf' ].
  Qed.

  (* =================================================================== *)
  (*  5.  THE DEPOSIT'S SUPPLIER: ONE OBSERVATION COMMIT, NOTHING ELSE     *)
  (* =================================================================== *)
  (* What the console arm needs is a LEASE and an input licence; what the
     file arm needs is the commit the kernel's AU spec already takes, and
     nothing at all beside it.  That is the whole content of "the per-arm
     payment is a resource the PROGRAM owns and understands"
     (design/user-read.md section 1): a file read costs its caller the AU
     it chose, and a caller that wants to be told nothing pays
     [FsAbsInvFire.fsabs_aread] from thin air. *)
  Lemma udepwf_st_read_file (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (wb : bool) (i : Z) (γo : gname)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) :
    pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F -∗
    udepwf_st N m pc USYS_read (read_file_fam (ukn_pay N) F)
      (FdOpen true wb (FdInode i γo)).
  Proof.
    iIntros "Hau". rewrite /udepwf_st.
    iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro_st uslot (xfam_rdf (ukn_pay N) F)
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) fdv
              (tf_of_arg0 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)).
    rewrite Hkey. rewrite /fileread_in /=. iIntros "$". iExact "Hau".
  Qed.

  (* =================================================================== *)
  (*  6.  THE FILE ROW, READ OFF THE POST                                 *)
  (* =================================================================== *)
  (* design/user-read.md section 3's Inode arm, assembled: at a PINNED
     file the receipt's own row IS the content post, and the leaf's
     resume-image bridge is what carries it into the buffer the program
     holds.  The disjunction is honest and it is the kernel's, not a
     weakening: readi answers -1 when a copyout faults, and no row above
     rules that out for an INODE descriptor -- [UexecRet.uexec_live_ok]
     refutes -1 only at the console.  A caller that tests [r >= 0], which
     is what cat's loop does, is in the left arm. *)
  Lemma read_arms_file_learn (Γ := fs_gamma_L fsc_fs)
      (i : Z) (γo : gname) (n : Z) (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_arms Γ i γo n
      (MkPfam (fun (av : aview) (_ : nat) (_ : anode) (_ : nat) =>
                 (⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
                  nview Γ q i (MkAnode (AFile bs0) nl))%I)
              (nview Γ q i (MkAnode (AFile bs0) nl)))
      r M' addr -∗
    nview Γ q i (MkAnode (AFile bs0) nl) ∗
    (⌜r = (mword_of_int (-1) : mword 64)⌝
     ∨ (∃ off : nat,
          (* the COUNT: exactly design section 3's [min (cnt, |bs| - off)] *)
          ⌜Z.to_nat (bv_unsigned r)
           = ard_count (Z.to_nat n) off (length bs0)⌝ ∗
          (* ...AND THE BYTES THE PROGRAM HOLDS ARE THE FILE'S *)
          ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
             g j = bs0 !!! (off + j)%nat⌝)).
  Proof.
    intros Hlin Himg Hnk. rewrite /read_arms /read_post_ok /read_post_fail.
    iIntros "[Hok | [%Hm1 Hfail]]".
    - iDestruct "Hok" as (av off a d) "(%Hpre & %Hn & %Htie & %Hdr & %Hbytes & [%Hav Hn2])".
      (* the pin collapses the observed row onto the caller's value *)
      destruct Hpre as (Hrow & _ & Hsz).
      assert (Hab : a = MkAnode (AFile bs0) nl)
        by exact (arow_at_pinned _ _ _ _ Hrow Hav).
      subst a. cbn [an_node] in Htie, Hbytes.
      rewrite /anode_size_ok /= /MAXFILE /BSIZE in Hsz.
      iFrame "Hn2". iRight. iExists off.
      (* the return value IS the clamped count, so [d] is it too.  The
         count fits a 64-bit word because the row's own SIZE CAP is what
         [ard_pre] carries: a file is at most [MAXFILE * BSIZE] bytes, so
         nothing here has to be assumed about how big a file can be. *)
      assert (Hdc : d = ard_count (Z.to_nat n) off (length bs0)).
      { assert (Hbu : bv_unsigned r
                      = Z.of_nat (ard_count (Z.to_nat n) off (length bs0))).
        { rewrite Htie. apply moi_small.
          pose proof (ard_count_sub (Z.to_nat n) off (length bs0)) as Hle.
          unfold Z64. lia. }
        lia. }
      iPureIntro. split.
      { rewrite -Hdr Nat2Z.id. exact Hdc. }
      intros j Hj.
      assert (Hjd : (j < d)%nat) by (rewrite -Hdr Nat2Z.id in Hj; lia).
      (* the delivered run sits inside the one the caller owns, so the
         two pure rows are about the same bytes *)
      assert (Hdk : (d <= k)%nat).
      { pose proof (ard_count_le (Z.to_nat n) off (length bs0)) as Hle. lia. }
      pose proof (Hbytes ltac:(intros i0 Hi0; apply Hlin; lia) j Hjd) as HM.
      pose proof (Himg j ltac:(lia)) as HG.
      rewrite HM in HG. by injection HG.
    - (* the sign guard hands the piece back unfired; the fault arm fires
         at advance 0.  Either way the pin comes home and nothing is
         claimed about the buffer. *)
      iSplitL "Hfail"; [ | iLeft; by iPureIntro ].
      iDestruct "Hfail" as "[[_ Hpf] | [_ Hrec]]".
      + iApply (pf_at_refund with "Hpf").
      + iDestruct "Hrec" as (av off a) "[_ [_ $]]".
  Qed.

  (* =================================================================== *)
  (*  7.  THE CONSUMER TEST -- cat, AT A CONCRETE FILE                     *)
  (* =================================================================== *)
  (* THE TEST THE LANE OWES (design/user-read.md section 3, RD-2's brief
     deliverable 5): a program holding a descriptor on a KNOWN file reads
     and LEARNS the bytes, and it has to fall out of the leaf with no new
     machinery.  It does: the only things this lemma builds are the
     caller's own receipt family (its pin, handed back) and the leaf's
     premises.  The file is a concrete four-byte one, spelled as a list,
     because the point of a test is that nothing about it is general. *)
  Definition cat_file : list (bv 8) :=
    [ Z_to_bv 8 104%Z;   (* 'h'  *)
      Z_to_bv 8 105%Z;   (* 'i'  *)
      Z_to_bv 8 33%Z;    (* '!'  *)
      Z_to_bv 8 10%Z ].  (* '\n' *)

  Definition cat_recv (Γ : fs_view_names Σ) (q : Qp) (i : Z) (nl : nat)
      : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : nat) (_ : anode) (_ : nat) =>
              (⌜av !! i = Some (MkAnode (AFile cat_file) nl)⌝ ∗
               nview Γ q i (MkAnode (AFile cat_file) nl))%I)
           (nview Γ q i (MkAnode (AFile cat_file) nl)).

  (* the caller's ONE piece, out of its pin and nothing else *)
  Lemma cat_piece (Γ := fs_gamma_L fsc_fs) (q : Qp) (i : Z) (γo : gname)
      (nl : nat) :
    nview Γ q i (MkAnode (AFile cat_file) nl) -∗
    pf_at (aread_commit_at Γ appE i γo) (cat_recv Γ q i nl).
  Proof.
    iIntros "Hn". rewrite /pf_at /cat_recv /=. iSplit; [ | iExact "Hn" ].
    iApply (aread_commit_at_pinned_self Γ appE i γo q
              (MkAnode (AFile cat_file) nl) with "Hn").
    iIntros (av off d) "%Hav Hn". iSplitR; [ by iPureIntro | iExact "Hn" ].
  Qed.

  Lemma wp_uk_cat_read_learns (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname) (q : Qp) (nl : nat)
      (Γ := fs_gamma_L fsc_fs) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for reading on inode i" -- the caller's own
       knowledge of its descriptor, which is what selects the arm *)
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo)) -∗
    (* THE PIN: "that inode is this file" *)
    nview Γ q i (MkAnode (AFile cat_file) nl) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo)) -∗
       nview Γ q i (MkAnode (AFile cat_file) nl) -∗
       (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∨ (∃ off : nat,
             ⌜Z.to_nat (bv_unsigned r)
              = ard_count (Z.to_nat cnt) off (length cat_file)⌝ ∗
             ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
                g j = cat_file !!! (off + j)%nat⌝)) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hcnt Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh Hpin Hbuf Hcont".
    iDestruct (cat_piece q i γo nl with "Hpin") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo (cat_recv Γ q i nl)
                 with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N) (cat_recv Γ q i nl)) fd
              (FdOpen true wb (FdInode i γo))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim_st uslot
                 (xfam_rdf (ukn_pay N) (cat_recv Γ q i nl)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 r M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(_ & _ & _ & Hcore)".
    rewrite Hkey.
    (* the arm, at the state the handle named *)
    rewrite /fileread_extra_core /=.
    (* the count the receipt is stated at IS the caller's own *)
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (read_arms_file_learn i γo cnt q cat_file nl r M'
                 (m !!! Regidx a1_idx) k g Hlin Himg ltac:(lia)
                 with "Hcore") as "[Hpin Hlearn]".
    iApply ("Hcont" $! h' r g with "Hufdh Hpin Hlearn Hrun Hbuf").
  Qed.

End UkReadFile.
