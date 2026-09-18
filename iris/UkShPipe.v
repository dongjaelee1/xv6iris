(* ===================================================================== *)
(* UkShPipe.v -- runcmd's PIPE ARM, lane SH-PIPE (design/app-pipe.md      *)
(* §5.1).                                                                *)
(*                                                                        *)
(* [UkShRun.wp_kshr_runcmd] walks the command tree at [ush_simple], which  *)
(* REFUTES the REDIR and PIPE rows of the jump table.  Upstream's lane     *)
(* SH-REDIR took the REDIR row off that list at the TOP of the tree and    *)
(* nowhere deeper ([UkShRedir.ush_top]); this file does the same for PIPE: *)
(*                                                                        *)
(*   ush_ptop (UPipe l r) := ush_simple l /\ ush_simple r                  *)
(*   ush_ptop c           := ush_simple c                                  *)
(*                                                                        *)
(* IT IS NOT AN EDIT TO [ush_simple], for SH-REDIR's reason, verbatim:     *)
(* [ush_simple] is a structural [Fixpoint], so `at the top and nowhere     *)
(* deeper' is not expressible in it, and widening it in place would        *)
(* silently strengthen [UkShRun.wp_kshr_runcmd], whose proof has no        *)
(* ledger, no children set and no fd handles to spend on the arm.  The     *)
(* design page's §5.1 should say [ush_ptop], not `[ush_simple] admits'.    *)
(*                                                                        *)
(* THE ARM IS THIRTY-ONE INSTRUCTIONS IN THREE PROCESSES (0x13c..0x1c2     *)
(* plus the shared [exit(0)] at 0xea), and it is the only arm of runcmd    *)
(* that forks twice:                                                      *)
(*                                                                        *)
(*   0x13c  addi a0,s0,-40      &p[0] -- the [int p[2]] of the frame       *)
(*   0x140  jal  ra,0xc96       pipe(p)            -- A CALL PREMISE       *)
(*   0x144  bltz a0,0x172       -1 -> panic("pipe")                        *)
(*   0x148  jal  ra,0x68        fork1()                                    *)
(*   0x14c  c.bnez a0,0x17e     parent -> the second fork1                 *)
(*   -- THE LEFT CHILD, whose fd 1 becomes the WRITE end --                *)
(*   0x14e  c.li  a0,1                                                     *)
(*   0x150  jal   ra,0xcae      close(1)                                   *)
(*   0x154  lw    a0,-36(s0)    p[1]                                       *)
(*   0x158  jal   ra,0xcfe      dup(p[1])   -- lands on slot 1             *)
(*   0x15c  lw    a0,-40(s0)    p[0]                                       *)
(*   0x160  jal   ra,0xcae      close(p[0])                                *)
(*   0x164  lw    a0,-36(s0)    p[1]                                       *)
(*   0x168  jal   ra,0xcae      close(p[1])                                *)
(*   0x16c  c.ld  a0,8(s1)      pcmd->left                                 *)
(*   0x16e  jal   ra,0x8e       runcmd(pcmd->left)                         *)
(*   -- panic("pipe") --                                                   *)
(*   0x172  auipc a0,0x1 ; 0x176 addi a0,a0,342 ; 0x17a jal ra,0x4a        *)
(*   -- THE PARENT, second fork --                                         *)
(*   0x17e  jal   ra,0x68       fork1()                                    *)
(*   0x182  c.bnez a0,0x1a6     parent -> the two closes and two waits     *)
(*   -- THE RIGHT CHILD, whose fd 0 becomes the READ end.  a0 IS ALREADY   *)
(*      ZERO here (it is fork's own answer), which is why this child has   *)
(*      no [c.li a0,0] before its close --                                 *)
(*   0x184  jal   ra,0xcae      close(0)                                   *)
(*   0x188  lw    a0,-40(s0) ; 0x18c jal ra,0xcfe   dup(p[0]) -> slot 0    *)
(*   0x190  lw    a0,-40(s0) ; 0x194 jal ra,0xcae   close(p[0])            *)
(*   0x198  lw    a0,-36(s0) ; 0x19c jal ra,0xcae   close(p[1])            *)
(*   0x1a0  c.ld  a0,16(s1) ; 0x1a2 jal ra,0x8e     runcmd(pcmd->right)    *)
(*   -- THE PARENT --                                                      *)
(*   0x1a6  lw    a0,-40(s0) ; 0x1aa jal ra,0xcae   close(p[0])            *)
(*   0x1ae  lw    a0,-36(s0) ; 0x1b2 jal ra,0xcae   close(p[1])            *)
(*   0x1b6  c.li  a0,0 ; 0x1b8 jal ra,0xc8e         wait(0)                *)
(*   0x1bc  c.li  a0,0 ; 0x1be jal ra,0xc8e         wait(0)                *)
(*   0x1c2  c.j   0xea          break -> the common exit(0)                *)
(*                                                                        *)
(* THE THREE CONTINUATIONS ARE THE ARM'S OUTPUT, not walks it closes:     *)
(* each child is handed back at [runcmd]'s OWN entry pc with the ledger    *)
(* its prologue left ([c; W; c] on the left, [R; c; c] on the right) and   *)
(* whatever the pipe's registration lent it, and the parent at 0xea with   *)
(* the two forks' answers and the two reaps'.  That is the form the        *)
(* application lane wants ([UkShRedir.wp_kshr_redir_arm]'s shape): the     *)
(* children are where echo and cat are exec'd and the parent is where the  *)
(* round closes, and none of the three is nameable here.                   *)
(* [wp_kshr_runcmd_pipe] below is the CLAIM-FREE instance that closes all  *)
(* three off the landed walk and the taint, and it is the consumer test.   *)
(*                                                                        *)
(* pipe(2) IS A CALL PREMISE, for SH-REDIR's reason and one more.  What    *)
(* [pipe] does to the byte queue is the application's business (design     *)
(* §2/§3: the per-pipe protocol invariant, allocated right here), and none *)
(* of it is visible in the instructions above; and the FRAGMENT the leaf   *)
(* hands back lives in the key's own post ([UkRunSys.wp_uk_ecall_pipe]'s   *)
(* [spost_at uslot USYS_pipe]), which only the CLASS'S INSTANCE can read   *)
(* -- this file is stated over the class, so a premise naming              *)
(* [pipe_qfrag] could not be discharged here at all.  So [ush_pipe_call]   *)
(* is the shape of sh's [pipe] STUB at the ledger, with an abstract        *)
(* REGISTRATION [R : pipe_names -> iProp] in place of everything the       *)
(* application wants out of it, exactly as [ush_open_call]'s [K : fdtype   *)
(* -> iProp] stands in for the file claim.                                *)
(*                                                                        *)
(* THE CLOSE DEPOSITS RIDE ON THE CALL'S ANSWER, and they are PERSISTENT.  *)
(* Six of the arm's calls are [close], four of them on a PIPE row, and a   *)
(* pipe row's close is a flagged number ([UkRun.udepw_cl]): the payment is *)
(* [SpecFileclose.fileclose_cpay], i.e. a close link or the kill           *)
(* credential.  [ush_cldep st] below is that deposit at EVERY record and   *)
(* every key -- which is what the arm needs, because the three processes   *)
(* that close a pipe row run at THREE DIFFERENT gname records and only     *)
(* the parent's is in scope when the premise is supplied.  It is           *)
(* persistent, so one copy serves all six closes, both forks and both      *)
(* execs; today it comes off the taint                                     *)
(* ([UexecExecMint.udepw_law_of_sup_close]) and under design §2's ruling   *)
(* it comes off the registry.  It is therefore stated as a conjunct of the *)
(* pipe call's answer rather than as an arm parameter of its own.          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.     (* [NOFILE] / [PIDMAX] *)
Require Import UsysMemOk.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require UkLoad.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShRedir.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import FdSlots UserFd.
Require Import PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UexecSG.
Require Import ChildTok.
Require Import UexecRet.     (* [uwait_ans] -- what a reap answers *)
Require Import UkFork.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE SCOPE, ONE PIPE LEVEL WIDER THAN [ush_simple].                  *)
(* ===================================================================== *)
Definition ush_ptop (c : ushcmd) : Prop :=
  match c with
  | UPipe l r => ush_simple l /\ ush_simple r
  | _ => ush_simple c
  end.

Lemma ush_ptop_of_simple (c : ushcmd) : ush_simple c -> ush_ptop c.
Proof. destruct c; cbn; try exact (fun H => H). intros []. Qed.

Lemma ush_ptop_not_pipe (c : ushcmd) :
  (forall l r, c <> UPipe l r) -> ush_ptop c -> ush_simple c.
Proof.
  destruct c as [ args | c1 fl md fd | l r | l r | c1 ];
    cbn; try (intros _ H; exact H).
  intros Hne. exfalso. exact (Hne l r eq_refl).
Qed.

Section UkShPipe.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ===================================================================== *)
  (* §1a THE SYMBOL PINS, off [shk_syms_pins] -- [UkShRun]'s are [Local].   *)
  (* ===================================================================== *)
  Local Lemma shp_close  : ShSyms.close  = 0xcae.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_runcmd : ShSyms.runcmd = 0x8e.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_fork1  : ShSyms.fork1  = 0x68.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_pipe   : ShSyms.pipe   = 0xc96.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_wait   : ShSyms.wait   = 0xc8e.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_panic  : ShSyms.panic  = 0x4a.
  Proof using . reflexivity. Qed.
  Local Lemma shp_dup    : ShSyms.dup    = 0xcfe.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.

  (* ===================================================================== *)
  (* §2 THE CLOSE DEPOSIT, AT EVERY RECORD AND EVERY KEY.                   *)
  (*                                                                        *)
  (* [UkCat.kcat_cldep] is the same shape one record in; the arm needs the   *)
  (* record quantified too, because the two children close their pipe rows   *)
  (* at their OWN fresh gname triples.                                      *)
  (* ===================================================================== *)
  Definition ush_cldep (st : fdstate) : iProp Σ :=
    (□ ∀ (N : uk_names Σ) (m : regfile) (pc : mword 64),
        udepw_cl N m pc st)%I.

  Global Instance ush_cldep_persistent st : Persistent (ush_cldep st).
  Proof using . rewrite /ush_cldep. apply _. Qed.

  Lemma ush_cldep_of_law (st : fdstate) : udepw_law 21 -∗ ush_cldep st.
  Proof using .
    iIntros "#H". rewrite /ush_cldep. iIntros "!>" (N m pc).
    iApply (udepw_cl_of_udepw N m pc st).
    iApply (udepw_of_law N m pc 21 with "H").
  Qed.

  (* ===================================================================== *)
  (* §2a THE FD KEY A [lw] LEAVES IN a0.                                    *)
  (* The two four-byte words [pipe] wrote are [trunc32] of the descriptor    *)
  (* numbers; [lw] sign-extends one into a0, and [argfd] reads it back with  *)
  (* [bv_signed (trunc32 _)] -- the identity at a descriptor.                *)
  (* ===================================================================== *)
  Local Lemma ushpi_fd_key (k : nat) :
    (k < NOFILE)%nat ->
    bv_signed (trunc32
      (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat k) : mword 64))
       : mword 64)) = Z.of_nat k.
  Proof using .
    intros Hk. rewrite trunc32_sext64.
    unfold NOFILE in Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]];
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | exfalso; lia ].
  Qed.

  (* ===================================================================== *)
  (* §3 THE TWO STUBS THIS ARM NEEDS THAT NOBODY HAS WRITTEN.               *)
  (*                                                                        *)
  (* [UkShRedir.wp_kshx_close_std] shuts a STANDARD stream at the ledger;    *)
  (* the four pipe closes shut a TAIL descriptor at a HANDLE, which is       *)
  (* [UkRunSys.wp_uk_ecall_close]'s footprint, and its deposit is the        *)
  (* flagged one.  [UkSh.wp_ksh_close] is the same three instructions at     *)
  (* that leaf but takes the deposit differently; this one takes             *)
  (* [ush_cldep].                                                           *)
  (* ===================================================================== *)
  Lemma wp_kshpi_close_h (N : uk_names Σ) `{!ukn_const N} (h : CpuId)
      (m : regfile) (fd : nat) (st : fdstate) (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    shk_code (ukn_t N) -∗
    ush_cldep st -∗
    UserFd.ufd (ukn_fd N) fd st -∗
    urun N h m (mword_of_int ShSyms.close) avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun N h'
         (<[Regidx a0_idx := r]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Harg. iIntros "#Hcode #Hdep Hh Hrun Hcont".
    rewrite shp_close.
    (* ---- 0xcae  c.li a7,21 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xcae)
              (mword_of_int 21 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_cae with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 21 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E01 : add_vec_int (mword_of_int 0xcae : mword 64) 2
                  = mword_of_int 0xcb0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E01 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (E12 : add_vec_int (mword_of_int 0xcb0 : mword 64) 4
                  = mword_of_int 0xcb4)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xcb0  ecall -- CLOSE, at the HANDLE ---- *)
    iApply (wp_uk_ecall_close N h1 m1 (mword_of_int 0xcb0) fd st avail
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 21 : mword 64));
                    vm_compute; reflexivity)
              ltac:(rewrite Ha0_1; exact Harg)
              ltac:(rewrite E12; vm_compute; reflexivity)
              with "[] Hrun [] Hh").
    { iApply (uis_shk_cb0 with "Hcode"). }
    { iApply "Hdep". }
    rewrite E12.
    iIntros (h2 r) "_ Hrun".
    set (m2 := <[Regidx a0_idx := r]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 21 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xcb4  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcb4) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cb4 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "Hrun").
  Qed.

  (* ...and sh's [dup] stub, which nothing has walked: /init's is
     [UkInit.wp_kinit_dup] at /init's own image. *)
  Lemma wp_kshpi_dup (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
      (l : list fdstate) (fd0 : nat) (st : fdstate) (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd0 ->
    st <> FdClosed ->
    (* [UkRunSys.wp_uk_ecall_dup]'s own premise (lane OFF-HAND-4, S1): the
       slot fdalloc chose is not one the record can be said to HOLD.  It is
       a premise here rather than [UkRun.ukn_parked_eq]'s class fact,
       because sh's record carries no such instance and the arm's children
       run at records fork chose ([UkShRun.wp_kshr_fork1] relays
       [ukn_held N' = ukn_held N]). *)
    ukn_held N = ∅ ->
    shk_code (ukn_t N) -∗
    UserFd.ustd (ukn_fd N) l -∗
    UserFd.ufd_own (ukn_fd N) l fd0 st -∗
    urun N h m (mword_of_int ShSyms.dup) avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((∃ fd1 : nat,
           ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64)
            /\ (fd1 < NOFILE)%nat⌝ ∗
           UserFd.ualloc (ukn_fd N) l fd1 st ∗
           UserFd.ufd_own (ukn_fd N) (UserFd.ustd_after l st) fd0 st)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)
            /\ fd_lowest_closed l = None⌝ ∗
           UserFd.ustd (ukn_fd N) l ∗
           UserFd.ufd_own (ukn_fd N) l fd0 st)) -∗
       urun N h'
         (<[Regidx a0_idx := r]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Harg Hne Hhd. iIntros "#Hcode Hstd Hown Hrun Hcont".
    rewrite shp_dup.
    (* ---- 0xcfe  c.li a7,10 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xcfe)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_cfe with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 10 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E01 : add_vec_int (mword_of_int 0xcfe : mword 64) 2
                  = mword_of_int 0xd00)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E01 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (E12 : add_vec_int (mword_of_int 0xd00 : mword 64) 4
                  = mword_of_int 0xd04)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xd00  ecall -- DUP, at the ledger and the source claim ---- *)
    iApply (wp_uk_ecall_dup N h1 m1 (mword_of_int 0xd00) l fd0 st avail
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              ltac:(rewrite Ha0_1; exact Harg)
              Hne Hhd
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd Hown").
    { iApply (uis_shk_d00 with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    rewrite E12.
    iIntros (h2 r) "Hans Hrun".
    set (m2 := <[Regidx a0_idx := r]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xd04  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xd04) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d04 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "Hans Hrun").
  Qed.

  (* ===================================================================== *)
  (* §3a [wait(0)] AS A CALL, AT A NAMED CHILDREN SET.                      *)
  (*                                                                        *)
  (* [UkShRun.wp_kshr_wait0] is the same two instructions at the INDEX-FREE  *)
  (* fragment, and it DISCARDS the answer -- which is right for the LIST     *)
  (* arm (it reaps a child it forked for its side effects) and wrong here:   *)
  (* what closes a pipeline round is precisely what the two reaps hand back  *)
  (* (design §4.2).  So this one runs on [UkShRun.wp_kshr_wait] and relays   *)
  (* [UexecRet.uwait_ans].                                                  *)
  (* ===================================================================== *)
  Lemma wp_kshpi_wait0 (N : uk_names Σ) `{!ukn_const N} (h : CpuId)
      (m : regfile) (pc0 pc1 ret : Z) (imm : mword 21) (Sc : gset gname)
      (avail : nat) :
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    (mword_of_int ShSyms.wait : mword 64)
      = add_vec (mword_of_int pc1 : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64)
      = add_vec_int (mword_of_int pc1 : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int ShSyms.wait : mword 64) 0) ('b"0")
      = true ->
    ret_pc (mword_of_int ret : mword 64) = mword_of_int ret ->
    shk_code (ukn_t N) -∗
    uinstr_is (ukn_t N) (mword_of_int pc0) true
      (C_LI (mword_of_int 0 : mword 6, Regidx a0_idx)) -∗
    uinstr_is (ukn_t N) (mword_of_int pc1) false (JAL (imm, Regidx ra_idx)) -∗
    urun N h m (mword_of_int pc0) avail -∗
    UserChildren.uch (ukn_ch N) Sc -∗
    (∀ (h' : CpuId) (m' : regfile) (rw : mword 64) (Sc' : gset gname),
       ⌜ ucallee_saved m m' ⌝ -∗
       uwait_ans rw Sc Sc' -∗
       urun N h' m' (mword_of_int ret) avail -∗
       UserChildren.uch (ukn_ch N) Sc' -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros E01 Hsym Hret Hal Hrp. iIntros "#Hcode #Hi0 #Hi1 Hrun Hch Hcont".
    iApply (wp_uk_cli N h m (mword_of_int pc0)
              (mword_of_int 0 : mword 6) a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Hi0 Hrun").
    rewrite E01. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (sign_extend' 64
                      (mword_of_int 0 : mword 6) : mword 64)]> m).
    iApply (UkShRun.wp_kshr_jal N h1 m1 pc1 ShSyms.wait ret imm avail
              Hsym Hret Hal with "Hi1 Hrun").
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx ra_idx := (mword_of_int ret : mword 64)]> m1).
    assert (Ha0_2 : uint (m2 !!! Regidx a0_idx) = 0).
    { rewrite /m2 (upd_ne m1 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_eq m (Regidx a0_idx)
                     (regval_into_reg (sign_extend' 64
                        (mword_of_int 0 : mword 6) : mword 64))).
      vm_compute. reflexivity. }
    assert (Hra2 : m2 !!! Regidx ra_idx = (mword_of_int ret : mword 64))
      by exact (upd_eq m1 (Regidx ra_idx) _).
    iApply (UkShRun.wp_kshr_wait Hpsok_free N h2 m2 avail Sc Ha0_2
              with "Hcode Hrun Hch").
    iIntros (h3 rw Sc') "Hans Hrun Hch".
    rewrite Hra2 Hrp.
    iApply ("Hcont" $! h3 _ rw Sc' with "[%] Hans Hrun Hch").
    intros q Hq.
    rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) rw
               (UkShRedir.ushx_cs_ne q a0_idx Hq
                  ltac:(right; left; vm_compute; reflexivity))).
    rewrite (upd_ne _ (Regidx a7_idx) (Regidx q) _
               (UkShRedir.ushx_cs_ne q a7_idx Hq
                  ltac:(right; right; right; right; vm_compute; reflexivity))).
    rewrite /m2 (upd_ne m1 (Regidx ra_idx) (Regidx q) _
                   (UkShRedir.ushx_cs_ne q ra_idx Hq
                      ltac:(left; vm_compute; reflexivity))).
    rewrite /m1 (upd_ne m (Regidx a0_idx) (Regidx q) _
                   (UkShRedir.ushx_cs_ne q a0_idx Hq
                      ltac:(right; left; vm_compute; reflexivity))).
    reflexivity.
  Qed.


  (* ===================================================================== *)
  (* §3b FIVE SMALL FACTS THE ARM NEEDS.                                    *)
  (* ===================================================================== *)
  (* the two pipe handles as the map [UkShRun.wp_kshr_fork1] hands back
     twice -- one entry per end, and [a <> b] is what makes it two *)
  Local Lemma ushpi_hs_in (γf : gname) (a b : nat) (sa sb : fdstate) :
    a <> b ->
    UserFd.ufd γf a sa -∗ UserFd.ufd γf b sb -∗
    ([∗ map] fd ↦ st ∈ (<[a := sa]> {[b := sb]} : gmap nat fdstate),
       UserFd.ufd γf fd st).
  Proof using .
    intros Hab. iIntros "Ha Hb".
    rewrite big_sepM_insert; [ | apply lookup_singleton_ne; congruence ].
    rewrite big_sepM_singleton. iFrame "Ha Hb".
  Qed.

  Local Lemma ushpi_hs_out (γf : gname) (a b : nat) (sa sb : fdstate) :
    a <> b ->
    ([∗ map] fd ↦ st ∈ (<[a := sa]> {[b := sb]} : gmap nat fdstate),
       UserFd.ufd γf fd st) -∗
    UserFd.ufd γf a sa ∗ UserFd.ufd γf b sb.
  Proof using .
    intros Hab. iIntros "H".
    rewrite big_sepM_insert; [ | apply lookup_singleton_ne; congruence ].
    rewrite big_sepM_singleton. iExact "H".
  Qed.

  (* a claim on a TAIL descriptor is the handle: the ledger arm names a
     standard stream and this one is above them *)
  Local Lemma ushpi_own_hi (γf : gname) (l : list fdstate) (fd : nat)
      (st : fdstate) :
    (NSTD <= fd)%nat ->
    UserFd.ufd_own γf l fd st -∗ UserFd.ufd γf fd st.
  Proof using .
    intros Hge. iIntros "[[%Hlt _] | Hh]"; [ exfalso; lia | iExact "Hh" ].
  Qed.

  Local Lemma ushpi_after_none (l : list fdstate) (st : fdstate) :
    fd_lowest_closed l = None -> UserFd.ustd_after l st = l.
  Proof using . intros H. rewrite /UserFd.ustd_after H. reflexivity. Qed.

  (* WHERE THE dup LANDS.  [close(1); dup(x)] puts the copy on slot 1 and
     [close(0); dup(x)] on slot 0, and it is the LEDGER that says so
     (design/user-fd.md §2): after the close the lowest closed slot is the
     one just shut, because the slots below it are sh's own and open. *)
  Local Lemma ushpi_low1 (l : list fdstate) (x0 x1 : fdstate) :
    l !! 0%nat = Some x0 -> l !! 1%nat = Some x1 -> x0 <> FdClosed ->
    fd_lowest_closed (<[1%nat := FdClosed]> l) = Some 1%nat.
  Proof using .
    intros H0 H1 Hne.
    destruct l as [| y0 [| y1 l2 ] ]; [ discriminate H0 | discriminate H1 | ].
    cbn in H0. injection H0 as H0.
    destruct y0 as [| rb wb ty ];
      [ exfalso; exact (Hne (eq_sym H0)) | cbn; reflexivity ].
  Qed.

  Local Lemma ushpi_low0 (l : list fdstate) (x0 : fdstate) :
    l !! 0%nat = Some x0 ->
    fd_lowest_closed (<[0%nat := FdClosed]> l) = Some 0%nat.
  Proof using .
    intros H0. destruct l as [| y0 l1 ]; [ discriminate H0 | ].
    cbn. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §3c THE TWO STUBS IN [UkShRedir.wp_kshx_rcall]'S [Hstub] SHAPE.        *)
  (* ===================================================================== *)
  Local Lemma ushpi_close_stub (N : uk_names Σ) `{!ukn_const N} (m : regfile)
      (ret : Z) (fd : nat) (st : fdstate) :
    bv_signed (trunc32
      ((<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
         !!! Regidx a0_idx)) = Z.of_nat fd ->
    forall (h0 : CpuId) (av : nat),
      shk_code (ukn_t N) -∗
      (ush_cldep st ∗ UserFd.ufd (ukn_fd N) fd st) -∗
      urun N h0 (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
        (mword_of_int ShSyms.close) av -∗
      (∀ (h1 : CpuId) (r : mword 64),
         (emp : iProp Σ) -∗
         urun N h1
           (<[Regidx a0_idx := r]>
              (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]>
                 (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)))
           (ret_pc ((<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
                      !!! Regidx ra_idx)) av -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof using .
    intros Harg h0 av. iIntros "#Hc [#Hd Hh] Hrun Hcont".
    iApply (wp_kshpi_close_h N h0 _ fd st av Harg with "Hc Hd Hh Hrun").
    iIntros (h1 r) "Hrun". iApply ("Hcont" $! h1 r with "[] Hrun"). done.
  Qed.

  Local Lemma ushpi_dup_stub (N : uk_names Σ) `{!ukn_const N} (m : regfile)
      (ret : Z) (l : list fdstate) (fd0 : nat) (st : fdstate) :
    bv_signed (trunc32
      ((<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
         !!! Regidx a0_idx)) = Z.of_nat fd0 ->
    st <> FdClosed -> ukn_held N = ∅ ->
    forall (h0 : CpuId) (av : nat),
      shk_code (ukn_t N) -∗
      (UserFd.ustd (ukn_fd N) l ∗ UserFd.ufd_own (ukn_fd N) l fd0 st) -∗
      urun N h0 (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
        (mword_of_int ShSyms.dup) av -∗
      (∀ (h1 : CpuId) (r : mword 64),
         ((∃ fd1 : nat,
             ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64)
              /\ (fd1 < NOFILE)%nat⌝ ∗
             UserFd.ualloc (ukn_fd N) l fd1 st ∗
             UserFd.ufd_own (ukn_fd N) (UserFd.ustd_after l st) fd0 st)
          ∨ (⌜r = (mword_of_int (-1) : mword 64)
              /\ fd_lowest_closed l = None⌝ ∗
             UserFd.ustd (ukn_fd N) l ∗
             UserFd.ufd_own (ukn_fd N) l fd0 st)) -∗
         urun N h1
           (<[Regidx a0_idx := r]>
              (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]>
                 (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)))
           (ret_pc ((<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
                      !!! Regidx ra_idx)) av -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Harg Hne Hhd h0 av. iIntros "#Hc [Hs Ho] Hrun Hcont".
    iApply (wp_kshpi_dup N h0 _ l fd0 st av Harg Hne Hhd
              with "Hc Hs Ho Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* §4 pipe(2), AS A CALL PREMISE.                                         *)
  (*                                                                        *)
  (* Modelled on [UkRunSys.wp_uk_ecall_pipe]'s conclusion, at sh's [pipe]    *)
  (* STUB ENTRY (so the supplier owns all three instructions, which is what  *)
  (* keeps the walk claim-free), with FOUR differences and each is priced:   *)
  (*                                                                        *)
  (*  - NO TAINT PREMISE.  The leaf's [app_taint] is what design §2  *)
  (*    replaces with the registry, so the arm must not name it; the         *)
  (*    supplier does whatever its leaf asks.                                *)
  (*  - THE BUFFER ADDRESS IS QUANTIFIED INSIDE, because it is the frame's   *)
  (*    [int p[2]] at [sp - 40] and no caller of the arm can name [sp].      *)
  (*  - THE ANSWER IS AT THE TWO SLOTS, NOT AT [ualloc_at].  At the ledger    *)
  (*    this walk carries ([c;c;c] -- three console rows, nothing closed)     *)
  (*    [fd_lowest_closed] is [None], so both of the leaf's [ualloc_at] arms *)
  (*    are the HANDLE arm and the ledger does not move.  What the arm needs *)
  (*    is the two handles and that the eight bytes SPELL their numbers.      *)
  (*  - AN ABSTRACT REGISTRATION [R : pipe_names -> iProp] stands for         *)
  (*    everything the application wants out of the call (the queue          *)
  (*    fragment, and under design §3 the protocol invariant allocated        *)
  (*    around it).  It CANNOT be [pipe_qfrag] here: that lives in the       *)
  (*    key's post ([spost_at uslot USYS_pipe]) and only the deposit         *)
  (*    class's INSTANCE can read that row, while this file -- like every    *)
  (*    [Uk*] file -- is stated over the class.  So the fragment goes        *)
  (*    inside [R], exactly as the file claim goes inside                    *)
  (*    [UkShRedir.ush_open_call]'s [K].  At [R := fun _ => emp] the landed  *)
  (*    leaf instantiates it; at [R γp := pipe_inv … ∗ wtok …] PIPE-PROTO's  *)
  (*    caller does.                                                        *)
  (*                                                                        *)
  (* THE TWO DESCRIPTOR NUMBERS ARE EXISTENTIAL AND THAT IS NOT A CHOICE.    *)
  (* The design page says [p = {3, 4}] at the ledger [c;c;c]; it is not      *)
  (* derivable.  [UsysMemOk]'s pipe row scans the WHOLE table                *)
  (* ([fd_least_closed sts a]) and a program's ledger pins only the low      *)
  (* [NSTD] of it ([UserFd.ustd_agree]), so all a caller learns is           *)
  (* [NSTD <= a] and [a <> b].  The arm is therefore stated at abstract      *)
  (* [a] and [b] and never needs more: it feeds them back to close and dup   *)
  (* out of the bytes the kernel wrote.                                     *)
  (* ===================================================================== *)
  Definition ush_pipe_ans (N : uk_names Σ) (dst : Z) (l : list fdstate)
      (R : pipe_names -> iProp Σ) (r : mword 64) : iProp Σ :=
    ((∃ (a b : nat) (γp : pipe_names),
        ⌜ uint r = 0 /\ a <> b /\ (NSTD <= a)%nat /\ (NSTD <= b)%nat
          /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat ⌝ ∗
        ubytes (ukn_d N) dst 4
          (nth_byte (trunc32 (mword_of_int (Z.of_nat a) : mword 64))) ∗
        ubytes (ukn_d N) (dst + 4) 4
          (nth_byte (trunc32 (mword_of_int (Z.of_nat b) : mword 64))) ∗
        UserFd.ustd (ukn_fd N) l ∗
        UserFd.ufd (ukn_fd N) a (FdOpen true false (FdPipe γp)) ∗
        UserFd.ufd (ukn_fd N) b (FdOpen false true (FdPipe γp)) ∗
        (* the registry, design §2: persistent, so one copy pays all six
           closes in all three processes *)
        ush_cldep (FdOpen true false (FdPipe γp)) ∗
        ush_cldep (FdOpen false true (FdPipe γp)) ∗
        R γp)
     (* ...OR IT FAILED, AT -1.  [bltz a0] is what the code does with the
        answer, so `not zero' is not enough: the walk needs the SIGN.  The
        landed row pins the return only on success (open's and dup's rows
        do pin their -1) -- see the lane report, item R-1. *)
     ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
        (∃ f : nat -> bv 8, ubytes (ukn_d N) dst 8 f) ∗
        UserFd.ustd (ukn_fd N) l))%I.

  Definition ush_pipe_call (N : uk_names Σ) (l : list fdstate)
      (R : pipe_names -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (av : nat) (dst : Z) (f : nat -> bv 8),
       ⌜ uint (m !!! Regidx a0_idx) = dst ⌝ -∗
       shk_code (ukn_t N) -∗
       UserFd.ustd (ukn_fd N) l -∗
       ubytes (ukn_d N) dst 8 f -∗
       urun N h m (mword_of_int ShSyms.pipe) av -∗
       (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
          ush_pipe_ans N dst l R r -∗
          urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ===================================================================== *)
  (* §4a WHAT A fork1 ANSWERS, WITH THE CHILDREN READING TAKEN OUT.         *)
  (* [UkShRun.wp_kshr_fork1]'s answer, minus the [uch] fragment (which the   *)
  (* arm threads itself) -- the shape the parent continuation relays twice.  *)
  (* ===================================================================== *)
  Definition ush_fork_ans (Sc Sc' : gset gname) (Rc : iProp Σ)
      (Q : Z -> iProp Σ) (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64) /\ Sc' = Sc⌝ ∗ Rc)
     ∨ (∃ (γ : gname) (pidv : mword 32),
          ⌜r = (sign_extend' 64 pidv : mword 64)
           /\ (1 <= bv_unsigned pidv <= PIDMAX)%Z
           /\ Sc' = Sc ∪ {[γ]}⌝ ∗
          child_tok γ pidv Q))%I.

  (* ===================================================================== *)
  (* §5 THE ARM.                                                            *)
  (*                                                                        *)
  (* THE PAYLOAD IS ONE [Qc] FOR BOTH CHILDREN, and that is forced twice    *)
  (* over, not chosen:                                                      *)
  (*  - [UkShRun.wp_kshr_fork1] requires [forall x y, Q x = Q y], so a       *)
  (*    child's payload cannot depend on the status it exits with; and       *)
  (*  - a [wait(0)] CANNOT TELL THE TWO CHILDREN APART.  What a reap answers *)
  (*    is [UexecRet.uwait_ans], whose reaping arm binds its own generation  *)
  (*    [γ'] with [γ' ∈ cs \/ pidv = 1]; the pid-indexed form                *)
  (*    ([UkShRun.wp_kshr_wait_pid], the only one that refutes the [pidv =   *)
  (*    1] disjunct) needs the caller's own [UserChildren.upid] fragment,    *)
  (*    and [wp_kshr_fork1] DROPS the one [UkFork.wp_uk_ecall_fork]'s child  *)
  (*    arm hands out.  So this arm relays the two answers and the two       *)
  (*    tokens unredeemed, and design §4.2's lend/payload split has to be    *)
  (*    SYMMETRIC in the two children.  See the lane report, item R-2.      *)
  (*                                                                        *)
  (* WHAT THE REGISTRATION IS SPLIT INTO cannot be three premises of their   *)
  (* own, because [γp] is not known until the call has returned: it is one   *)
  (* wand, at three [pipe_names]-indexed parameters.                        *)
  (* ===================================================================== *)
  Lemma wp_kshr_pipe_arm (N : uk_names Σ) `{!ukn_const N}
      (cl cr : ushcmd) (h : CpuId) (m : regfile) (t szv cwdv : Z)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (av : nat)
      (R RcL RcR Rk : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ) :
    (forall x y : Z, Qc x = Qc y) ->
    (⊢ ukn_pay N (-1)) ->
    ukn_held N = ∅ ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    (* the two standard streams the two children shut before their dup:
       sh's own, open and not a pipe *)
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gp)) ->
    (forall (rb wb : bool) (gp : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    UkSh.sh_deps -∗
    shk_code (ukn_t N) -∗
    ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (UPipe cl cr) -∗
    usz (ukn_s N) szv -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    UserChildren.uch (ukn_ch N) Sc -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (∀ γp : pipe_names, R γp -∗ RcL γp ∗ (RcR γp ∗ Rk γp)) -∗
    ush_pipe_call N ld R -∗
    urun N h m (mword_of_int ShSyms.runcmd)
      (6 + (2 + (UkShDiag.ush_Dg + av))) -∗
    (* ---- THE LEFT CHILD, at runcmd's own entry: fd 1 is the pipe's
       WRITE end and the two tail slots the call came back on are shut ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ ukn_held N' = ∅ ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q cl -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       ush_cldep (FdOpen true false (FdPipe γp)) -∗
       ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + av)) -∗
       WP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD: fd 0 is the pipe's READ end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ ukn_held N' = ∅ ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q cr -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       ush_cldep (FdOpen true false (FdPipe γp)) -∗
       ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + av)) -∗
       WP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea -- the [break]'s target, which is the
       common [exit(0)] every runcmd arm ends at ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       uwait_ans rw1 S2 S3 -∗
       uwait_ans rw2 S3 S4 -∗
       UserChildren.uch (ukn_ch N) S4 -∗
       ush_jtab (ukn_t N) -∗
       usz (ukn_s N) szv -∗
       UserFd.ustd (ukn_fd N) ld -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       Rk γp -∗
       urun N h' m' (mword_of_int 0xea) (2 + (UkShDiag.ush_Dg + av)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros HQc Hpx Hhd Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    iIntros "#Hdp #Hcode #Hjt #Htree Hsz Hstd Hcwd Hch #Hkw Hsplit Hpipe Hrun
             HcL HcR Hpar".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iDestruct (ush_cmd_addr with "Htree") as %[Htr Ht8].
    assert (Ht4 : t mod 4 = 0)
      by (pose proof (Z.mod_divide t 8 ltac:(lia)) as Hd;
          apply Z.mod_divide; [ lia | ];
          destruct (proj1 Hd Ht8) as [kq Hkq]; exists (2 * kq); lia).
    (* ---- the frame: 0x8e..0xb8, out at the PIPE row 0x13c ---- *)
    iApply (UkShRun.wp_kshr_entry N (UPipe cl cr) h m t
              (2 + (UkShDiag.ush_Dg + av))%nat Ha0
              with "Hcode Hjt Htree Hrun").
    iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 Hp8 Hrun".
    cbn [ush_jarm].
    assert (HR64 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned.
      pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hsp4 : uint sp0 mod 4 = 0).
    { pose proof (Z.mod_divide (uint sp0) 8 ltac:(lia)) as Hd.
      apply Z.mod_divide; [ lia | ].
      destruct (proj1 Hd Hal8) as [kq Hkq]. exists (2 * kq). lia. }
    assert (Hd40 : (uint sp0 - 40) mod 4 = 0)
      by (rewrite Zminus_mod Hsp4; reflexivity).
    assert (Hd36 : (uint sp0 - 40 + 4) mod 4 = 0)
      by (replace (uint sp0 - 40 + 4) with (uint sp0 - 36) by lia;
          rewrite Zminus_mod Hsp4; reflexivity).
    assert (Ho40 : uoff_i12 (mword_of_int 4056 : mword 12) = -40)
      by (vm_compute; reflexivity).
    assert (Ho36 : uoff_i12 (mword_of_int 4060 : mword 12) = -36)
      by (vm_compute; reflexivity).
    assert (E40i : (sign_extend' 64 (mword_of_int 4056 : mword 12) : mword 64)
                   = mword_of_int (-40))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x13c  addi a0,s0,-40 -- &p[0] ---- *)
    iApply (wp_uk_addi N h1 m1 (mword_of_int 0x13c)
              (mword_of_int 4056 : mword 12) s0_idx a0_idx
              (mword_of_int (uint sp0 - 40))
              (2 + (UkShDiag.ush_Dg + av))%nat
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_1 E40i moi_add_l; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shk_13c with "Hcode"). }
    assert (E13c : add_vec_int (mword_of_int 0x13c : mword 64) 4
                   = mword_of_int 0x140)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E13c. iIntros (h2) "Hrun".
    set (p1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 40)
                                     : mword 64)]> m1).
    assert (Hp1 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    p1 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_p1 : uint (p1 !!! Regidx a0_idx) = uint sp0 - 40).
    { rewrite /p1 (upd_eq m1 (Regidx a0_idx)
                     (mword_of_int (uint sp0 - 40) : mword 64)).
      apply uint_moi. lia. }
    assert (Hst_p1 : UkShRun.ush_st p1 sp0 t).
    { split;
        [ rewrite (Hp1 s0_idx ltac:(vm_compute; discriminate)); exact Hs0_1
        | rewrite (Hp1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1 ]. }
    (* ---- 0x140  jal ra,0xc96 <pipe> -- THE CALL PREMISE ---- *)
    iApply (UkShRun.wp_kshr_jal N h2 p1 0x140 ShSyms.pipe 0x144
              (mword_of_int 2902 : mword 21) (2 + (UkShDiag.ush_Dg + av))%nat
              ltac:(rewrite shp_pipe; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_pipe; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_140 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (p2 := <[Regidx ra_idx := (mword_of_int 0x144 : mword 64)]> p1).
    assert (Hp2 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    p2 !!! Regidx q = p1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne p1 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Hra_p2 : ret_pc (p2 !!! Regidx ra_idx)
                     = (mword_of_int 0x144 : mword 64))
      by (rewrite /p2 (upd_eq p1 (Regidx ra_idx) _);
          apply bv_eq; vm_compute; reflexivity).
    assert (Hst_p2 : UkShRun.ush_st p2 sp0 t).
    { destruct Hst_p1 as [Hq0 Hq1]. split;
        [ rewrite (Hp2 s0_idx ltac:(vm_compute; discriminate)); exact Hq0
        | rewrite (Hp2 s1_idx ltac:(vm_compute; discriminate)); exact Hq1 ]. }
    iDestruct "Hp8" as (w8) "Hp8".
    iApply ("Hpipe" $! h3 p2 ((2 + (UkShDiag.ush_Dg + av))%nat)
              (uint sp0 - 40) (nth_byte w8)
              with "[%] Hcode Hstd [Hp8] Hrun").
    { rewrite (Hp2 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_p1. }
    { iExact "Hp8". }
    iIntros (h4 m4 r4) "%Hcs4 %Ha0_4 Hans Hrun".
    rewrite Hra_p2.
    pose proof (UkShRun.ush_st_cs p2 m4 sp0 t Hst_p2 Hcs4) as Hst_m4.
    iDestruct "Hans" as "[ Hok | (%Hr4 & Hbs & Hstd) ]"; last first.
    { (* ============ pipe FAILED: panic("pipe") ============ *)
      (* ---- 0x144  bltz a0,0x172 -- TAKEN ---- *)
      iApply (wp_uk_btype0 N h4 m4 (mword_of_int 0x144)
                (mword_of_int 46 : mword 13) a0_idx BLT
                true (mword_of_int 0x172) (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(cbn [uv_btaken]; rewrite Ha0_4 Hr4;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_144 with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x172  auipc a0,0x1 ---- *)
      assert (Eau : add_vec (mword_of_int 0x172 : mword 64)
                      (auipc_off (mword_of_int 1 : mword 20))
                    = (mword_of_int 0x1172 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_auipc N h5 m4 (mword_of_int 0x172)
                (mword_of_int 1 : mword 20) a0_idx
                (mword_of_int 0x1172) (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(exact (eq_sym Eau))
                with "[] Hrun").
      { iApply (uis_shk_172 with "Hcode"). }
      assert (E172 : add_vec_int (mword_of_int 0x172 : mword 64) 4
                     = mword_of_int 0x176)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E172. iIntros (h6) "Hrun".
      set (z1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x1172 : mword 64)]> m4).
      (* ---- 0x176  addi a0,a0,342 -- 0x12c8, the "pipe" literal ---- *)
      assert (Ead : add_vec (mword_of_int 0x1172 : mword 64)
                      (sign_extend' 64 (mword_of_int 342 : mword 12))
                    = (mword_of_int 0x12c8 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_addi N h6 z1 (mword_of_int 0x176)
                (mword_of_int 342 : mword 12) a0_idx a0_idx
                (mword_of_int 0x12c8) (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /z1 (upd_eq m4 (Regidx a0_idx)
                                     (mword_of_int 0x1172 : mword 64));
                      exact (eq_sym Ead))
                with "[] Hrun").
      { iApply (uis_shk_176 with "Hcode"). }
      assert (E176 : add_vec_int (mword_of_int 0x176 : mword 64) 4
                     = mword_of_int 0x17a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E176. iIntros (h7) "Hrun".
      set (z2 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x12c8 : mword 64)]> z1).
      (* ---- 0x17a  jal ra,0x4a <panic> ---- *)
      iApply (UkShRun.wp_kshr_jal N h7 z2 0x17a ShSyms.panic 0x17e
                (mword_of_int 2096848 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(rewrite shp_panic; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_panic; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_17a with "Hcode"). }
      iIntros (h8) "Hrun".
      set (z3 := <[Regidx ra_idx := (mword_of_int 0x17e : mword 64)]> z2).
      assert (Ha0_z3 : uint (z3 !!! Regidx a0_idx) = 0x12c8).
      { rewrite /z3 (upd_ne z2 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /z2 (upd_eq z1 (Regidx a0_idx)
                       (mword_of_int 0x12c8 : mword 64)).
        vm_compute. reflexivity. }
      replace (2 + (UkShDiag.ush_Dg + av))%nat
        with (UkShDiag.ush_Dg + (2 + av))%nat by lia.
      iDestruct Hpx as "Hpay".
      iApply (UkShDiag.ush_diag_leaf_holds N h8 z3 ShSyms.panic (2 + av)%nat
                ltac:(left; split;
                      [ reflexivity | right; right; exact Ha0_z3 ])
                with "Hdp Hcode Hro [] Hpay Hrun").
      rewrite UkShRun.ush_diag_res_panic. done. }
    (* ============ pipe SUCCEEDED ============ *)
    iDestruct "Hok" as (a b γp)
      "((%Hr0 & %Hab & %Hage & %Hbge & %Halt & %Hblt)
        & Hb0 & Hb1 & Hstd & Hha & Hhb & #HdR & #HdW & HR)".
    assert (Hr4z : r4 = (mword_of_int 0 : mword 64))
      by exact (moi_of_uint_eq r4 0 Hr0).
    (* ---- 0x144  bltz a0,0x172 -- NOT taken ---- *)
    iApply (wp_uk_btype0 N h4 m4 (mword_of_int 0x144)
              (mword_of_int 46 : mword 13) a0_idx BLT
              false (mword_of_int 0x172) (2 + (UkShDiag.ush_Dg + av))%nat
              ltac:(cbn [uv_btaken]; rewrite Ha0_4 Hr4z;
                    vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_144 with "Hcode"). }
    assert (E144 : add_vec_int (mword_of_int 0x144 : mword 64) 4
                   = mword_of_int 0x148)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E144. iIntros (h5) "Hrun".
    iDestruct ("Hsplit" $! γp with "HR") as "[HRcL [HRcR HRk]]".
    (* ---- 0x148  jal ra,0x68 <fork1> ---- *)
    iApply (UkShRun.wp_kshr_jal N h5 m4 0x148 ShSyms.fork1 0x14c
              (mword_of_int 2096928 : mword 21)
              (2 + (UkShDiag.ush_Dg + av))%nat
              ltac:(rewrite shp_fork1; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_fork1; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_148 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (f1 := <[Regidx ra_idx := (mword_of_int 0x14c : mword 64)]> m4).
    assert (Hra_f1 : ret_pc (f1 !!! Regidx ra_idx)
                     = (mword_of_int 0x14c : mword 64))
      by (rewrite /f1 (upd_eq m4 (Regidx ra_idx) _);
          apply bv_eq; vm_compute; reflexivity).
    assert (Hst_f1 : UkShRun.ush_st f1 sp0 t)
      by (apply UkShRun.ush_st_upd;
          [ exact Hst_m4 | vm_compute; lia | vm_compute; lia ]).
    iDestruct Hpx as "Hpay".
    iApply (UkShRun.wp_kshr_fork1 UkShDiag.ush_Dg N
              (fun gt gd _ =>
                 (ush_jtab gt ∗ ush_cmd gd t (UPipe cl cr)
                  ∗ ubytes gd (uint sp0 - 40) 4
                      (nth_byte (trunc32 (mword_of_int (Z.of_nat a)
                                          : mword 64)))
                  ∗ ubytes gd (uint sp0 - 40 + 4) 4
                      (nth_byte (trunc32 (mword_of_int (Z.of_nat b)
                                          : mword 64))))%I)
              (FP := UkShRun.forkable_ush_paypipe t (uint sp0 - 40)
                       (uint sp0 - 40 + 4) (UPipe cl cr)
                       (trunc32 (mword_of_int (Z.of_nat a) : mword 64))
                       (trunc32 (mword_of_int (Z.of_nat b) : mword 64)))
              szv ld
              (<[a := FdOpen true false (FdPipe γp)]>
                 {[b := FdOpen false true (FdPipe γp)]})
              h6 f1 av cwdv Sc Qc (RcL γp) (ukn_pay N (-1)) HQc
              with "Hcode Hro [Hjt Htree Hb0 Hb1] Hsz Hstd Hcwd Hch
                    [Hha Hhb] HRcL Hkw Hpay Hrun").
    { iFrame "Hjt Htree Hb0 Hb1". }
    { iApply (ushpi_hs_in (ukn_fd N) a b _ _ Hab with "Hha Hhb"). }
    rewrite Hra_f1.
    iSplitR "Hpar HcL HcR HRcR HRk".
    { (* ---- fork1's -1 arm: panic("fork") ---- *)
      iIntros (hA mA rA) "%HmsgA %HrA _ Hstd Hpayv Hrun".
      iApply (UkShDiag.ush_diag_leaf_holds N hA mA ShSyms.panic av
                ltac:(left; split; [ reflexivity | left; exact HmsgA ])
                with "Hdp Hcode Hro [] Hpayv Hrun").
      rewrite UkShRun.ush_diag_res_panic. done. }
    iSplitL "Hpar HcR HRcR HRk".
    - (* ===================== THE PARENT: fork1 AGAIN ==================== *)
      iIntros (hA mA rA) "%HrA %HcsA %Ha0_A Hans1 (#Hjt2 & #Ht2 & Hb0 & Hb1)
                          Hsz Hstd Hcwd HD Hpayv Hrun".
      iAssert (∃ S1 : gset gname,
                 ush_fork_ans Sc S1 (RcL γp) Qc rA
                 ∗ UserChildren.uch (ukn_ch N) S1)%I
        with "[Hans1]" as (S1) "[Hfa1 Hch]".
      { iDestruct "Hans1" as "[(%He & Hch & HRc) | Hpid]".
        - iExists Sc. iFrame "Hch". iLeft. iFrame "HRc". iPureIntro.
          split; [ exact He | reflexivity ].
        - iDestruct "Hpid" as (γ pidv) "(%Hr & %Hrng & Htok & Hch)".
          iExists (Sc ∪ {[γ]}). iFrame "Hch". iRight. iExists γ, pidv.
          iFrame "Htok". iPureIntro.
          split; [ exact Hr | split; [ exact Hrng | reflexivity ] ]. }
      pose proof (UkShRun.ush_st_cs f1 mA sp0 t Hst_f1 HcsA) as Hst_mA.
      (* ---- 0x14c  c.bnez a0,0x17e -- TAKEN ---- *)
      iApply (wp_uk_cbnez N hA mA (mword_of_int 0x14c)
                (mword_of_int 25 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x17e) (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_A; symmetry;
                      exact (UkShRun.ush_neqv_true rA HrA))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_14c with "Hcode"). }
      iIntros (hB) "Hrun".
      (* ---- 0x17e  jal ra,0x68 <fork1> ---- *)
      iApply (UkShRun.wp_kshr_jal N hB mA 0x17e ShSyms.fork1 0x182
                (mword_of_int 2096874 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(rewrite shp_fork1; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_fork1; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_17e with "Hcode"). }
      iIntros (hC) "Hrun".
      set (f2 := <[Regidx ra_idx := (mword_of_int 0x182 : mword 64)]> mA).
      assert (Hra_f2 : ret_pc (f2 !!! Regidx ra_idx)
                       = (mword_of_int 0x182 : mword 64))
        by (rewrite /f2 (upd_eq mA (Regidx ra_idx) _);
            apply bv_eq; vm_compute; reflexivity).
      assert (Hst_f2 : UkShRun.ush_st f2 sp0 t)
        by (apply UkShRun.ush_st_upd;
            [ exact Hst_mA | vm_compute; lia | vm_compute; lia ]).
      iDestruct (ushpi_hs_out (ukn_fd N) a b _ _ Hab with "HD") as "[Hha Hhb]".
      iApply (UkShRun.wp_kshr_fork1 UkShDiag.ush_Dg N
                (fun gt gd _ =>
                   (ush_jtab gt ∗ ush_cmd gd t (UPipe cl cr)
                    ∗ ubytes gd (uint sp0 - 40) 4
                        (nth_byte (trunc32 (mword_of_int (Z.of_nat a)
                                            : mword 64)))
                    ∗ ubytes gd (uint sp0 - 40 + 4) 4
                        (nth_byte (trunc32 (mword_of_int (Z.of_nat b)
                                            : mword 64))))%I)
                (FP := UkShRun.forkable_ush_paypipe t (uint sp0 - 40)
                         (uint sp0 - 40 + 4) (UPipe cl cr)
                         (trunc32 (mword_of_int (Z.of_nat a) : mword 64))
                         (trunc32 (mword_of_int (Z.of_nat b) : mword 64)))
                szv ld
                (<[a := FdOpen true false (FdPipe γp)]>
                   {[b := FdOpen false true (FdPipe γp)]})
                hC f2 av cwdv S1 Qc (RcR γp) (ukn_pay N (-1)) HQc
                with "Hcode Hro [Hjt2 Ht2 Hb0 Hb1] Hsz Hstd Hcwd Hch
                      [Hha Hhb] HRcR Hkw Hpayv Hrun").
      { iFrame "Hjt2 Ht2 Hb0 Hb1". }
      { iApply (ushpi_hs_in (ukn_fd N) a b _ _ Hab with "Hha Hhb"). }
      rewrite Hra_f2.
      iSplitR "Hpar HcR Hfa1 HRk".
      { (* ---- fork1's -1 arm: panic("fork") ---- *)
        iIntros (hZ mZ rZ) "%HmsgZ %HrZ _ Hstd Hpayv Hrun".
        iApply (UkShDiag.ush_diag_leaf_holds N hZ mZ ShSyms.panic av
                  ltac:(left; split; [ reflexivity | left; exact HmsgZ ])
                  with "Hdp Hcode Hro [] Hpayv Hrun").
        rewrite UkShRun.ush_diag_res_panic. done. }
      iSplitL "Hpar Hfa1 HRk".
      + (* ============ THE PARENT: two closes, two waits, break ========== *)
        iIntros (hD mD rD) "%HrD %HcsD %Ha0_D Hans2 (#Hjt3 & #Ht3 & Hb0 & Hb1)
                            Hsz Hstd Hcwd HD Hpayv Hrun".
        iAssert (∃ S2 : gset gname,
                   ush_fork_ans S1 S2 (RcR γp) Qc rD
                   ∗ UserChildren.uch (ukn_ch N) S2)%I
          with "[Hans2]" as (S2) "[Hfa2 Hch]".
        { iDestruct "Hans2" as "[(%He & Hch & HRc) | Hpid]".
          - iExists S1. iFrame "Hch". iLeft. iFrame "HRc". iPureIntro.
            split; [ exact He | reflexivity ].
          - iDestruct "Hpid" as (γ pidv) "(%Hr & %Hrng & Htok & Hch)".
            iExists (S1 ∪ {[γ]}). iFrame "Hch". iRight. iExists γ, pidv.
            iFrame "Htok". iPureIntro.
            split; [ exact Hr | split; [ exact Hrng | reflexivity ] ]. }
        pose proof (UkShRun.ush_st_cs f2 mD sp0 t Hst_f2 HcsD) as Hst_mD.
        (* ---- 0x182  c.bnez a0,0x1a6 -- TAKEN ---- *)
        iApply (wp_uk_cbnez N hD mD (mword_of_int 0x182)
                  (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                  true (mword_of_int 0x1a6) (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0_D; symmetry;
                        exact (UkShRun.ush_neqv_true rD HrD))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_182 with "Hcode"). }
        iIntros (hE) "Hrun".
        iDestruct (ushpi_hs_out (ukn_fd N) a b _ _ Hab with "HD")
          as "[Hha Hhb]".
        (* ---- 0x1a6  lw a0,-40(s0) -- p[0] ---- *)
        iApply (wp_uk_lw N hE mD (mword_of_int 0x1a6)
                  (mword_of_int 4056 : mword 12) s0_idx a0_idx
                  (uint sp0 - 40)
                  (trunc32 (mword_of_int (Z.of_nat a) : mword 64))
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(rewrite (proj1 Hst_mD) Ho40; lia)
                  Hd40 ltac:(vm_compute; discriminate)
                  with "[] Hb0 Hrun").
        { iApply (uis_shk_1a6 with "Hcode"). }
        iIntros "Hb0".
        assert (E1a6 : add_vec_int (mword_of_int 0x1a6 : mword 64) 4
                       = mword_of_int 0x1aa)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E1a6. iIntros (hF) "Hrun".
        set (k1 := <[Regidx a0_idx
                     := regval_into_reg (sign_extend' 64
                          (trunc32 (mword_of_int (Z.of_nat a)
                                    : mword 64)))]> mD).
        assert (Hk1a : bv_signed (trunc32
                  ((<[Regidx ra_idx := (mword_of_int 0x1ae : mword 64)]> k1)
                     !!! Regidx a0_idx)) = Z.of_nat a).
        { rewrite (upd_ne k1 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite /k1 (upd_eq mD (Regidx a0_idx) _).
          exact (ushpi_fd_key a Halt). }
        assert (Hst_k1 : UkShRun.ush_st k1 sp0 t)
          by (apply UkShRun.ush_st_upd;
              [ exact Hst_mD | vm_compute; lia | vm_compute; lia ]).
        (* ---- 0x1aa  jal ra,0xcae <close> -- close(p[0]) ---- *)
        iApply (UkShRedir.wp_kshx_rcall N hF k1 0x1aa ShSyms.close 0x1ae 21
                  (mword_of_int 2820 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  (ush_cldep (FdOpen true false (FdPipe γp))
                     ∗ UserFd.ufd (ukn_fd N) a
                         (FdOpen true false (FdPipe γp)))%I
                  (fun _ => emp%I)
                  (ushpi_close_stub N k1 0x1ae a
                     (FdOpen true false (FdPipe γp)) Hk1a)
                  ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_close; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcode [] [Hha] Hrun").
        { iApply (uis_shk_1aa with "Hcode"). }
        { iFrame "HdR Hha". }
        iIntros (hG mG rG) "%HcsG %Ha0_G _ Hrun".
        pose proof (UkShRun.ush_st_cs k1 mG sp0 t Hst_k1 HcsG) as Hst_mG.
        (* ---- 0x1ae  lw a0,-36(s0) -- p[1] ---- *)
        iApply (wp_uk_lw N hG mG (mword_of_int 0x1ae)
                  (mword_of_int 4060 : mword 12) s0_idx a0_idx
                  (uint sp0 - 40 + 4)
                  (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(rewrite (proj1 Hst_mG) Ho36; lia)
                  Hd36 ltac:(vm_compute; discriminate)
                  with "[] Hb1 Hrun").
        { iApply (uis_shk_1ae with "Hcode"). }
        iIntros "Hb1".
        assert (E1ae : add_vec_int (mword_of_int 0x1ae : mword 64) 4
                       = mword_of_int 0x1b2)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E1ae. iIntros (hH) "Hrun".
        set (k2 := <[Regidx a0_idx
                     := regval_into_reg (sign_extend' 64
                          (trunc32 (mword_of_int (Z.of_nat b)
                                    : mword 64)))]> mG).
        assert (Hk2b : bv_signed (trunc32
                  ((<[Regidx ra_idx := (mword_of_int 0x1b6 : mword 64)]> k2)
                     !!! Regidx a0_idx)) = Z.of_nat b).
        { rewrite (upd_ne k2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite /k2 (upd_eq mG (Regidx a0_idx) _).
          exact (ushpi_fd_key b Hblt). }
        assert (Hst_k2 : UkShRun.ush_st k2 sp0 t)
          by (apply UkShRun.ush_st_upd;
              [ exact Hst_mG | vm_compute; lia | vm_compute; lia ]).
        (* ---- 0x1b2  jal ra,0xcae <close> -- close(p[1]) ---- *)
        iApply (UkShRedir.wp_kshx_rcall N hH k2 0x1b2 ShSyms.close 0x1b6 21
                  (mword_of_int 2812 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  (ush_cldep (FdOpen false true (FdPipe γp))
                     ∗ UserFd.ufd (ukn_fd N) b
                         (FdOpen false true (FdPipe γp)))%I
                  (fun _ => emp%I)
                  (ushpi_close_stub N k2 0x1b6 b
                     (FdOpen false true (FdPipe γp)) Hk2b)
                  ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_close; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcode [] [Hhb] Hrun").
        { iApply (uis_shk_1b2 with "Hcode"). }
        { iFrame "HdW Hhb". }
        iIntros (hI mI rI) "%HcsI %Ha0_I _ Hrun".
        (* ---- 0x1b6..0x1ba  wait(0) ---- *)
        iApply (wp_kshpi_wait0 N hI mI 0x1b6 0x1b8 0x1bc
                  (mword_of_int 2774 : mword 21) S2
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_wait; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_wait; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcode [] [] Hrun Hch").
        { iApply (uis_shk_1b6 with "Hcode"). }
        { iApply (uis_shk_1b8 with "Hcode"). }
        iIntros (hJ mJ rw1 S3) "%HcsJ Hwa1 Hrun Hch".
        (* ---- 0x1bc..0x1c0  wait(0) again ---- *)
        iApply (wp_kshpi_wait0 N hJ mJ 0x1bc 0x1be 0x1c2
                  (mword_of_int 2768 : mword 21) S3
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_wait; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_wait; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcode [] [] Hrun Hch").
        { iApply (uis_shk_1bc with "Hcode"). }
        { iApply (uis_shk_1be with "Hcode"). }
        iIntros (hK mK rw2 S4) "%HcsK Hwa2 Hrun Hch".
        (* ---- 0x1c2  c.j 0xea -- break, to the common exit(0) ---- *)
        iApply (wp_uk_cj N hK mK (mword_of_int 0x1c2)
                  (mword_of_int 1940 : mword 11) (mword_of_int 0xea)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_1c2 with "Hcode"). }
        iIntros (hL) "Hrun".
        iApply ("Hpar" $! hL mK γp rA rD rw1 rw2 S1 S2 S3 S4
                  with "Hfa1 Hfa2 Hwa1 Hwa2 Hch Hjt3 Hsz Hstd Hcwd HRk Hrun").
      + (* ================== THE RIGHT CHILD: fd 0 = the READ end ========= *)
        iIntros (N' hD mD γ')
          "%Hpeq %Hheq %HcsD %Ha0_D Hmy HRcR #Hck (#Hjt3 & #Ht3 & Hb0 & Hb1)
           Hsz Hstd Hcwd Hch HD Hrun".
        pose proof (ukn_const_of_eq N' Qc Hpeq HQc) as Hcst'.
        assert (Hhd' : ukn_held N' = ∅) by (rewrite Hheq; exact Hhd).
        pose proof (UkShRun.ush_st_cs f2 mD sp0 t Hst_f2 HcsD) as Hst_mD.
        iDestruct (ushpi_hs_out (ukn_fd N') a b _ _ Hab with "HD")
          as "[Hha Hhb]".
        iDestruct (ush_cmd_pipe with "Ht3") as "[_ #Hsr3]".
        iDestruct "Hsr3" as (qr3) "[#Hqrp3 #Hqrc3]".
        (* ---- 0x182  c.bnez a0,0x1a6 -- NOT taken ---- *)
        iApply (wp_uk_cbnez N' hD mD (mword_of_int 0x182)
                  (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                  false (mword_of_int 0x1a6) (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0_D; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_shk_182 with "Hck"). }
        assert (E182 : add_vec_int (mword_of_int 0x182 : mword 64) 2
                       = mword_of_int 0x184)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E182. iIntros (hE) "Hrun".
        (* ---- 0x184  jal ra,0xcae <close> -- close(0), a0 IS fork's 0 ---- *)
        assert (Hcl0 : bv_signed (trunc32
                  ((<[Regidx ra_idx := (mword_of_int 0x188 : mword 64)]> mD)
                     !!! Regidx a0_idx)) = Z.of_nat 0).
        { rewrite (upd_ne mD (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)) Ha0_D.
          vm_compute. reflexivity. }
        iApply (UkShRedir.wp_kshx_rcall N' hE mD 0x184 ShSyms.close 0x188 21
                  (mword_of_int 2858 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  (UserFd.ustd (ukn_fd N') ld)
                  (fun _ => UserFd.ustd (ukn_fd N')
                              (<[0%nat := FdClosed]> ld))
                  (fun h0 avq =>
                     UkShRedir.wp_kshx_close_std N' h0
                       (<[Regidx ra_idx := (mword_of_int 0x188 : mword 64)]> mD)
                       ld 0%nat st0 avq Hcl0
                       ltac:(unfold NSTD; lia) Hl0 Hne0 Hnp0)
                  ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_close; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hck [] Hstd Hrun").
        { iApply (uis_shk_184 with "Hck"). }
        iIntros (hF mF rF) "%HcsF %Ha0_F Hstd Hrun".
        pose proof (UkShRun.ush_st_cs mD mF sp0 t Hst_mD HcsF) as Hst_mF.
        (* ---- 0x188  lw a0,-40(s0) -- p[0] ---- *)
        iApply (wp_uk_lw N' hF mF (mword_of_int 0x188)
                  (mword_of_int 4056 : mword 12) s0_idx a0_idx
                  (uint sp0 - 40)
                  (trunc32 (mword_of_int (Z.of_nat a) : mword 64))
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(rewrite (proj1 Hst_mF) Ho40; lia)
                  Hd40 ltac:(vm_compute; discriminate)
                  with "[] Hb0 Hrun").
        { iApply (uis_shk_188 with "Hck"). }
        iIntros "Hb0".
        assert (E188 : add_vec_int (mword_of_int 0x188 : mword 64) 4
                       = mword_of_int 0x18c)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E188. iIntros (hG) "Hrun".
        set (y1 := <[Regidx a0_idx
                     := regval_into_reg (sign_extend' 64
                          (trunc32 (mword_of_int (Z.of_nat a)
                                    : mword 64)))]> mF).
        assert (Hy1a : bv_signed (trunc32
                  ((<[Regidx ra_idx := (mword_of_int 0x190 : mword 64)]> y1)
                     !!! Regidx a0_idx)) = Z.of_nat a).
        { rewrite (upd_ne y1 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite /y1 (upd_eq mF (Regidx a0_idx) _).
          exact (ushpi_fd_key a Halt). }
        assert (Hst_y1 : UkShRun.ush_st y1 sp0 t)
          by (apply UkShRun.ush_st_upd;
              [ exact Hst_mF | vm_compute; lia | vm_compute; lia ]).
        (* ---- 0x18c  jal ra,0xcfe <dup> -- dup(p[0]), onto slot 0 ---- *)
        iApply (UkShRedir.wp_kshx_rcall N' hG y1 0x18c ShSyms.dup 0x190 10
                  (mword_of_int 2930 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  (UserFd.ustd (ukn_fd N') (<[0%nat := FdClosed]> ld)
                     ∗ UserFd.ufd_own (ukn_fd N') (<[0%nat := FdClosed]> ld) a
                         (FdOpen true false (FdPipe γp)))%I
                  (fun rr =>
                     ((∃ fd1 : nat,
                         ⌜rr = (mword_of_int (Z.of_nat fd1) : mword 64)
                          /\ (fd1 < NOFILE)%nat⌝ ∗
                         UserFd.ualloc (ukn_fd N') (<[0%nat := FdClosed]> ld)
                           fd1 (FdOpen true false (FdPipe γp)) ∗
                         UserFd.ufd_own (ukn_fd N')
                           (UserFd.ustd_after (<[0%nat := FdClosed]> ld)
                              (FdOpen true false (FdPipe γp))) a
                           (FdOpen true false (FdPipe γp)))
                      ∨ (⌜rr = (mword_of_int (-1) : mword 64)
                          /\ fd_lowest_closed (<[0%nat := FdClosed]> ld)
                             = None⌝ ∗
                         UserFd.ustd (ukn_fd N') (<[0%nat := FdClosed]> ld) ∗
                         UserFd.ufd_own (ukn_fd N') (<[0%nat := FdClosed]> ld) a
                           (FdOpen true false (FdPipe γp)))))%I
                  (ushpi_dup_stub N' y1 0x190 (<[0%nat := FdClosed]> ld) a
                     (FdOpen true false (FdPipe γp)) Hy1a
                     ltac:(discriminate) Hhd')
                  ltac:(rewrite shp_dup; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_dup; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hck [] [Hstd Hha] Hrun").
        { iApply (uis_shk_18c with "Hck"). }
        { iSplitL "Hstd"; [ iExact "Hstd" | ].
          iApply (UserFd.ufd_own_hi with "Hha"). }
        iIntros (hH mH rH) "%HcsH %Ha0_H Hdans Hrun".
        pose proof (ushpi_low0 ld st0 Hl0) as Hlow0.
        iDestruct "Hdans" as "[Hds | (%Hdf & _ & _)]"; last first.
        { exfalso. rewrite Hlow0 in Hdf. destruct Hdf as [_ Hc].
          discriminate Hc. }
        iDestruct "Hds" as (fd1) "((%Hfr & %Hfl) & Hal & Hown)".
        iDestruct (UserFd.ualloc_std (ukn_fd N') (<[0%nat := FdClosed]> ld)
                     fd1 0%nat (FdOpen true false (FdPipe γp)) Hlow0
                     with "Hal") as "[%Hfd1 Hstd]".
        rewrite /UserFd.ustd_after Hlow0.
        rewrite list_insert_insert.
        iDestruct (ushpi_own_hi (ukn_fd N') (<[0%nat := FdOpen true false
                      (FdPipe γp)]> ld) a (FdOpen true false (FdPipe γp)) Hage
                     with "Hown") as "Hha".
        pose proof (UkShRun.ush_st_cs y1 mH sp0 t Hst_y1 HcsH) as Hst_mH.
        (* ---- 0x190  lw a0,-40(s0) -- p[0] again ---- *)
        iApply (wp_uk_lw N' hH mH (mword_of_int 0x190)
                  (mword_of_int 4056 : mword 12) s0_idx a0_idx
                  (uint sp0 - 40)
                  (trunc32 (mword_of_int (Z.of_nat a) : mword 64))
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(rewrite (proj1 Hst_mH) Ho40; lia)
                  Hd40 ltac:(vm_compute; discriminate)
                  with "[] Hb0 Hrun").
        { iApply (uis_shk_190 with "Hck"). }
        iIntros "Hb0".
        assert (E190 : add_vec_int (mword_of_int 0x190 : mword 64) 4
                       = mword_of_int 0x194)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E190. iIntros (hI) "Hrun".
        set (y2 := <[Regidx a0_idx
                     := regval_into_reg (sign_extend' 64
                          (trunc32 (mword_of_int (Z.of_nat a)
                                    : mword 64)))]> mH).
        assert (Hy2a : bv_signed (trunc32
                  ((<[Regidx ra_idx := (mword_of_int 0x198 : mword 64)]> y2)
                     !!! Regidx a0_idx)) = Z.of_nat a).
        { rewrite (upd_ne y2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite /y2 (upd_eq mH (Regidx a0_idx) _).
          exact (ushpi_fd_key a Halt). }
        assert (Hst_y2 : UkShRun.ush_st y2 sp0 t)
          by (apply UkShRun.ush_st_upd;
              [ exact Hst_mH | vm_compute; lia | vm_compute; lia ]).
        (* ---- 0x194  jal ra,0xcae <close> -- close(p[0]) ---- *)
        iApply (UkShRedir.wp_kshx_rcall N' hI y2 0x194 ShSyms.close 0x198 21
                  (mword_of_int 2842 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  (ush_cldep (FdOpen true false (FdPipe γp))
                     ∗ UserFd.ufd (ukn_fd N') a
                         (FdOpen true false (FdPipe γp)))%I
                  (fun _ => emp%I)
                  (ushpi_close_stub N' y2 0x198 a
                     (FdOpen true false (FdPipe γp)) Hy2a)
                  ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_close; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hck [] [Hha] Hrun").
        { iApply (uis_shk_194 with "Hck"). }
        { iFrame "HdR Hha". }
        iIntros (hJ mJ rJ) "%HcsJ %Ha0_J _ Hrun".
        pose proof (UkShRun.ush_st_cs y2 mJ sp0 t Hst_y2 HcsJ) as Hst_mJ.
        (* ---- 0x198  lw a0,-36(s0) -- p[1] ---- *)
        iApply (wp_uk_lw N' hJ mJ (mword_of_int 0x198)
                  (mword_of_int 4060 : mword 12) s0_idx a0_idx
                  (uint sp0 - 40 + 4)
                  (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(rewrite (proj1 Hst_mJ) Ho36; lia)
                  Hd36 ltac:(vm_compute; discriminate)
                  with "[] Hb1 Hrun").
        { iApply (uis_shk_198 with "Hck"). }
        iIntros "Hb1".
        assert (E198 : add_vec_int (mword_of_int 0x198 : mword 64) 4
                       = mword_of_int 0x19c)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E198. iIntros (hK) "Hrun".
        set (y3 := <[Regidx a0_idx
                     := regval_into_reg (sign_extend' 64
                          (trunc32 (mword_of_int (Z.of_nat b)
                                    : mword 64)))]> mJ).
        assert (Hy3b : bv_signed (trunc32
                  ((<[Regidx ra_idx := (mword_of_int 0x1a0 : mword 64)]> y3)
                     !!! Regidx a0_idx)) = Z.of_nat b).
        { rewrite (upd_ne y3 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite /y3 (upd_eq mJ (Regidx a0_idx) _).
          exact (ushpi_fd_key b Hblt). }
        assert (Hst_y3 : UkShRun.ush_st y3 sp0 t)
          by (apply UkShRun.ush_st_upd;
              [ exact Hst_mJ | vm_compute; lia | vm_compute; lia ]).
        (* ---- 0x19c  jal ra,0xcae <close> -- close(p[1]) ---- *)
        iApply (UkShRedir.wp_kshx_rcall N' hK y3 0x19c ShSyms.close 0x1a0 21
                  (mword_of_int 2834 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  (ush_cldep (FdOpen false true (FdPipe γp))
                     ∗ UserFd.ufd (ukn_fd N') b
                         (FdOpen false true (FdPipe γp)))%I
                  (fun _ => emp%I)
                  (ushpi_close_stub N' y3 0x1a0 b
                     (FdOpen false true (FdPipe γp)) Hy3b)
                  ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_close; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hck [] [Hhb] Hrun").
        { iApply (uis_shk_19c with "Hck"). }
        { iFrame "HdW Hhb". }
        iIntros (hL mL rL) "%HcsL %Ha0_L _ Hrun".
        pose proof (UkShRun.ush_st_cs y3 mL sp0 t Hst_y3 HcsL) as Hst_mL.
        (* ---- 0x1a0  c.ld a0,16(s1) -- pcmd->right ---- *)
        iApply (UkShRun.wp_uk_cldq N' hL mL (mword_of_int 0x1a0)
                  (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
                  (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                  (t + 16) (mword_of_int qr3)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite (proj2 Hst_mL)
                          (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(rewrite Zplus_mod Ht8; reflexivity)
                  ltac:(vm_compute; discriminate)
                  with "[] Hqrp3 Hrun").
        { iApply (uis_shk_1a0 with "Hck"). }
        iIntros "_".
        assert (E1a0 : add_vec_int (mword_of_int 0x1a0 : mword 64) 2
                       = mword_of_int 0x1a2)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E1a0. iIntros (hM) "Hrun".
        set (y4 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int qr3 : mword 64)]> mL).
        (* ---- 0x1a2  jal ra,0x8e <runcmd> -- THE RECURSION ---- *)
        iApply (UkShRun.wp_kshr_jal N' hM y4 0x1a2 ShSyms.runcmd 0x1a6
                  (mword_of_int 2096876 : mword 21)
                  (2 + (UkShDiag.ush_Dg + av))%nat
                  ltac:(rewrite shp_runcmd; apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite shp_runcmd; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_1a2 with "Hck"). }
        iIntros (hO) "Hrun".
        iApply ("HcR" $! N' hO _ γ' γp qr3
                  with "[%] [%] [%] Hmy Hck Hjt3 Hqrc3 Hsz Hstd Hcwd Hch
                        HdR HdW HRcR Hrun");
          [ exact Hpeq | exact Hhd' | ].
        rewrite (upd_ne y4 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq mL (Regidx a0_idx) (mword_of_int qr3 : mword 64)).
    - (* =================== THE LEFT CHILD: fd 1 = the WRITE end ========= *)
      iIntros (N' h7 m7 γ')
        "%Hpeq %Hheq %Hcs7 %Ha0_7 Hmy HRcL #Hck (#Hjt2 & #Ht2 & Hb0 & Hb1)
         Hsz Hstd Hcwd Hch HD Hrun".
      pose proof (ukn_const_of_eq N' Qc Hpeq HQc) as Hcst'.
      assert (Hhd' : ukn_held N' = ∅) by (rewrite Hheq; exact Hhd).
      pose proof (UkShRun.ush_st_cs f1 m7 sp0 t Hst_f1 Hcs7) as Hst_m7.
      iDestruct (ushpi_hs_out (ukn_fd N') a b _ _ Hab with "HD")
        as "[Hha Hhb]".
      iDestruct (ush_cmd_pipe with "Ht2") as "[#Hsl2 _]".
      iDestruct "Hsl2" as (ql2) "[#Hqlp2 #Hqlc2]".
      (* ---- 0x14c  c.bnez a0,0x17e -- NOT taken ---- *)
      iApply (wp_uk_cbnez N' h7 m7 (mword_of_int 0x14c)
                (mword_of_int 25 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x17e) (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_7; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_14c with "Hck"). }
      assert (E14c : add_vec_int (mword_of_int 0x14c : mword 64) 2
                     = mword_of_int 0x14e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E14c. iIntros (h8) "Hrun".
      (* ---- 0x14e  c.li a0,1 ---- *)
      iApply (wp_uk_cli N' h8 m7 (mword_of_int 0x14e)
                (mword_of_int 1 : mword 6) a0_idx
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_shk_14e with "Hck"). }
      assert (E14e : add_vec_int (mword_of_int 0x14e : mword 64) 2
                     = mword_of_int 0x150)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E14e. iIntros (h9) "Hrun".
      set (q1 := <[Regidx a0_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 1 : mword 6) : mword 64)]> m7).
      assert (Hq1a : bv_signed (trunc32
                ((<[Regidx ra_idx := (mword_of_int 0x154 : mword 64)]> q1)
                   !!! Regidx a0_idx)) = Z.of_nat 1).
      { rewrite (upd_ne q1 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /q1 (upd_eq m7 (Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)).
        vm_compute. reflexivity. }
      assert (Hst_q1 : UkShRun.ush_st q1 sp0 t)
        by (apply UkShRun.ush_st_upd;
            [ exact Hst_m7 | vm_compute; lia | vm_compute; lia ]).
      (* ---- 0x150  jal ra,0xcae <close> -- close(1) ---- *)
      iApply (UkShRedir.wp_kshx_rcall N' h9 q1 0x150 ShSyms.close 0x154 21
                (mword_of_int 2910 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                (UserFd.ustd (ukn_fd N') ld)
                (fun _ => UserFd.ustd (ukn_fd N') (<[1%nat := FdClosed]> ld))
                (fun h0 avq =>
                   UkShRedir.wp_kshx_close_std N' h0
                     (<[Regidx ra_idx := (mword_of_int 0x154 : mword 64)]> q1)
                     ld 1%nat st1 avq Hq1a
                     ltac:(unfold NSTD; lia) Hl1 Hne1 Hnp1)
                ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_close; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hck [] Hstd Hrun").
      { iApply (uis_shk_150 with "Hck"). }
      iIntros (hA mA rA) "%HcsA %Ha0_A Hstd Hrun".
      pose proof (UkShRun.ush_st_cs q1 mA sp0 t Hst_q1 HcsA) as Hst_mA.
      (* ---- 0x154  lw a0,-36(s0) -- p[1] ---- *)
      iApply (wp_uk_lw N' hA mA (mword_of_int 0x154)
                (mword_of_int 4060 : mword 12) s0_idx a0_idx
                (uint sp0 - 40 + 4)
                (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite (proj1 Hst_mA) Ho36; lia)
                Hd36 ltac:(vm_compute; discriminate)
                with "[] Hb1 Hrun").
      { iApply (uis_shk_154 with "Hck"). }
      iIntros "Hb1".
      assert (E154 : add_vec_int (mword_of_int 0x154 : mword 64) 4
                     = mword_of_int 0x158)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E154. iIntros (hB) "Hrun".
      set (q2 := <[Regidx a0_idx
                   := regval_into_reg (sign_extend' 64
                        (trunc32 (mword_of_int (Z.of_nat b)
                                  : mword 64)))]> mA).
      assert (Hq2b : bv_signed (trunc32
                ((<[Regidx ra_idx := (mword_of_int 0x15c : mword 64)]> q2)
                   !!! Regidx a0_idx)) = Z.of_nat b).
      { rewrite (upd_ne q2 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /q2 (upd_eq mA (Regidx a0_idx) _).
        exact (ushpi_fd_key b Hblt). }
      assert (Hst_q2 : UkShRun.ush_st q2 sp0 t)
        by (apply UkShRun.ush_st_upd;
            [ exact Hst_mA | vm_compute; lia | vm_compute; lia ]).
      (* ---- 0x158  jal ra,0xcfe <dup> -- dup(p[1]), onto slot 1 ---- *)
      iApply (UkShRedir.wp_kshx_rcall N' hB q2 0x158 ShSyms.dup 0x15c 10
                (mword_of_int 2982 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                (UserFd.ustd (ukn_fd N') (<[1%nat := FdClosed]> ld)
                   ∗ UserFd.ufd_own (ukn_fd N') (<[1%nat := FdClosed]> ld) b
                       (FdOpen false true (FdPipe γp)))%I
                (fun rr =>
                   ((∃ fd1 : nat,
                       ⌜rr = (mword_of_int (Z.of_nat fd1) : mword 64)
                        /\ (fd1 < NOFILE)%nat⌝ ∗
                       UserFd.ualloc (ukn_fd N') (<[1%nat := FdClosed]> ld)
                         fd1 (FdOpen false true (FdPipe γp)) ∗
                       UserFd.ufd_own (ukn_fd N')
                         (UserFd.ustd_after (<[1%nat := FdClosed]> ld)
                            (FdOpen false true (FdPipe γp))) b
                         (FdOpen false true (FdPipe γp)))
                    ∨ (⌜rr = (mword_of_int (-1) : mword 64)
                        /\ fd_lowest_closed (<[1%nat := FdClosed]> ld)
                           = None⌝ ∗
                       UserFd.ustd (ukn_fd N') (<[1%nat := FdClosed]> ld) ∗
                       UserFd.ufd_own (ukn_fd N') (<[1%nat := FdClosed]> ld) b
                         (FdOpen false true (FdPipe γp)))))%I
                (ushpi_dup_stub N' q2 0x15c (<[1%nat := FdClosed]> ld) b
                   (FdOpen false true (FdPipe γp)) Hq2b
                   ltac:(discriminate) Hhd')
                ltac:(rewrite shp_dup; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_dup; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hck [] [Hstd Hhb] Hrun").
      { iApply (uis_shk_158 with "Hck"). }
      { iSplitL "Hstd"; [ iExact "Hstd" | ].
        iApply (UserFd.ufd_own_hi with "Hhb"). }
      iIntros (hC mC rC) "%HcsC %Ha0_C Hdans Hrun".
      pose proof (ushpi_low1 ld st0 st1 Hl0 Hl1 Hne0) as Hlow1.
      iDestruct "Hdans" as "[Hds | (%Hdf & _ & _)]"; last first.
      { exfalso. rewrite Hlow1 in Hdf. destruct Hdf as [_ Hc].
        discriminate Hc. }
      iDestruct "Hds" as (fd1) "((%Hfr & %Hfl) & Hal & Hown)".
      iDestruct (UserFd.ualloc_std (ukn_fd N') (<[1%nat := FdClosed]> ld)
                   fd1 1%nat (FdOpen false true (FdPipe γp)) Hlow1
                   with "Hal") as "[%Hfd1 Hstd]".
      rewrite /UserFd.ustd_after Hlow1.
      rewrite list_insert_insert.
      iDestruct (ushpi_own_hi (ukn_fd N') (<[1%nat := FdOpen false true
                    (FdPipe γp)]> ld) b (FdOpen false true (FdPipe γp)) Hbge
                   with "Hown") as "Hhb".
      pose proof (UkShRun.ush_st_cs q2 mC sp0 t Hst_q2 HcsC) as Hst_mC.
      (* ---- 0x15c  lw a0,-40(s0) -- p[0] ---- *)
      iApply (wp_uk_lw N' hC mC (mword_of_int 0x15c)
                (mword_of_int 4056 : mword 12) s0_idx a0_idx
                (uint sp0 - 40)
                (trunc32 (mword_of_int (Z.of_nat a) : mword 64))
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite (proj1 Hst_mC) Ho40; lia)
                Hd40 ltac:(vm_compute; discriminate)
                with "[] Hb0 Hrun").
      { iApply (uis_shk_15c with "Hck"). }
      iIntros "Hb0".
      assert (E15c : add_vec_int (mword_of_int 0x15c : mword 64) 4
                     = mword_of_int 0x160)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E15c. iIntros (hD) "Hrun".
      set (q3 := <[Regidx a0_idx
                   := regval_into_reg (sign_extend' 64
                        (trunc32 (mword_of_int (Z.of_nat a)
                                  : mword 64)))]> mC).
      assert (Hq3a : bv_signed (trunc32
                ((<[Regidx ra_idx := (mword_of_int 0x164 : mword 64)]> q3)
                   !!! Regidx a0_idx)) = Z.of_nat a).
      { rewrite (upd_ne q3 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /q3 (upd_eq mC (Regidx a0_idx) _).
        exact (ushpi_fd_key a Halt). }
      assert (Hst_q3 : UkShRun.ush_st q3 sp0 t)
        by (apply UkShRun.ush_st_upd;
            [ exact Hst_mC | vm_compute; lia | vm_compute; lia ]).
      (* ---- 0x160  jal ra,0xcae <close> -- close(p[0]) ---- *)
      iApply (UkShRedir.wp_kshx_rcall N' hD q3 0x160 ShSyms.close 0x164 21
                (mword_of_int 2894 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                (ush_cldep (FdOpen true false (FdPipe γp))
                   ∗ UserFd.ufd (ukn_fd N') a
                       (FdOpen true false (FdPipe γp)))%I
                (fun _ => emp%I)
                (ushpi_close_stub N' q3 0x164 a
                   (FdOpen true false (FdPipe γp)) Hq3a)
                ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_close; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hck [] [Hha] Hrun").
      { iApply (uis_shk_160 with "Hck"). }
      { iFrame "HdR Hha". }
      iIntros (hE mE rE) "%HcsE %Ha0_E _ Hrun".
      pose proof (UkShRun.ush_st_cs q3 mE sp0 t Hst_q3 HcsE) as Hst_mE.
      (* ---- 0x164  lw a0,-36(s0) -- p[1] ---- *)
      iApply (wp_uk_lw N' hE mE (mword_of_int 0x164)
                (mword_of_int 4060 : mword 12) s0_idx a0_idx
                (uint sp0 - 40 + 4)
                (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite (proj1 Hst_mE) Ho36; lia)
                Hd36 ltac:(vm_compute; discriminate)
                with "[] Hb1 Hrun").
      { iApply (uis_shk_164 with "Hck"). }
      iIntros "Hb1".
      assert (E164 : add_vec_int (mword_of_int 0x164 : mword 64) 4
                     = mword_of_int 0x168)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E164. iIntros (hF) "Hrun".
      set (q4 := <[Regidx a0_idx
                   := regval_into_reg (sign_extend' 64
                        (trunc32 (mword_of_int (Z.of_nat b)
                                  : mword 64)))]> mE).
      assert (Hq4b : bv_signed (trunc32
                ((<[Regidx ra_idx := (mword_of_int 0x16c : mword 64)]> q4)
                   !!! Regidx a0_idx)) = Z.of_nat b).
      { rewrite (upd_ne q4 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /q4 (upd_eq mE (Regidx a0_idx) _).
        exact (ushpi_fd_key b Hblt). }
      assert (Hst_q4 : UkShRun.ush_st q4 sp0 t)
        by (apply UkShRun.ush_st_upd;
            [ exact Hst_mE | vm_compute; lia | vm_compute; lia ]).
      (* ---- 0x168  jal ra,0xcae <close> -- close(p[1]) ---- *)
      iApply (UkShRedir.wp_kshx_rcall N' hF q4 0x168 ShSyms.close 0x16c 21
                (mword_of_int 2886 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                (ush_cldep (FdOpen false true (FdPipe γp))
                   ∗ UserFd.ufd (ukn_fd N') b
                       (FdOpen false true (FdPipe γp)))%I
                (fun _ => emp%I)
                (ushpi_close_stub N' q4 0x16c b
                   (FdOpen false true (FdPipe γp)) Hq4b)
                ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_close; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hck [] [Hhb] Hrun").
      { iApply (uis_shk_168 with "Hck"). }
      { iFrame "HdW Hhb". }
      iIntros (hG mG rG) "%HcsG %Ha0_G _ Hrun".
      pose proof (UkShRun.ush_st_cs q4 mG sp0 t Hst_q4 HcsG) as Hst_mG.
      (* ---- 0x16c  c.ld a0,8(s1) -- pcmd->left ---- *)
      iApply (UkShRun.wp_uk_cldq N' hG mG (mword_of_int 0x16c)
                (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                (t + 8) (mword_of_int ql2)
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite (proj2 Hst_mG)
                        (uint_moi t ltac:(unfold Z64; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Ht8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hqlp2 Hrun").
      { iApply (uis_shk_16c with "Hck"). }
      iIntros "_".
      assert (E16c : add_vec_int (mword_of_int 0x16c : mword 64) 2
                     = mword_of_int 0x16e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E16c. iIntros (hH) "Hrun".
      set (q5 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ql2 : mword 64)]> mG).
      (* ---- 0x16e  jal ra,0x8e <runcmd> -- THE RECURSION ---- *)
      iApply (UkShRun.wp_kshr_jal N' hH q5 0x16e ShSyms.runcmd 0x172
                (mword_of_int 2096928 : mword 21)
                (2 + (UkShDiag.ush_Dg + av))%nat
                ltac:(rewrite shp_runcmd; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite shp_runcmd; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_16e with "Hck"). }
      iIntros (hI) "Hrun".
      iApply ("HcL" $! N' hI _ γ' γp ql2
                with "[%] [%] [%] Hmy Hck Hjt2 Hqlc2 Hsz Hstd Hcwd Hch
                      HdR HdW HRcL Hrun");
        [ exact Hpeq | exact Hhd' | ].
      rewrite (upd_ne q5 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mG (Regidx a0_idx) (mword_of_int ql2 : mword 64)).
  Qed.


  (* ===================================================================== *)
  (* §6 THE CONSUMER TEST: THE ARM AT THE FREE INSTANCE.                    *)
  (*                                                                        *)
  (* [wp_kshr_pipe_arm] hands out three continuations and eleven            *)
  (* parameters; the only way to see the statement is USABLE is to spend     *)
  (* it, so this corollary closes all three off the LANDED walk and the      *)
  (* taint, at the degenerate instantiation the brief names -- [R],          *)
  (* [RcL], [RcR] and [Rk] all [emp], [Qc] the caller's own payload (so      *)
  (* the children's records satisfy the caller's exec supply and its free    *)
  (* exit row, exactly as the LIST and BACK arms arrange), the two           *)
  (* children through [UkShDiag.wp_kshr_runcmd_final] and the parent         *)
  (* through [UkShRun.wp_kshr_exit0] at 0xea -- which is where the LIST      *)
  (* arm's parent and the BACK arm's parent end too.                        *)
  (*                                                                        *)
  (* WHAT IT DOES NOT DISCHARGE, and this is the lane's one refutation:      *)
  (* [ush_pipe_call] stays a premise.  It is NOT instantiable from the       *)
  (* landed [UkRunSys.wp_uk_ecall_pipe] -- see the note on                   *)
  (* [ush_pipe_ans]'s failure arm.  Everything else the arm asks for is      *)
  (* paid here, which is what makes the gap exactly one row wide.            *)
  (* ===================================================================== *)
  Lemma wp_kshr_runcmd_pipe (cl cr : ushcmd) :
    ush_simple cl -> ush_simple cr ->
    forall (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
           (t szv cwdv : Z) (ld : list fdstate) (st0 st1 : fdstate)
           (Sc : gset gname) (n : nat),
      (⊢ ukn_pay N (-1)) ->
      ukn_held N = ∅ ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
      st0 <> FdClosed -> st1 <> FdClosed ->
      (forall (rb wb : bool) (gp : pipe_names),
         st0 <> FdOpen rb wb (FdPipe gp)) ->
      (forall (rb wb : bool) (gp : pipe_names),
         st1 <> FdOpen rb wb (FdPipe gp)) ->
      UkSh.sh_deps -∗
      shk_code (ukn_t N) -∗
      uxsup_at (ukn_pay N) -∗
      □ (app_taint -∗ ukn_pay N (-1)) -∗
      ush_jtab (ukn_t N) -∗
      ush_cmd (ukn_d N) t (UPipe cl cr) -∗
      usz (ukn_s N) szv -∗
      UserFd.ustd (ukn_fd N) ld -∗
      UserCwd.ucwd (ukn_cwd N) cwdv -∗
      UserChildren.uch (ukn_ch N) Sc -∗
      ush_pipe_call N ld (fun _ => emp)%I -∗
      urun N h m (mword_of_int ShSyms.runcmd)
        (6 * ush_ht (UPipe cl cr) + (2 + (UkShDiag.ush_Dg + n))) -∗
      WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hscl Hscr N Hcst h m t szv cwdv ld st0 st1 Sc n
           Hpx Hhd Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    iIntros "#Hdp #Hcode #Hexs #Hkw #Hjt #Htree Hsz Hstd Hcwd Hch Hpipe Hrun".
    pose proof (Nat.le_max_l (ush_ht cl) (ush_ht cr)) as HM1.
    pose proof (Nat.le_max_r (ush_ht cl) (ush_ht cr)) as HM2.
    replace (6 * ush_ht (UPipe cl cr) + (2 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (2 + (UkShDiag.ush_Dg
                      + (6 * Nat.max (ush_ht cl) (ush_ht cr) + n))))%nat
      by (cbn [ush_ht]; lia).
    iApply (wp_kshr_pipe_arm N cl cr h m t szv cwdv ld st0 st1 Sc
              (6 * Nat.max (ush_ht cl) (ush_ht cr) + n)%nat
              (fun _ => emp)%I (fun _ => emp)%I (fun _ => emp)%I
              (fun _ => emp)%I (ukn_pay N)
              (ukn_const_eq (N := N)) Hpx Hhd Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1
              with "Hdp Hcode Hjt Htree Hsz Hstd Hcwd Hch Hkw [] Hpipe Hrun").
    { iIntros (γp) "_". iSplitR; [ done | iSplitR; done ]. }
    - (* ---- THE LEFT CHILD: the landed walk, at the ledger its prologue
           left ---- *)
      iIntros (N' h' m' γ' γp q) "%Hpeq %Hhd' %Ha0' Hmy #Hck #Hjt2 #Hqc Hsz
                                  Hstd Hcwd Hch _ _ _ Hrun".
      pose proof (ukn_const_of_eq N' (ukn_pay N) Hpeq
                    (ukn_const_eq (N := N))) as Hcst'.
      assert (Hpx' : ⊢ ukn_pay N' (-1)) by (rewrite Hpeq; exact Hpx).
      iAssert (□ (app_taint -∗ ukn_pay N' (-1)))%I as "#Hkw'".
      { rewrite Hpeq. iExact "Hkw". }
      iAssert (uxsup_at (ukn_pay N')) as "#Hexs'".
      { rewrite Hpeq. iExact "Hexs". }
      replace (2 + (UkShDiag.ush_Dg
                    + (6 * Nat.max (ush_ht cl) (ush_ht cr) + n)))%nat
        with (6 * ush_ht cl
              + (2 + (UkShDiag.ush_Dg
                      + (6 * (Nat.max (ush_ht cl) (ush_ht cr) - ush_ht cl)
                         + n))))%nat by lia.
      iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free cl Hscl N' h' m' q szv
                (<[1%nat := FdOpen false true (FdPipe γp)]> ld)
                ((6 * (Nat.max (ush_ht cl) (ush_ht cr) - ush_ht cl) + n)%nat)
                Hpx' Ha0'
                with "Hdp Hck Hexs' Hkw' Hjt2 Hqc Hsz Hstd [Hcwd] [Hch] Hrun").
      { iApply (UserCwd.ucwd_any_of with "Hcwd"). }
      { iApply (UserChildren.uch_any_of with "Hch"). }
    - (* ---- THE RIGHT CHILD ---- *)
      iIntros (N' h' m' γ' γp q) "%Hpeq %Hhd' %Ha0' Hmy #Hck #Hjt2 #Hqc Hsz
                                  Hstd Hcwd Hch _ _ _ Hrun".
      pose proof (ukn_const_of_eq N' (ukn_pay N) Hpeq
                    (ukn_const_eq (N := N))) as Hcst'.
      assert (Hpx' : ⊢ ukn_pay N' (-1)) by (rewrite Hpeq; exact Hpx).
      iAssert (□ (app_taint -∗ ukn_pay N' (-1)))%I as "#Hkw'".
      { rewrite Hpeq. iExact "Hkw". }
      iAssert (uxsup_at (ukn_pay N')) as "#Hexs'".
      { rewrite Hpeq. iExact "Hexs". }
      replace (2 + (UkShDiag.ush_Dg
                    + (6 * Nat.max (ush_ht cl) (ush_ht cr) + n)))%nat
        with (6 * ush_ht cr
              + (2 + (UkShDiag.ush_Dg
                      + (6 * (Nat.max (ush_ht cl) (ush_ht cr) - ush_ht cr)
                         + n))))%nat by lia.
      iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free cr Hscr N' h' m' q szv
                (<[0%nat := FdOpen true false (FdPipe γp)]> ld)
                ((6 * (Nat.max (ush_ht cl) (ush_ht cr) - ush_ht cr) + n)%nat)
                Hpx' Ha0'
                with "Hdp Hck Hexs' Hkw' Hjt2 Hqc Hsz Hstd [Hcwd] [Hch] Hrun").
      { iApply (UserCwd.ucwd_any_of with "Hcwd"). }
      { iApply (UserChildren.uch_any_of with "Hch"). }
    - (* ---- THE PARENT: 0xea  c.li a0,0 ; 0xec  jal ra,<exit> ---- *)
      iIntros (h' m' γp r1 r2 rw1 rw2 S1 S2 S3 S4)
        "_ _ _ _ Hch #Hjt3 Hsz Hstd Hcwd _ Hrun".
      iApply (UkShRun.wp_kshr_exit0 N h' m' 0xea 0xec 0xf0
                (mword_of_int 0 : mword 6) (mword_of_int 2970 : mword 21)
                (2 + (UkShDiag.ush_Dg
                      + (6 * Nat.max (ush_ht cl) (ush_ht cr) + n)))%nat Hpx
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcode [] [] Hrun").
      { iApply (uis_shk_ea with "Hcode"). }
      { iApply (uis_shk_ec with "Hcode"). }
  Qed.

  (* ...AND THE SAME AT [ush_ptop], which is what makes the scope claim of   *)
  (* §1 load-bearing: at every shape but a top-level PIPE the LANDED walk    *)
  (* covers the tree unchanged, and at that one shape the corollary above    *)
  (* does.                                                                   *)
  Lemma wp_kshr_runcmd_ptop (c : ushcmd) :
    ush_ptop c ->
    forall (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
           (t szv cwdv : Z) (ld : list fdstate) (st0 st1 : fdstate)
           (Sc : gset gname) (n : nat),
      (⊢ ukn_pay N (-1)) ->
      ukn_held N = ∅ ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
      st0 <> FdClosed -> st1 <> FdClosed ->
      (forall (rb wb : bool) (gp : pipe_names),
         st0 <> FdOpen rb wb (FdPipe gp)) ->
      (forall (rb wb : bool) (gp : pipe_names),
         st1 <> FdOpen rb wb (FdPipe gp)) ->
      UkSh.sh_deps -∗
      shk_code (ukn_t N) -∗
      uxsup_at (ukn_pay N) -∗
      □ (app_taint -∗ ukn_pay N (-1)) -∗
      ush_jtab (ukn_t N) -∗
      ush_cmd (ukn_d N) t c -∗
      usz (ukn_s N) szv -∗
      UserFd.ustd (ukn_fd N) ld -∗
      UserCwd.ucwd (ukn_cwd N) cwdv -∗
      UserChildren.uch (ukn_ch N) Sc -∗
      ush_pipe_call N ld (fun _ => emp)%I -∗
      urun N h m (mword_of_int ShSyms.runcmd)
        (6 * ush_ht c + (2 + (UkShDiag.ush_Dg + n))) -∗
      WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hp N Hcst h m t szv cwdv ld st0 st1 Sc n
           Hpx Hhd Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    iIntros "#Hdp #Hcode #Hexs #Hkw #Hjt #Htree Hsz Hstd Hcwd Hch Hpipe Hrun".
    destruct c as [ args | c1 fl md fd | lc rc | lc rc | c1 ].
    - iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free (UExec args) Hp N h m t
                szv ld n Hpx Ha0
                with "Hdp Hcode Hexs Hkw Hjt Htree Hsz Hstd [Hcwd] [Hch] Hrun");
        [ iApply (UserCwd.ucwd_any_of with "Hcwd")
        | iApply (UserChildren.uch_any_of with "Hch") ].
    - exfalso. cbn in Hp. exact Hp.
    - iApply (wp_kshr_runcmd_pipe lc rc (proj1 Hp) (proj2 Hp) N h m t szv cwdv
                ld st0 st1 Sc n Hpx Hhd Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1
                with "Hdp Hcode Hexs Hkw Hjt Htree Hsz Hstd Hcwd Hch Hpipe
                      Hrun").
    - iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free (UList lc rc) Hp N h m t
                szv ld n Hpx Ha0
                with "Hdp Hcode Hexs Hkw Hjt Htree Hsz Hstd [Hcwd] [Hch] Hrun");
        [ iApply (UserCwd.ucwd_any_of with "Hcwd")
        | iApply (UserChildren.uch_any_of with "Hch") ].
    - iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free (UBack c1) Hp N h m t
                szv ld n Hpx Ha0
                with "Hdp Hcode Hexs Hkw Hjt Htree Hsz Hstd [Hcwd] [Hch] Hrun");
        [ iApply (UserCwd.ucwd_any_of with "Hcwd")
        | iApply (UserChildren.uch_any_of with "Hch") ].
  Qed.


  (* ===================================================================== *)
  (* §7 HOW FAR THE LANDED LEAF GETS -- THE GAP, MEASURED.                  *)
  (*                                                                        *)
  (* [ush_pipe_call] is the shape sh's code needs and it is NOT             *)
  (* instantiable from [UkRunSys.wp_uk_ecall_pipe] today.  The reason is    *)
  (* ONE CONJUNCT and this section proves that it is one: the predicate     *)
  (* below is [ush_pipe_call] with its failure arm weakened from            *)
  (* [r = -1] to the leaf's own [uint r <> 0], and                          *)
  (* [ush_pipe_call_weak_of_leaf] discharges it OUTRIGHT -- the two         *)
  (* handles, the eight bytes read back as the two descriptor numbers, the  *)
  (* ledger, the persistent close registrations and (at [R := emp]) the     *)
  (* registration are all payable today, off the taint and nothing else.    *)
  (*                                                                        *)
  (* WHAT IS MISSING is the SIGN of a failing return, because sh's next     *)
  (* instruction is [bltz a0]: [UsysMemOk.usys_fd_ok]'s pipe row pins the   *)
  (* return only on the success side (`if decide (uint r = 0) then … else   *)
  (* sts' = sts'), while the OPEN and DUP rows beside it both say           *)
  (* [r = -1] on failure.  It cannot be bridged by a premise: a premise     *)
  (* [forall r, uint r <> 0 -> r = -1] is FALSE, and one stated over the    *)
  (* row is false too (take [r = 1], [sts' = sts]), so anything built on    *)
  (* either would be vacuous (claude-notes/durable-notes.md, Vacuity).      *)
  (* The fix is in the ROW and its kernel-side discharge; see the lane      *)
  (* report, item R-1.                                                      *)
  (* ===================================================================== *)
  Definition ush_pipe_ans_weak (N : uk_names Σ) (dst : Z) (l : list fdstate)
      (R : pipe_names -> iProp Σ) (r : mword 64) : iProp Σ :=
    ((∃ (a b : nat) (γp : pipe_names),
        ⌜ uint r = 0 /\ a <> b /\ (NSTD <= a)%nat /\ (NSTD <= b)%nat
          /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat ⌝ ∗
        ubytes (ukn_d N) dst 4
          (nth_byte (trunc32 (mword_of_int (Z.of_nat a) : mword 64))) ∗
        ubytes (ukn_d N) (dst + 4) 4
          (nth_byte (trunc32 (mword_of_int (Z.of_nat b) : mword 64))) ∗
        UserFd.ustd (ukn_fd N) l ∗
        UserFd.ufd (ukn_fd N) a (FdOpen true false (FdPipe γp)) ∗
        UserFd.ufd (ukn_fd N) b (FdOpen false true (FdPipe γp)) ∗
        ush_cldep (FdOpen true false (FdPipe γp)) ∗
        ush_cldep (FdOpen false true (FdPipe γp)) ∗
        R γp)
     ∨ (⌜ uint r <> 0 ⌝ ∗
        (∃ f : nat -> bv 8, ubytes (ukn_d N) dst 8 f) ∗
        UserFd.ustd (ukn_fd N) l))%I.

  Definition ush_pipe_call_weak (N : uk_names Σ) (l : list fdstate)
      (R : pipe_names -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (av : nat) (dst : Z) (f : nat -> bv 8),
       ⌜ uint (m !!! Regidx a0_idx) = dst ⌝ -∗
       shk_code (ukn_t N) -∗
       UserFd.ustd (ukn_fd N) l -∗
       ubytes (ukn_d N) dst 8 f -∗
       urun N h m (mword_of_int ShSyms.pipe) av -∗
       (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
          ush_pipe_ans_weak N dst l R r -∗
          urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE TAINT AND THE CLOSE LAW ARE TWO PREMISES, not one.  The taint is
     what [UkRunSys.wp_uk_ecall_pipe] itself asks for; [udepw_law 21] is
     what the two registrations are built from, and the taint gives it
     ([UexecExecMint.udepw_law_of_sup_close]) -- but that file is an
     APPLICATION-LEVEL mint and importing it into a proofmode-heavy walk
     is the wedge claude-notes/durable-notes.md records, so the
     conversion is left to the caller, which lives up there anyway. *)
  Lemma ush_pipe_call_weak_of_leaf (N : uk_names Σ) `{!ukn_const N}
      (l : list fdstate) :
    (* the ledger this walk carries: three console rows, nothing shut, so
       both of the leaf's allocations land ABOVE the standard streams and
       the ledger does not move *)
    fd_lowest_closed l = None ->
    app_taint -∗ udepw_law 21 -∗
    ush_pipe_call_weak N l (fun _ => emp)%I.
  Proof using Hpsok_free.
    intros Hnone. iIntros "#Hkc #Hcl".
    iIntros (h m av dst f) "%Hdst #Hcode Hstd Hbuf Hrun Hcont".
    rewrite shp_pipe.
    (* ---- 0xc96  c.li a7,4 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xc96)
              (mword_of_int 4 : mword 6) a7_idx av
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c96 with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 4 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E01 : add_vec_int (mword_of_int 0xc96 : mword 64) 2
                  = mword_of_int 0xc98)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E01 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (E12 : add_vec_int (mword_of_int 0xc98 : mword 64) 4
                  = mword_of_int 0xc9c)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xc98  ecall -- the PIPE leaf ---- *)
    iApply (wp_uk_ecall_pipe N h1 m1 (mword_of_int 0xc98) l f av
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 4 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hkc Hstd [Hbuf]").
    { iApply (uis_shk_c98 with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    { rewrite Ha0_1 Hdst. iExact "Hbuf". }
    rewrite E12.
    iIntros (h2 r g W fdep M' fdv' cw' cs') "Hans _ Hrun Hbuf".
    rewrite Ha0_1 Hdst.
    set (m2 := <[Regidx a0_idx := r]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 4 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xc9c  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xc9c) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) av
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c9c with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 m2 r with "[%] [%] [Hans Hbuf] Hrun").
    { intros q Hq.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) r
                 (UkShRedir.ushx_cs_ne q a0_idx Hq
                    ltac:(right; left; vm_compute; reflexivity))).
      rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx q) _
                     (UkShRedir.ushx_cs_ne q a7_idx Hq
                        ltac:(right; right; right; right;
                              vm_compute; reflexivity))).
      reflexivity. }
    { exact (upd_eq m1 (Regidx a0_idx) r). }
    rewrite /ush_pipe_ans_weak.
    iDestruct "Hans" as "[ Hok | [%Hrne Hstd] ]"; last first.
    { iRight. iSplitR; [ by iPureIntro | ]. iSplitL "Hbuf"; [ | iExact "Hstd" ].
      iExists g. iExact "Hbuf". }
    iDestruct "Hok" as (a b γp)
      "((%Hr0 & %Hab & %Halt & %Hblt & %Hg & _) & Hala & Halb & Hstd)".
    rewrite (ushpi_after_none l (FdOpen true false (FdPipe γp)) Hnone).
    rewrite (ushpi_after_none l (FdOpen false true (FdPipe γp)) Hnone).
    rewrite /UserFd.ualloc_at Hnone.
    iDestruct "Hala" as "[%Hage Hha]".
    iDestruct "Halb" as "[%Hbge Hhb]".
    iLeft. iExists a, b, γp.
    iSplitR.
    { iPureIntro. repeat split; assumption. }
    (* THE EIGHT BYTES ARE THE TWO NUMBERS, split at four *)
    rewrite (UkRunSys.ubytes_split (ukn_d N) dst 4 8 g ltac:(lia)).
    iDestruct "Hbuf" as "[Hlo Hhi]".
    iSplitL "Hlo".
    { iApply (UkRunSys.ubytes_ext (ukn_d N) dst 4 g
                (nth_byte (trunc32 (mword_of_int (Z.of_nat a) : mword 64)))
                with "Hlo").
      intros j Hj. rewrite (Hg j ltac:(lia)).
      destruct (Nat.ltb_spec j 4) as [_ | Hc]; [ reflexivity | lia ]. }
    iSplitL "Hhi".
    { replace (dst + 4) with (dst + Z.of_nat 4) by lia.
      iApply (UkRunSys.ubytes_ext (ukn_d N) (dst + Z.of_nat 4) (8 - 4)%nat
                (fun j => g (4 + j)%nat)
                (nth_byte (trunc32 (mword_of_int (Z.of_nat b) : mword 64)))
                with "Hhi").
      intros j Hj. rewrite (Hg (4 + j)%nat ltac:(lia)).
      destruct (Nat.ltb_spec (4 + j) 4) as [Hc | _]; [ lia | ].
      replace (4 + j - 4)%nat with j by lia. reflexivity. }
    iFrame "Hstd Hha Hhb".
    iSplitR; [ iApply (ush_cldep_of_law with "Hcl") | ].
    iSplitR; [ iApply (ush_cldep_of_law with "Hcl") | done ].
  Qed.

End UkShPipe.
