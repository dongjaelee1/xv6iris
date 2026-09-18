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

End UkShPipe.
