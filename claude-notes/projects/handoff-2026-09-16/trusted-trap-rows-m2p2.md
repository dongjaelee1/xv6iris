# TRAP-ROWS M2 part 2 -- the trusted diff (statements only)
diff --git a/iris/SpecFileread.v b/iris/SpecFileread.v
index b2bd55a9b..1c0428ffe 100644
--- a/iris/SpecFileread.v
+++ b/iris/SpecFileread.v
@@ -1158,6 +1158,39 @@ Section SpecFileread.
     iExists cur, d'. iExact "Hrd".
   Qed.
 
+  (* ...AND THE REASON, READ OFF WITHOUT SPENDING THE ARM (lane TRAP-ROWS,
+     T2(ii)).  Both disjuncts are persistent, so the receipt comes straight
+     back; the READING arm is refuted at [r = -1] by its own run bound --
+     [bv_unsigned] of the -1 word is 2^64-1 and the run is at most the
+     request, which is a 32-bit signed count ([SpecSysRead.sys_rw_count_lt]
+     at the caller).  This is what lets usertrap's second [killed] check
+     refute its own resume branch: at a zero flag the shot is impossible,
+     so the reason can only be the sign guard, and a caller that asked for
+     a non-negative count has ruled that out too. *)
+  Lemma console_receipt_m1_why (gn : gname) (P : uptd) (Rd : nat -> nat -> iProp Σ)
+      (Rin : list (list mobs * bv 8) -> iProp Σ)
+      (n : Z) (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) :
+    (n < 2 ^ 31)%Z ->
+    r = (mword_of_int (-1) : mword 64) ->
+    console_receipt gn P Rd Rin n r M' addr -∗
+    (⌜(n < 0)%Z⌝ ∨ ChildTok.kill_shot gn) ∗
+    console_receipt gn P Rd Rin n r M' addr.
+  Proof.
+    intros Hnb Hr. rewrite /console_receipt.
+    iIntros "[ (%Hm1 & #Hwhy & Hrd) | Hrun ]".
+    - iSplitR "Hrd"; [ iExact "Hwhy" | ].
+      iLeft. iSplitR; [by iPureIntro |].
+      iSplitR; [iExact "Hwhy" |]. iExact "Hrd".
+    - iDestruct "Hrun" as (d dc cur hs sl) "(%Hd & %Hle & _)".
+      exfalso. rewrite Hr in Hd.
+      assert (Hm : bv_unsigned (mword_of_int (-1) : mword 64)
+                   = 18446744073709551615%Z)
+        by (vm_compute; reflexivity).
+      rewrite Hm in Hd.
+      change (2 ^ 31)%Z with 2147483648%Z in Hnb.
+      lia.
+  Qed.
+
   (* THE ONE STEP FROM consoleread's POST.  Its ledger is over the run's
      SOURCE function [bs]; the image is [umem_wr M dst d bs], and
      [UserPtTree.umem_wr_lookup_in] reads the [j]th byte back out of it
@@ -1316,6 +1349,25 @@ Section SpecFileread.
     P ∗ fileread_extra_core gn pt st n F Rd Rin r M' addr.
   Proof. by iIntros "$". Qed.
 
+  (* ...and the same at the arm the dispatcher's row 5 is stated at *)
+  Lemma fileread_extra_core_m1_why (gn : gname) (pt : uptd) (rb : bool) (n : Z)
+      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
+      (Rd : nat -> nat -> iProp Σ)
+      (Rin : list (list mobs * bv 8) -> iProp Σ)
+      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) :
+    (n < 2 ^ 31)%Z ->
+    r = (mword_of_int (-1) : mword 64) ->
+    fileread_extra_core gn pt (FdOpen true rb (FdDevice CONSOLE)) n F Rd Rin r M' addr -∗
+    (⌜(n < 0)%Z⌝ ∨ ChildTok.kill_shot gn) ∗
+    fileread_extra_core gn pt (FdOpen true rb (FdDevice CONSOLE)) n F Rd Rin r M' addr.
+  Proof.
+    intros Hnb Hr. rewrite /fileread_extra_core.
+    destruct (decide (CONSOLE = CONSOLE)) as [_ | Hne];
+      [| exfalso; exact (Hne eq_refl)].
+    iApply (console_receipt_m1_why gn pt Rd Rin n r M' addr Hnb Hr).
+  Qed.
+
+
   (* ---- READING THE KEYED INPUT, BUILDING THE KEYED OUTPUT -------------
      One-liners, so that no walk ever has to unfold the two matches and
      every arm names the fact it is standing on. *)
diff --git a/iris/SpecKwait.v b/iris/SpecKwait.v
index 35d258939..aaa3f51e6 100644
--- a/iris/SpecKwait.v
+++ b/iris/SpecKwait.v
@@ -245,7 +245,8 @@ Definition wp_kwait_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG 
          the reaper holds both halves of the zombie's [p->xstate] and the
          escrow is keyed at what that cell reads
          ([ProcDefs.proc_dormant]'s ZOMBIE arm). *)
-      wait_ans rv (xstate_val xw) cs cs' -∗
+      wait_ans rv (xstate_val xw) cs cs' (pv_gen (us_V U))
+        (bool_decide (addr = (zero_reg : mword 64))) -∗
       sie_cap_gpr KT1 mf av b pj -∗
       cpu_own 0 eb pj b lks -∗
       pc_is ret_tgt -∗
diff --git a/iris/SpecSysWait.v b/iris/SpecSysWait.v
index 0049375ec..08970cfd4 100644
--- a/iris/SpecSysWait.v
+++ b/iris/SpecSysWait.v
@@ -144,7 +144,8 @@ Definition wp_sys_wait_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslot
          child's pid with its escrow -- at the status word this call
          copied out -- the pid uniqueness over the caller's children, and
          the reading at what the reap left it. *)
-      wait_ans rv (xstate_val xw) cs cs' -∗
+      wait_ans rv (xstate_val xw) cs cs' (pv_gen (us_V U))
+        (bool_decide (v0 = (zero_reg : mword 64))) -∗
       sie_cap_gpr KT1 mf av b pj -∗
       cpu_own 0%nat eb pj b lks -∗
       pc_is ret_tgt -∗
diff --git a/iris/SpecSyscall.v b/iris/SpecSyscall.v
index ea8db76f4..bf19a10cd 100644
--- a/iris/SpecSyscall.v
+++ b/iris/SpecSyscall.v
@@ -516,9 +516,16 @@ Section SyscExec.
      The escrow the reap hands back and the pid uniqueness that identifies
      the generation ride in the same answer ([UexecRet.uwait_ans], which is
      kwait's own [UserChildren.wait_ans] at the a0 word). *)
+  (* ...AND IT CARRIES THE CALLER'S GENERATION AND ITS STATUS POINTER
+     (lane TRAP-ROWS, T4): the -1 arm's reason names the incarnation and is
+     guarded on the null pointer, and both are readings of data this row
+     already has. *)
   Definition sysc_wait_out (U : ustate) (r : mword 64)
       (cs cs' : gset gname) : iProp Σ :=
-    (⌜sysc_num (us_V U) = UsysMemOk.USYS_wait⌝ -∗ uwait_ans r cs cs')%I.
+    (⌜sysc_num (us_V U) = UsysMemOk.USYS_wait⌝ -∗
+       uwait_ans_at r cs cs' (pv_gen (us_V U))
+         (bool_decide (pv_tf (us_V U) !!! tf_arg_idx 0
+                       = (zero_reg : mword 64))))%I.
 
   Lemma sysc_wait_out_ne (U : ustate) (r : mword 64) (cs cs' : gset gname) :
     sysc_num (us_V U) <> UsysMemOk.USYS_wait -> ⊢ sysc_wait_out U r cs cs'.
@@ -533,9 +540,11 @@ Section SyscExec.
   Lemma sysc_wait_out_of (U : ustate) (r : mword 64) (rv : mword 32) (xs : Z)
       (cs cs' : gset gname) :
     r = (sign_extend' 64 rv : mword 64) ->
-    wait_ans rv xs cs cs' -∗ sysc_wait_out U r cs cs'.
+    wait_ans rv xs cs cs' (pv_gen (us_V U))
+      (bool_decide (pv_tf (us_V U) !!! tf_arg_idx 0 = (zero_reg : mword 64))) -∗
+    sysc_wait_out U r cs cs'.
   Proof.
-    intros ->. rewrite /sysc_wait_out /uwait_ans. iIntros "H %Hn".
+    intros ->. rewrite /sysc_wait_out /uwait_ans_at. iIntros "H %Hn".
     iExists rv, xs. iSplitR; [done | iExact "H"].
   Qed.
 
diff --git a/iris/SpecUsertrap.v b/iris/SpecUsertrap.v
index b2aa3208b..a75d901b8 100644
--- a/iris/SpecUsertrap.v
+++ b/iris/SpecUsertrap.v
@@ -129,6 +129,10 @@ Require Import ChildTok.   (* [child_tok] -- fork's answer to the parent *)
 Require Import UexecSG.        (* [uexecSG]: [sbundle] / [spost] / [skey_eq] *)
 Require Import UexecApply.     (* [uslot_key_cong] -- the slot across the re-key *)
 Require Import UexecExecInst.  (* the class INSTANCE: the process's exec bundle *)
+Require Import SpecSysRead.    (* [sys_rw_count] -- the read's count, for [ut_live_out] *)
+Require Import SpecArgfd.      (* [fd_st_of_key] -- the descriptor the read names *)
+Require Import ConsoleInv.     (* [CONSOLE] -- the device the read row is about *)
+Require Import StackOwn.       (* [uint_zero_reg] *)
 Require Import FirstTok.       (* [fsabs_env] -- what the loop mints the bundle from *)
 From Kernel Require KernelSyms.
 Require Import ProcAvail.
@@ -613,28 +617,195 @@ Qed.
 Definition ut_wait_out `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
     {SG : uexecSG Σ}
     (sc_v : mword 64) (tf : list (mword 64)) (r : mword 64)
-    (cs cs' : gset gname)
+    (cs cs' : gset gname) (gn : gname)
     : iProp Σ :=
   (⌜sc_v = uecall_scause /\ usys_num tf = USYS_wait⌝ -∗
-     uwait_ans r cs cs')%I.
+     uwait_ans_at r cs cs' gn
+       (bool_decide (tf !!! tf_arg_idx 0 = (zero_reg : mword 64))))%I.
 
 Lemma ut_wait_out_cong `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
     {SG : uexecSG Σ}
     (sc_v : mword 64) (tf1 tf2 : list (mword 64)) (r1 r2 : mword 64)
-    (cs cs' : gset gname) :
+    (cs cs' : gset gname) (gn : gname) :
   usys_num tf1 = usys_num tf2 -> r1 = r2 ->
-  ut_wait_out sc_v tf1 r1 cs cs' -∗ ut_wait_out sc_v tf2 r2 cs cs'.
+  tf1 !!! tf_arg_idx 0 = tf2 !!! tf_arg_idx 0 ->
+  ut_wait_out sc_v tf1 r1 cs cs' gn -∗ ut_wait_out sc_v tf2 r2 cs cs' gn.
 Proof.
-  intros Hn Hr. rewrite /ut_wait_out. subst r2. iIntros "H %Hc".
+  intros Hn Hr Ha0. rewrite /ut_wait_out. subst r2. rewrite Ha0.
+  iIntros "H %Hc".
   iApply "H". iPureIntro. split; [exact (proj1 Hc) |].
   rewrite Hn. exact (proj2 Hc).
 Qed.
 
+(* ...AND WHAT THE PROCESS IS HANDED.  The U tier cannot name the
+   incarnation ([UexecRet.uwait_ans]'s header), so the reason is absorbed
+   here -- it is delivered instead as the resume's own pure row
+   ([ut_live_out]).  (lane TRAP-ROWS, T4) *)
+Lemma ut_wait_out_forget `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
+    {SG : uexecSG Σ}
+    (sc_v : mword 64) (tf : list (mword 64)) (r : mword 64)
+    (cs cs' : gset gname) (gn : gname) :
+  ut_wait_out sc_v tf r cs cs' gn -∗
+  (⌜sc_v = uecall_scause /\ usys_num tf = USYS_wait⌝ -∗
+     uwait_ans r cs cs').
+Proof.
+  rewrite /ut_wait_out. iIntros "H %Hc".
+  iDestruct ("H" with "[%]") as "H"; [exact Hc |].
+  iApply (uwait_ans_of with "H").
+Qed.
+
+(* ===================================================================== *)
+(* WHAT THE RESUMING PROCESS LEARNS FROM ITS OWN SURVIVAL (lane            *)
+(* TRAP-ROWS, T2(iii) and T4).                                            *)
+(* ===================================================================== *)
+(* A PURE row, and it has to be: what the two kernel rows carry is the
+   incarnation's kill one-shot, and [UkRun.urun] binds the process's own
+   generation with no resource beside it -- the U tier cannot name it, so
+   the reason is absorbed at this boundary
+   ([ut_wait_out_forget], [UexecRet.uwait_ans]'s header) and what comes out
+   instead is what the shot's REFUTATION proves.
+     THE REFUTATION HAPPENS AT +0xa6.  usertrap's second [killed] check is
+   the one place a shot can be contradicted: at a zero flag <p->lock>'s row
+   holds the UNFIRED one-shot ([SchedCtx.kill_paid_shot_nz]), and
+   [ChildTok.kill_pend] is linear, so no refuter can be carried out of that
+   critical section.  A process that RESUMES therefore knows the shot was
+   never fired, and each of the two rows collapses to its other disjunct:
+
+     * THE READ.  At an open readable CONSOLE descriptor and a non-negative
+       count, [SpecFileread.console_receipt]'s -1 arm has exactly two
+       exits -- fileread's [n < 0] sign guard and consoleread's [killed]
+       test.  The shot is gone and the guard is refuted by the count, so
+       the surviving -1 cause AT AN OPEN READABLE CONSOLE FD IS [n < 0],
+       NOT A CLOSED FD: the arm is unreachable and the answer is not -1.
+     * WAIT.  At a NULL status pointer the failing arm's reason
+       ([UserChildren.wait_why]) has three disjuncts and the null pointer
+       kills the copyout one, so with the shot gone a -1 means the caller's
+       children column was EMPTY.
+
+   Both are read at the ENTRY trapframe and the ENTRY descriptor index --
+   the key the deposit went down at -- because that is what the process's
+   own returning arm is indexed by. *)
+(* WAIT'S HALF IS NOT HERE, AND THE REASON IS A GAP IN THE KERNEL'S OWN
+   ARM (lane TRAP-ROWS, T4).  The intended second clause was
+     [sc_v = uecall_scause -> usys_num tf = USYS_wait ->
+      uint (tf !!! tf_arg_idx 0) = 0 -> r = -1 -> cs' = ∅],
+   and it is TRUE but not derivable: refuting [r = -1] on
+   [UserChildren.wait_ans]'s REAPING arm needs the reaped child's pid to be
+   something other than -1, and nothing in the tree says so.  What a slot's
+   generation carries is [SlotGen.gen_halves_at] (SlotGen.v:393), i.e.
+   [bv_unsigned pid <> 0] and nothing more; the bound that would settle it,
+   [1 <= nextpid <= PIDMAX], lives in <pid_lock>'s payload
+   ([PidLock.nextpid_res_at], PidLock.v:127) and never travels to the
+   process block.  So the wait row's reason has to ride the ARM, where the
+   two exits are told apart by the reaping arm's own [ChildTok.exit_tok] --
+   see the lane's report.  The [cs'] parameter is kept so that clause can be
+   added here without re-cutting the route. *)
+Definition ut_live_out (sc_v : mword 64) (tf : list (mword 64))
+    (sts : list fdstate) (r : mword 64) (cs' : gset gname) : Prop :=
+  sc_v = uecall_scause -> usys_num tf = USYS_read ->
+  (0 <= sys_rw_count (tf !!! tf_arg_idx 2))%Z ->
+  forall rb : bool,
+    fd_st_of_key (tf !!! tf_arg_idx 0) sts
+      = FdOpen true rb (FdDevice CONSOLE) ->
+    r <> (mword_of_int (-1) : mword 64).
+
+(* THE TWO GUARDS, NAMED AND DECIDABLE.  usertrap's +0xa6 block proves the
+   row by REFUTING each guard against the unfired one-shot, and a refutation
+   needs the guard as a Coq case, not as an Iris hypothesis -- see
+   [ProofUsertrapTail.ut_a6]. *)
+Definition ut_live_fd_g (tf : list (mword 64)) (sts : list fdstate) : Prop :=
+  exists rb : bool,
+    fd_st_of_key (tf !!! tf_arg_idx 0) sts = FdOpen true rb (FdDevice CONSOLE).
+
+Global Instance ut_live_fd_g_dec (tf : list (mword 64)) (sts : list fdstate) :
+  Decision (ut_live_fd_g tf sts).
+Proof.
+  rewrite /ut_live_fd_g.
+  destruct (decide (fd_st_of_key (tf !!! tf_arg_idx 0) sts
+                    = FdOpen true true (FdDevice CONSOLE))) as [H1 | H1];
+    [ left; exists true; exact H1 | ].
+  destruct (decide (fd_st_of_key (tf !!! tf_arg_idx 0) sts
+                    = FdOpen true false (FdDevice CONSOLE))) as [H2 | H2];
+    [ left; exists false; exact H2 | ].
+  right. intros [rb Hrb]. destruct rb; [ exact (H1 Hrb) | exact (H2 Hrb) ].
+Defined.
+
+Definition ut_live_read_g (sc_v : mword 64) (tf : list (mword 64))
+    (sts : list fdstate) (r : mword 64) : Prop :=
+  sc_v = uecall_scause /\ usys_num tf = USYS_read
+  /\ (0 <= sys_rw_count (tf !!! tf_arg_idx 2))%Z
+  /\ ut_live_fd_g tf sts
+  /\ r = (mword_of_int (-1) : mword 64).
+
+Global Instance ut_live_read_g_dec sc_v tf sts r :
+  Decision (ut_live_read_g sc_v tf sts r).
+Proof. rewrite /ut_live_read_g. apply _. Defined.
+
+(* ...and the row, out of the refutation *)
+Lemma ut_live_out_of (sc_v : mword 64) (tf : list (mword 64))
+    (sts : list fdstate) (r : mword 64) (cs' : gset gname) :
+  ~ ut_live_read_g sc_v tf sts r ->
+  ut_live_out sc_v tf sts r cs'.
+Proof.
+  intros Hr He Hn Hc rb Hfd Hm1. apply Hr.
+  split_and!; [ exact He | exact Hn | exact Hc | exists rb; exact Hfd | exact Hm1 ].
+Qed.
+
+(* ...AND THE SAME ROW AT THE U TIER'S SPELLING (lane TRAP-ROWS, T2(iii)).
+   [UexecRet.uexec_live_ok] names the descriptor by INDEX, because
+   [SpecArgfd.fd_st_of_key] lives above that file; this is the one hop
+   between the two, and it is the [decide] in [fd_st_of_key] itself. *)
+Lemma uexec_live_ok_of_live (sc_v : mword 64) (tf : list (mword 64))
+    (sts : list fdstate) (r : mword 64) (cs' : gset gname) :
+  sc_v = uecall_scause ->
+  ut_live_out sc_v tf sts r cs' ->
+  UexecRet.uexec_live_ok (usys_num tf) tf sts r.
+Proof.
+  intros He H Hn Hc rb Hlt Hfd.
+  refine (H He Hn Hc rb _).
+  rewrite /fd_st_of_key. rewrite decide_True; [| exact Hlt].
+  rewrite Hfd. reflexivity.
+Qed.
+
+(* the row is FREE at a non-ecall cause: both clauses are guarded on it *)
+Lemma ut_live_out_ne (sc_v : mword 64) (tf : list (mword 64))
+    (sts : list fdstate) (r : mword 64) (cs' : gset gname) :
+  sc_v <> uecall_scause -> ut_live_out sc_v tf sts r cs'.
+Proof. intros Hne Hc. exfalso. exact (Hne Hc). Qed.
+
+(* ...and at any number that is not the read *)
+Lemma ut_live_out_num (sc_v : mword 64) (tf : list (mword 64))
+    (sts : list fdstate) (r : mword 64) (cs' : gset gname) :
+  usys_num tf <> USYS_read -> ut_live_out sc_v tf sts r cs'.
+Proof. intros Hr _ Hn. exfalso. exact (Hr Hn). Qed.
+
+(* the two readings the row is stated at do not move across the save walk,
+   so the row transports like [ut_wait_out_cong] does *)
+Lemma ut_live_out_cong (sc_v : mword 64) (tf1 tf2 : list (mword 64))
+    (sts : list fdstate) (r1 r2 : mword 64) (cs' : gset gname) :
+  usys_num tf1 = usys_num tf2 -> r1 = r2 ->
+  tf1 !!! tf_arg_idx 0 = tf2 !!! tf_arg_idx 0 ->
+  tf1 !!! tf_arg_idx 2 = tf2 !!! tf_arg_idx 2 ->
+  ut_live_out sc_v tf1 sts r1 cs' -> ut_live_out sc_v tf2 sts r2 cs'.
+Proof.
+  intros Hn Hr Ha0 Ha2 H1. subst r2.
+  intros He Hnum Hcnt rb Hfd. rewrite <- Ha0 in Hfd. rewrite <- Ha2 in Hcnt.
+  exact (H1 He ltac:(rewrite Hn; exact Hnum) Hcnt rb Hfd).
+Qed.
+
+(* [uint a1 = 0] is the null pointer the wait clause is conditioned on, in
+   the form the kernel's own row reads it at *)
+Lemma zero_reg_of_uint (x : mword 64) : uint x = 0%Z -> x = (zero_reg : mword 64).
+Proof.
+  intro H. apply bv_eq. rewrite <- !uint_unsigned.
+  rewrite uint_zero_reg. exact H.
+Qed.
+
 Lemma ut_wait_out_quiet `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
     {SG : uexecSG Σ}
     (sc_v : mword 64) (tf : list (mword 64)) (r : mword 64)
-    (cs cs' : gset gname) :
-  sc_v <> uecall_scause -> ⊢ ut_wait_out sc_v tf r cs cs'.
+    (cs cs' : gset gname) (gn : gname) :
+  sc_v <> uecall_scause -> ⊢ ut_wait_out sc_v tf r cs cs' gn.
 Proof.
   intros Hne. rewrite /ut_wait_out. iIntros "%Hc". exfalso.
   exact (Hne (proj1 Hc)).
@@ -643,8 +814,8 @@ Qed.
 Lemma ut_wait_out_quiet_n `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
     {SG : uexecSG Σ}
     (sc_v : mword 64) (tf : list (mword 64)) (r : mword 64)
-    (cs cs' : gset gname) :
-  usys_num tf <> USYS_wait -> ⊢ ut_wait_out sc_v tf r cs cs'.
+    (cs cs' : gset gname) (gn : gname) :
+  usys_num tf <> USYS_wait -> ⊢ ut_wait_out sc_v tf r cs cs' gn.
 Proof.
   intros Hne. rewrite /ut_wait_out. iIntros "%Hc". exfalso.
   exact (Hne (proj2 Hc)).
@@ -1399,7 +1570,13 @@ Definition usertrap_post `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fi
     (* ...AND WAIT'S: what the reap left the caller's reading -- see
        [ut_wait_out] *)
     ut_wait_out sc_v (<[tf_epc_idx := ret_pc sepc_v]> (pv_tf (us_V U)))
-      (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' -∗
+      (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' gn -∗
+    (* ...AND WHAT A RESUME ITSELF PROVES (lane TRAP-ROWS, T2(iii) / T4):
+       the two rows above answer at the incarnation, the process cannot
+       name it, and this is what survives the refutation -- see
+       [ut_live_out]. *)
+    ⌜ut_live_out sc_v (<[tf_epc_idx := ret_pc sepc_v]> (pv_tf (us_V U)))
+        sts (pv_tf (us_V U') !!! tf_arg_idx 0) cs'⌝ -∗
     (* ...AND THE UNTAKEN CONTINUATION (lane TRAP-ROWS, T3): at a non-ecall
        cause the process handed the kernel the additive pair, and a resume
        means the kernel took the RIGHT side and owes it back -- at the key
diff --git a/iris/SpecUservec.v b/iris/SpecUservec.v
index 361172115..540664682 100644
--- a/iris/SpecUservec.v
+++ b/iris/SpecUservec.v
@@ -385,7 +385,11 @@ Definition uservec_post `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ} `{GEN
       (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' -∗
     (* ...AND WAIT'S, forwarded the same way -- [SpecUsertrap.ut_wait_out] *)
     ut_wait_out sc_v (tf_of g (ret_pc sepc_v))
-      (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' -∗
+      (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' gn -∗
+    (* ...AND WHAT A RESUME PROVES, forwarded the same way (lane TRAP-ROWS,
+       T2(iii) / T4) -- [SpecUsertrap.ut_live_out] *)
+    ⌜ut_live_out sc_v (tf_of g (ret_pc sepc_v)) sts
+        (pv_tf (us_V U') !!! tf_arg_idx 0) cs'⌝ -∗
     (* ...AND THE UNTAKEN CONTINUATION, forwarded the same way (lane
        TRAP-ROWS, T3) -- [SpecUsertrap.ut_kill_out] *)
     ut_kill_out sc_v Wk -∗
diff --git a/iris/UexecApply.v b/iris/UexecApply.v
index a526d79de..a2374b63a 100644
--- a/iris/UexecApply.v
+++ b/iris/UexecApply.v
@@ -525,10 +525,10 @@ Section Apply.
          sets and no trapframe word, so it transports on the nose. *)
       destruct (decide (usys_num (uvis_tf W') = USYS_wait)) as [_ | _].
       { iSplit.
-        + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio Hcho Hsp".
+        + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio %Hlo Hcho Hsp".
           rewrite -(Hb r M' pi' szv' fdv' cw' gn' cs').
           iApply ("H" $! r M' pi' szv' fdv' cw' gn' cs'
-                    with "[%] [%] [%] [%] [%] [%] [Hcho] [Hsp]").
+                    with "[%] [%] [%] [%] [%] [%] [%] [Hcho] [Hsp]").
           * exact (usys_mem_ok_args _ (uvis_tf W') (uvis_tf W) r _ _ _ _ _ _ _ _
                      (eq_sym Ha0) (eq_sym Ha1) (eq_sym Ha2) Hmo).
           * exact (usys_fd_ok_arg_cong _ (uvis_tf W') (uvis_tf W) _ _ _
@@ -538,14 +538,15 @@ Section Apply.
           * exact Hco.
           * exact Hgo.
           * exact Hpio.
+          * exact (uexec_live_ok_cong _ _ _ _ _ (eq_sym Ha0) (eq_sym Ha2) Hlo).
           * iExact "Hcho".
           * iEval (rewrite (spost_at_cong S (usys_num (uvis_tf W')) f W' W r
                               M' fdv' cw' cs' (skey_eq_sym W W' Hsk))) in "Hsp".
             iExact "Hsp".
-        + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio Hcho Hsp".
+        + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio %Hlo Hcho Hsp".
           rewrite (Hb r M' pi' szv' fdv' cw' gn' cs').
           iApply ("H" $! r M' pi' szv' fdv' cw' gn' cs'
-                    with "[%] [%] [%] [%] [%] [%] [Hcho] [Hsp]").
+                    with "[%] [%] [%] [%] [%] [%] [%] [Hcho] [Hsp]").
           * exact (usys_mem_ok_args _ (uvis_tf W) (uvis_tf W') r _ _ _ _ _ _ _ _
                      Ha0 Ha1 Ha2 Hmo).
           * exact (usys_fd_ok_arg_cong _ (uvis_tf W) (uvis_tf W') _ _ _
@@ -555,15 +556,16 @@ Section Apply.
           * exact Hco.
           * exact Hgo.
           * exact Hpio.
+          * exact (uexec_live_ok_cong _ _ _ _ _ Ha0 Ha2 Hlo).
           * iExact "Hcho".
           * iEval (rewrite (spost_at_cong S (usys_num (uvis_tf W')) f W W' r
                               M' fdv' cw' cs' Hsk)) in "Hsp". iExact "Hsp". } 
     (* the returning arms: the row transports by SS3 *)
       iSplit.
-      + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio %Hcho Hsp".
+      + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio %Hlo %Hcho Hsp".
         rewrite -(Hb r M' pi' szv' fdv' cw' gn' cs').
         iApply ("H" $! r M' pi' szv' fdv' cw' gn' cs'
-                  with "[%] [%] [%] [%] [%] [%] [%] [Hsp]").
+                  with "[%] [%] [%] [%] [%] [%] [%] [%] [Hsp]").
         * exact (usys_mem_ok_args _ (uvis_tf W') (uvis_tf W) r _ _ _ _ _ _ _ _
                    (eq_sym Ha0) (eq_sym Ha1) (eq_sym Ha2) Hmo).
         * exact (usys_fd_ok_arg_cong _ (uvis_tf W') (uvis_tf W) _ _ _
@@ -577,16 +579,17 @@ Section Apply.
            and neither does the pid's *)
         * exact Hgo.
         * exact Hpio.
+        * exact (uexec_live_ok_cong _ _ _ _ _ (eq_sym Ha0) (eq_sym Ha2) Hlo).
         * exact Hcho.
         (* ...and the armed post transports by the SAME key rows the
            deposit does ([UexecSG.skey_eq]) *)
         * iEval (rewrite (spost_at_cong S (usys_num (uvis_tf W')) f W' W r
                             M' fdv' cw' cs' (skey_eq_sym W W' Hsk))) in "Hsp".
           iExact "Hsp".
-      + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio %Hcho Hsp".
+      + iIntros "H" (r M' pi' szv' fdv' cw' gn' cs' lz') "%Hmo %Hfo %Hpo %Hco %Hgo %Hpio %Hlo %Hcho Hsp".
         rewrite (Hb r M' pi' szv' fdv' cw' gn' cs').
         iApply ("H" $! r M' pi' szv' fdv' cw' gn' cs'
-                  with "[%] [%] [%] [%] [%] [%] [%] [Hsp]").
+                  with "[%] [%] [%] [%] [%] [%] [%] [%] [Hsp]").
         * exact (usys_mem_ok_args _ (uvis_tf W) (uvis_tf W') r _ _ _ _ _ _ _ _
                    Ha0 Ha1 Ha2 Hmo).
         * exact (usys_fd_ok_arg_cong _ (uvis_tf W) (uvis_tf W') _ _ _
@@ -596,6 +599,7 @@ Section Apply.
         * exact Hco.
         * exact Hgo.
         * exact Hpio.
+        * exact (uexec_live_ok_cong _ _ _ _ _ Ha0 Ha2 Hlo).
         * exact Hcho.
         * iEval (rewrite (spost_at_cong S (usys_num (uvis_tf W')) f W W' r
                             M' fdv' cw' cs' Hsk)) in "Hsp". iExact "Hsp".
@@ -877,6 +881,10 @@ Section LoopApply.
        ([UsysMemOk.usys_ret_pid_ne]). *)
     usys_ret_pid (usys_num (uvis_tf (uvis_run W)))
       (uvis_tf W' !!! tf_arg_idx 0) (uvis_pid W) ->
+    (* ...AND WHAT THE RESUME ITSELF PROVES (lane TRAP-ROWS, T2(iii)), read
+       at the same outgoing a0 word -- [UexecRet.uexec_live_ok]. *)
+    uexec_live_ok (usys_num (uvis_tf (uvis_run W))) (uvis_tf (uvis_run W))
+      (uvis_fd W) (uvis_tf W' !!! tf_arg_idx 0) ->
     (* ...and the resume key's pid is the trapped key's, exactly as its
        generation is: nothing re-numbers the caller, so the loop builds the
        resume key at the pid it resumed the process with. *)
@@ -908,13 +916,15 @@ Section LoopApply.
        ⌜usys_cwd_ok (usys_num (uvis_tf (uvis_run W))) r' (uvis_cwd W) cw'⌝ -∗
        ⌜usys_gen_ok (usys_num (uvis_tf (uvis_run W))) (uvis_gen W) gn'⌝ -∗
        ⌜usys_ret_pid (usys_num (uvis_tf (uvis_run W))) r' (uvis_pid W)⌝ -∗
+       ⌜uexec_live_ok (usys_num (uvis_tf (uvis_run W))) (uvis_tf (uvis_run W))
+                      (uvis_fd W) r'⌝ -∗
        CH r' cs' -∗
        spost_at S (usys_num (uvis_tf (uvis_run W))) f (uvis_run W) r'
          M' fdv' cw' cs' -∗
        S (bump (uvis_run W) r' M' π' szv' fdv' cw' gn' cs' lz')) -∗
     S W'.
   Proof.
-    intros Hl Hgn [Hb1 Hb2] Hm Hfdrow Hpiperow Hcwrow Hpidrow Hpidk.
+    intros Hl Hgn [Hb1 Hb2] Hm Hfdrow Hpiperow Hcwrow Hpidrow Hliverow Hpidk.
     iIntros "Hch Hsp Hret".
     (* the two length side conditions the bump's readers take *)
     assert (Hla : (tf_arg_idx 0 < length (uvis_tf (uvis_run W)))%nat)
@@ -953,10 +963,11 @@ Section LoopApply.
     iDestruct ("Hret" $! r (uvis_M W') (uvis_perm W') (uvis_sz W')
                  (uvis_fd W') (uvis_cwd W') (uvis_gen W') (uvis_ch W')
                  (uvis_lazy W')
-                 with "[%] [%] [%] [%] [%] [%] Hch Hsp") as "Hs";
+                 with "[%] [%] [%] [%] [%] [%] [%] Hch Hsp") as "Hs";
       [ exact Hm | rewrite <- Ha0; exact Hfdrow
       | rewrite <- Ha0; exact Hpiperow | exact Hcwrow
-      | exact Hgn | rewrite <- Ha0; exact Hpidrow | ].
+      | exact Hgn | rewrite <- Ha0; exact Hpidrow
+      | rewrite <- Ha0; exact Hliverow | ].
     assert (Hp1 : tf_resume_pc (bump_tf (uvis_tf (uvis_run W)) r)
                   = tf_resume_pc (uvis_tf W')).
     { rewrite (tf_resume_pc_bump (uvis_tf (uvis_run W)) r Hle).
@@ -1023,6 +1034,15 @@ Section LoopApply.
     (sc = uecall_scause ->
        usys_ret_pid (usys_num (uvis_tf (uvis_run W)))
          (uvis_tf W' !!! tf_arg_idx 0) (uvis_pid W)) ->
+    (* ...AND WHAT THE RESUME ITSELF PROVES (lane TRAP-ROWS, T2(iii)), on
+       the same terms and by the same route: usertrap's second [killed]
+       check refuted the read's one-shot, so at an open readable console
+       descriptor the answer is not -1 -- [SpecUsertrap.ut_live_out], off
+       [SpecUservec]'s post.  Guarded on the ecall like the pid row; the
+       transparent arm answers nothing. *)
+    (sc = uecall_scause ->
+       uexec_live_ok (usys_num (uvis_tf (uvis_run W))) (uvis_tf (uvis_run W))
+         (uvis_fd W) (uvis_tf W' !!! tf_arg_idx 0)) ->
     (* THE CWD ROWS RIDE INSIDE THE ROUND: [uround_ok] relates the key's
        [uvis_cwd] on both sides, so nothing here has to be told about it
        separately -- the transparent arm pins it, the returning arm reads
@@ -1093,7 +1113,7 @@ Section LoopApply.
     (if decide (sc = uecall_scause) then uexec_arm sc W f
      else uslot (uvis_run W)) -∗ uslot W'.
   Proof.
-    intros Hl Hgn Hpidk Hch Hfd Hfdrow Hpiperow Hpidrow Hr.
+    intros Hl Hgn Hpidk Hch Hfd Hfdrow Hpiperow Hpidrow Hliverow Hr.
     iIntros "Hxo Hfo Hwo Hsp Hret".
     destruct (decide (sc = uecall_scause)) as [Hec | Hne].
     - (* ---- ECALL ---- *)
@@ -1137,7 +1157,8 @@ Section LoopApply.
                        ⌜usys_ch_ok (usys_num (uvis_tf (uvis_run W))) r'
                           (uvis_ch W) cs2⌝%I)
                     Hl Hgn Hb Hm
-                    (Hfdrow Hec) (Hpiperow Hec) Hc (Hpidrow Hec) Hpidk
+                    (Hfdrow Hec) (Hpiperow Hec) Hc (Hpidrow Hec)
+                    (Hliverow Hec) Hpidk
                     with "[] [Hsp] [Hret]").
           (* the children row: this arm is not one of the two that move it *)
           { iPureIntro. exact Hchq. }
@@ -1264,7 +1285,8 @@ Section LoopApply.
                        (fun (r' : mword 64) (cs2 : gset gname) =>
                           uwait_ans r' (uvis_ch W) cs2)
                        Hl Hgn Hb Hm
-                       (Hfdrow Hec) (Hpiperow Hec) Hc (Hpidrow Hec) Hpidk
+                       (Hfdrow Hec) (Hpiperow Hec) Hc (Hpidrow Hec)
+                    (Hliverow Hec) Hpidk
                        with "[Hwo] [Hsp] [Hret]").
              { iApply "Hwo". iPureIntro. split; [exact Hec | exact Hwt]. }
              { iExact "Hsp". }
@@ -1277,7 +1299,8 @@ Section LoopApply.
                           ⌜usys_ch_ok (usys_num (uvis_tf (uvis_run W))) r'
                              (uvis_ch W) cs2⌝%I)
                        Hl Hgn Hb Hm
-                       (Hfdrow Hec) (Hpiperow Hec) Hc (Hpidrow Hec) Hpidk
+                       (Hfdrow Hec) (Hpiperow Hec) Hc (Hpidrow Hec)
+                    (Hliverow Hec) Hpidk
                        with "[] [Hsp] [Hret]").
              { iPureIntro. exact Hchq. }
              { iExact "Hsp". }
@@ -1347,6 +1370,12 @@ Section LoopApply.
     (sc = uecall_scause ->
        usys_ret_pid (usys_num (tf_of g (ret_pc sepc_v)))
          (pv_tf (us_V U') !!! tf_arg_idx 0) (uvis_pid W)) ->
+    (* ...and WHAT THE RESUME PROVES, forwarded the same way (lane
+       TRAP-ROWS, T2(iii)) -- see [uexec_ret_round_slot] *)
+    (sc = uecall_scause ->
+       uexec_live_ok (usys_num (tf_of g (ret_pc sepc_v)))
+         (tf_of g (ret_pc sepc_v)) (uvis_fd W)
+         (pv_tf (us_V U') !!! tf_arg_idx 0)) ->
     (* ...and the round's cwd ends are the key's and the RECORD's: the
        inum rides inside the block, so the resumed key's [uvis_cwd] is
        [pv_cwi (us_V U')] by [uvis_of] itself -- no view to choose *)
@@ -1386,13 +1415,14 @@ Section LoopApply.
      else uslot (uvis_run W)) -∗
     uslot (uvis_of U' fdv' (uvis_gen W) cs' (uvis_pid W)).
   Proof.
-    intros Hl -> -> Hfd Hchrow Hfdrow Hpiperow Hpidrow Hr.
+    intros Hl -> -> Hfd Hchrow Hfdrow Hpiperow Hpidrow Hliverow Hr.
     (* THE RESUME KEY IS BUILT AT THE TRAPPED KEY'S OWN GENERATION -- no
        entry re-incarnates its caller -- AND AT ITS OWN PID, for the same
        reason -- and at the set the loop passes. *)
     exact (uexec_ret_round_slot sc W
              (uvis_of U' fdv' (uvis_gen W) cs' (uvis_pid W))
-             f Hl eq_refl eq_refl Hchrow Hfd Hfdrow Hpiperow Hpidrow Hr).
+             f Hl eq_refl eq_refl Hchrow Hfd Hfdrow Hpiperow Hpidrow
+             Hliverow Hr).
   Qed.
 
   (* ------------------------------------------------------------------ *)
diff --git a/iris/UexecExecInst.v b/iris/UexecExecInst.v
index 1b75f96aa..17ecbfca2 100644
--- a/iris/UexecExecInst.v
+++ b/iris/UexecExecInst.v
@@ -1408,6 +1408,39 @@ Section UexecExecInst.
     iSplitR; [by iPureIntro |]. iExact "H".
   Qed.
 
+  (* ...AND THE READ ROW'S REASON, READ OFF THE POST WITHOUT SPENDING IT
+     (lane TRAP-ROWS, T2(ii)).  Both disjuncts are persistent, so the post
+     comes straight back; usertrap's second [killed] check refutes the
+     right one against <p->lock>'s own row and is left with the sign
+     guard. *)
+  Lemma spost_at_read_why (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
+      (rb : bool) (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
+      (cw' : Z) (cs' : gset gname) :
+    fd_st_of_key (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W)
+      = FdOpen true rb (FdDevice ConsoleInv.CONSOLE) ->
+    r = (mword_of_int (-1) : mword 64) ->
+    spost_at X 5 f W r M' fdv' cw' cs' -∗
+    (⌜(sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2)) < 0)%Z⌝
+     ∨ ChildTok.kill_shot (uvis_gen W)) ∗
+    spost_at X 5 f W r M' fdv' cw' cs'.
+  Proof.
+    intros Hfd Hr.
+    pose proof (sys_rw_count_lt (tf_w (uvis_tf W) (tf_arg_idx 2))) as Hlt.
+    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
+    xv6_take.
+    iDestruct "H" as "(%Hret & %P & %Hpm & %Hwf & %Hlz & Hcore)".
+    rewrite Hfd.
+    iDestruct (fileread_extra_core_m1_why (uvis_gen W) P rb
+                 (sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2)))
+                 (rf_F f) (rf_ret f) (rf_in f) r M'
+                 (tf_w (uvis_tf W) (tf_arg_idx 1)) Hlt Hr
+                 with "Hcore") as "(#Hwhy & Hcore)".
+    iSplitR "Hcore"; [ iExact "Hwhy" | ].
+    iSplitR; [by iPureIntro |]. iExists P.
+    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
+    iSplitR; [by iPureIntro |]. iExact "Hcore".
+  Qed.
+
   (* ...and chdir's, at the working directory the call RESUMES at: the arm
      the dispatcher splits ([SpecSysChdir.chdir_arms_split]) hands the
      kernel half back and this the process's. *)
diff --git a/iris/UexecRet.v b/iris/UexecRet.v
index 4863a36a5..8aacbcf2e 100644
--- a/iris/UexecRet.v
+++ b/iris/UexecRet.v
@@ -1005,9 +1005,26 @@ Section UexecRet.
      is READ and not chosen, exactly as fork's is: the row is
      [WaitInv.ch_frag] off the kernel's residue and kwait moves it under
      <wait_lock>. *)
-  Definition uwait_ans (r : mword 64) (cs cs' : gset gname) : iProp Σ :=
+  (* ...AT THE CALLER'S GENERATION AND ITS STATUS POINTER (lane TRAP-ROWS,
+     T4): what the kernel's own channels carry, because the -1 arm's reason
+     names the incarnation and is guarded on the null pointer. *)
+  Definition uwait_ans_at (r : mword 64) (cs cs' : gset gname)
+      (gn : gname) (nullst : bool) : iProp Σ :=
     (∃ (rv : mword 32) (xs : Z),
-       ⌜r = (sign_extend' 64 rv : mword 64)⌝ ∗ wait_ans rv xs cs cs')%I.
+       ⌜r = (sign_extend' 64 rv : mword 64)⌝ ∗
+       wait_ans rv xs cs cs' gn nullst)%I.
+
+  (* ...AND WHAT THE PROCESS SEES.  [urun] binds the process's own
+     generation with NO resource beside it (UkRun.v's note), so the U tier
+     cannot name it -- the reason is ABSORBED here and delivered instead as
+     the resume's own pure row ([SpecUsertrap.ut_live_out]). *)
+  Definition uwait_ans (r : mword 64) (cs cs' : gset gname) : iProp Σ :=
+    (∃ (gn : gname) (b : bool), uwait_ans_at r cs cs' gn b)%I.
+
+  Lemma uwait_ans_of (r : mword 64) (cs cs' : gset gname)
+      (gn : gname) (b : bool) :
+    uwait_ans_at r cs cs' gn b -∗ uwait_ans r cs cs'.
+  Proof. iIntros "H". iExists gn, b. iExact "H". Qed.
 
   (* the failing arm, at the word the [li -1] tails leave in a0 *)
   Lemma sext_neg1_64 :
@@ -1015,19 +1032,27 @@ Section UexecRet.
     = (mword_of_int (-1) : mword 64).
   Proof. apply bv_eq; vm_compute; reflexivity. Qed.
 
+  Lemma uwait_ans_at_neg1 (cs : gset gname) (gn : gname) (b : bool) :
+    (⌜b = false⌝ ∨ ⌜cs = (∅ : gset gname)⌝ ∨ ChildTok.kill_shot gn) -∗
+    uwait_ans_at (mword_of_int (-1) : mword 64) cs cs gn b.
+  Proof.
+    iIntros "Hwhy". iExists (mword_of_int (-1) : mword 32), 0%Z.
+    iSplitR; [iPureIntro; symmetry; exact sext_neg1_64 |].
+    iApply (wait_ans_neg with "Hwhy").
+  Qed.
+
   Lemma uwait_ans_neg1 (cs : gset gname) :
     ⊢ uwait_ans (mword_of_int (-1) : mword 64) cs cs.
   Proof.
-    iExists (mword_of_int (-1) : mword 32), 0%Z.
-    iSplitR; [iPureIntro; symmetry; exact sext_neg1_64 |].
-    iApply wait_ans_neg.
+    iExists inhabitant, false.
+    iApply uwait_ans_at_neg1. by iLeft.
   Qed.
 
   (* ...and the pure row, for the relays that only want the set's move *)
   Lemma uwait_ans_reaped (r : mword 64) (cs cs' : gset gname) :
     uwait_ans r cs cs' -∗ ⌜ch_reaped cs cs'⌝.
   Proof.
-    iIntros "H". iDestruct "H" as (rv xs) "[_ Ha]".
+    iIntros "H". iDestruct "H" as (gn b rv xs) "[_ Ha]".
     iApply (wait_ans_reaped with "Ha").
   Qed.
 
@@ -1222,6 +1247,45 @@ Section UexecRet.
     iApply ("H" with "Hp HRc").
   Qed.
 
+  (* WHAT A RESUME PROVES ABOUT THE CONSOLE READ (lane TRAP-ROWS, T2(iii)).
+     See [uexec_ret_cont_gen]'s own note for why it is true; the shape here
+     is the U tier's: the count is the a2 word read as a C [int]
+     ([SpecSysRead.sys_rw_count]'s spelling), the descriptor is the a0 word
+     read as an index into the caller's own table
+     ([SpecArgfd.fd_st_of_key]'s two cases, split out so that neither
+     definition has to travel down here), and CONSOLE is major 1
+     ([ConsoleInv.CONSOLE]). *)
+  Definition uexec_live_ok (n : Z) (tf : list (mword 64))
+      (sts : list fdstate) (r : mword 64) : Prop :=
+    n = USYS_read ->
+    (0 <= bv_signed (trunc32 (tf_w tf (tf_arg_idx 2))))%Z ->
+    forall rb : bool,
+      (0 <= usys_argfd tf < Z.of_nat NOFILE)%Z ->
+      sts !! Z.to_nat (usys_argfd tf) = Some (FdOpen true rb (FdDevice 1)) ->
+      r <> (mword_of_int (-1) : mword 64).
+
+  (* free at every number but the read *)
+  Lemma uexec_live_ok_ne (n : Z) (tf : list (mword 64))
+      (sts : list fdstate) (r : mword 64) :
+    n <> USYS_read -> uexec_live_ok n tf sts r.
+  Proof. intros Hne Hn. exfalso. exact (Hne Hn). Qed.
+
+  (* ...and it reads two trapframe words and nothing else, so it transports
+     across a re-key like the other pure rows ([UexecSG.skey_eq] fixes both) *)
+  Lemma uexec_live_ok_cong (n : Z) (tf1 tf2 : list (mword 64))
+      (sts : list fdstate) (r : mword 64) :
+    tf_w tf1 (tf_arg_idx 0) = tf_w tf2 (tf_arg_idx 0) ->
+    tf_w tf1 (tf_arg_idx 2) = tf_w tf2 (tf_arg_idx 2) ->
+    uexec_live_ok n tf1 sts r -> uexec_live_ok n tf2 sts r.
+  Proof.
+    intros Ha0 Ha2 H Hn Hc rb Hlt Hfd.
+    rewrite <- Ha2 in Hc.
+    rewrite /tf_w in Ha0.
+    rewrite /usys_argfd in Hlt, Hfd.
+    rewrite <- Ha0 in Hlt, Hfd.
+    exact (H Hn Hc rb Hlt Hfd).
+  Qed.
+
   (* the returning arm's CONTINUATION: the four pure rows, the syscall's
      armed post [spost_at] -- what the process gets back for the bundle it
      deposited -- and the next slot at the bumped key.
@@ -1280,6 +1344,23 @@ Section UexecRet.
           from [SpecSysGetpid]'s own post.  LAST among the pure rows, so
           every existing intro pattern keeps working. *)
        ⌜usys_ret_pid n r (uvis_pid W)⌝ -∗
+       (* ...AND WHAT THE RESUME ITSELF PROVES (lane TRAP-ROWS, T2(iii)).
+          A process that comes back HERE was not killed, and usertrap's
+          second [killed] check is where that is cashed: at a zero flag
+          <p->lock>'s row holds the UNFIRED one-shot
+          ([SchedCtx.kill_paid_shot_nz]), which refutes the [kill_shot]
+          disjunct of [SpecFileread.console_receipt]'s -1 arm.  With the
+          shot gone the arm has exactly one cause left, fileread's [n < 0]
+          sign guard, and a caller that asked for a non-negative count has
+          ruled that out too -- so AT AN OPEN READABLE CONSOLE DESCRIPTOR
+          the read did not return -1.  [SpecUsertrap.ut_live_out] is this
+          at the kernel's own spelling and [ProofUserretClosed] is the one
+          hop between them.
+          READ AT THE TRAPPING KEY's descriptor view and argument words,
+          which is what the caller holds.  The descriptor is named by INDEX
+          rather than through [SpecArgfd.fd_st_of_key]: that lives above
+          this file, and a program holds its table as a list. *)
+       ⌜uexec_live_ok n (uvis_tf W) (uvis_fd W) r⌝ -∗
        (* ...AND THE CHILDREN SET, off the same return value: the row the
           number's own answer carries -- pure and quiet at the twenty
           entries that keep the reading, [uwait_ans] at wait, which reaps. *)
@@ -1998,6 +2079,8 @@ Section UexecRet.
            ⌜usys_cwd_ok n r (uvis_cwd W) cw'⌝ -∗
            ⌜usys_gen_ok n (uvis_gen W) g'⌝ -∗
            ⌜usys_ret_pid n r (uvis_pid W)⌝ -∗
+           (* ...and what the resume proves (lane TRAP-ROWS, T2(iii)) *)
+           ⌜uexec_live_ok n (uvis_tf W) (uvis_fd W) r⌝ -∗
            uwait_ans r (uvis_ch W) cs' -∗
            spost_at uslot n f W r M' fdv' cw' cs' -∗
            uslot (bump W r M' π' szv' fdv' cw' g' cs' lz')))
@@ -2024,6 +2107,8 @@ Section UexecRet.
            ⌜usys_cwd_ok n r (uvis_cwd W) cw'⌝ -∗
            ⌜usys_gen_ok n (uvis_gen W) g'⌝ -∗
            ⌜usys_ret_pid n r (uvis_pid W)⌝ -∗
+           (* ...and what the resume proves (lane TRAP-ROWS, T2(iii)) *)
+           ⌜uexec_live_ok n (uvis_tf W) (uvis_fd W) r⌝ -∗
            ⌜usys_ch_ok n r (uvis_ch W) cs'⌝ -∗
            spost_at uslot n f W r M' fdv' cw' cs' -∗
            uslot (bump W r M' π' szv' fdv' cw' g' cs' lz'))))).
@@ -2324,11 +2409,11 @@ Section UexecRet.
        process reads neither: the answer is dropped like the receipt. *)
     destruct (decide (usys_num (uvis_tf W) = USYS_wait)).
     { rewrite /uexec_wait_F /uexec_ret_cont_gen.
-      iIntros (r M' π' szv' fdv' cw' g' cs' lz' _ _ _ _ Hg _) "_ _".
+      iIntros (r M' π' szv' fdv' cw' g' cs' lz' _ _ _ _ Hg _ _) "_ _".
       rewrite (usys_gen_ok_quiet _ _ _ Hg). iApply ("H" with "[] HR").
       cbn [uvis_gen bump bump_at]. iExact "Hpay". }
     rewrite /uexec_ret_cont_F /uexec_ret_cont_gen.
-    iIntros (r M' π' szv' fdv' cw' g' cs' lz' _ _ _ _ Hg _ _) "_".
+    iIntros (r M' π' szv' fdv' cw' g' cs' lz' _ _ _ _ Hg _ _ _) "_".
     rewrite (usys_gen_ok_quiet _ _ _ Hg). iApply ("H" with "[] HR").
     cbn [uvis_gen bump bump_at]. iExact "Hpay".
   Qed.
diff --git a/iris/UkRunMem.v b/iris/UkRunMem.v
index ba7b96b12..976eb5f66 100644
--- a/iris/UkRunMem.v
+++ b/iris/UkRunMem.v
@@ -412,13 +412,18 @@ Section UkRunMem.
   Lemma wp_uk_sb_denied (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
       (imm : mword 12) (rs1 rs2 : mword 5) (a : Z) (b0 : bv 8) (avail : nat) :
     a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
-    (⊢ ukn_pay N (-1)) ->
     uinstr_is (ukn_t N) pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
     utext (ukn_t N) a b0 -∗
     urun N h m pc avail -∗
+    (* THE PAYLOAD AT THE KILL STATUS, AS A RESOURCE (the IO-LEAF review).
+       It used to be the Coq-level [⊢ ukn_pay N (-1)] -- "the payload is
+       free" -- which a child that dies at a LINEAR payload cannot supply;
+       a caller that still has the free payload derives this in one
+       [iPoseProof] ([UkRun.ukn_pay_free_of_triv]). *)
+    ukn_pay N (-1) -∗
     WP (Loop : expr riscv_lang).
   Proof.
-    intros Ha Hpay. iIntros "#Hi #Ht Hrun".
+    intros Ha. iIntros "#Hi #Ht Hrun Hpay".
     iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & Hb)".
     iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
     iDestruct (uheap_text with "Hheap Ht") as %(HM & Hx & Hbnd).
@@ -435,7 +440,7 @@ Section UkRunMem.
       exfalso. apply Hnw. exists q. exact (conj Hq Ew). }
     iApply (UkStore.wp_uk_sb_denied C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc
               fdv cw gn cs pidv imm rs1 rs2 (mword_of_int a) (m !!! Regidx rs2)
-              Hui Htgt eq_refl Hden Hcan Hpay with "Hb Hmy").
+              Hui Htgt eq_refl Hden Hcan with "Hb Hmy Hpay").
   Qed.
 
   Lemma wp_uk_ld (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
diff --git a/iris/UkRunSys.v b/iris/UkRunSys.v
index d4474d884..daee4a37b 100644
--- a/iris/UkRunSys.v
+++ b/iris/UkRunSys.v
@@ -600,7 +600,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -729,7 +729,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -891,7 +891,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1061,7 +1061,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1215,7 +1215,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1375,7 +1375,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1527,7 +1527,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1636,7 +1636,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1762,7 +1762,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -1914,7 +1914,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -2058,7 +2058,7 @@ Section UkRunSys.
        to be [emp] and is a wand from "the answer was -1" now
        ([UexecSG.spost_at_exec]), which is exactly the branch this leaf is
        on -- a successful exec never resumes here. *)
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hsp".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hsp".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -2184,7 +2184,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow Hans _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow Hans _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -2368,7 +2368,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -2575,7 +2575,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -2933,6 +2933,18 @@ Section UkRunSys.
           eliminates [ConsoleInv.cons_swallow]'s copyout-fault disjunct by
           [uk_read_nofault] above. *)
        ⌜uvis_lazy W = false⌝ -∗
+       (* ...AND THE ANSWER IS NOT -1 (lane TRAP-ROWS, T2(iii)).  A process
+          that resumes was not killed, and usertrap's second [killed] check
+          is where that is cashed: with the one-shot refuted,
+          [SpecFileread.console_receipt]'s -1 arm has exactly one cause
+          left, fileread's [n < 0] sign guard, and a caller that asked for
+          a non-negative count has ruled that out too.  So AT AN OPEN
+          READABLE CONSOLE DESCRIPTOR the read did not fail -- and the
+          reason the row is guarded rather than flat is that a caller whose
+          fd is closed, or not the console, or whose count is negative, HAS
+          no such fact.  [UexecRet.uexec_live_ok] names the descriptor by
+          index, which is the form a program holding its own table wants. *)
+       ⌜uexec_live_ok USYS_read (uvis_tf W) (uvis_fd W) r⌝ -∗
        (* the ledger comes straight back: read moves no descriptor *)
        UserFd.ustd (ukn_fd N) l -∗
        (* THE POST, AT THE TRAPPING KEY AND THE RESUME IMAGE *)
@@ -3015,7 +3027,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -3071,7 +3083,7 @@ Section UkRunSys.
     { iIntros (h'') "Hrun".
       iApply ("Hcont" $! h'' r d g (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
                 _ _ _ _
-                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hstd Hpost Hrun Hbuf").
+                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hstd Hpost Hrun Hbuf").
       - exact Hdcap.
       - intros j Hj. apply Hgf; lia.
       (* the destination run is linear, off the ownership of the buffer *)
@@ -3097,7 +3109,10 @@ Section UkRunSys.
       - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc).
       - rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false). exact Htake.
       (* definitional: the run is at [false] *)
-      - reflexivity. }
+      - reflexivity.
+      (* ...and what the resume proved, straight off the arm's own row
+         (lane TRAP-ROWS, T2(iii)) *)
+      - exact Hliverow. }
     iDestruct (ukcq_ukc with "Hkc") as "Hkc".
     iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb'");
       [ exact Hlo' | exact Hpm' | exact Hlzf' ].
@@ -3245,7 +3260,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -3397,7 +3412,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -3651,7 +3666,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     (* THE LAZY BIT, THE CWD, THE GENERATION AND THE CHILDREN ALL CROSSED
        THE TRAP UNCHANGED: 16 is none of the rows that move them. *)
     assert (Hlzq : lz' = false)
@@ -3850,7 +3865,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     assert (Hlzq : lz' = false)
       by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
           vm_compute; discriminate).
@@ -4003,7 +4018,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -4144,7 +4159,7 @@ Section UkRunSys.
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
     iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
-      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow Hpost".
+      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
     (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
        trapping key is at [false] -- the U tier's run is
        ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
@@ -4339,7 +4354,7 @@ Section UkRunSys.
     cbn [uvis_gen uvis_of_run].
     iSplitR; [ iFrame "Hmy" | ].
     iSplitL "Hdepn"; [ iExact "Hdepn" | ].
-    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hchrow _".
+    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow _".
     (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
        it, and this is not it -- so the engine's half is re-keyed onto the
        view the process resumes at and the program's half never moved. *)
diff --git a/iris/UkStore.v b/iris/UkStore.v
index 714e1f6db..0f210f594 100644
--- a/iris/UkStore.v
+++ b/iris/UkStore.v
@@ -764,7 +764,16 @@ Section UkStorePostFetch.
       (imm : mword 12) (sr1 sr2 : mword 5)
       (va wval : mword 64) (ib : mword 32) (t' : ptree)
       (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
-      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
+      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32)
+      (* THE STEP'S OWN LEFT SIDE (lane TRAP-ROWS, T3 / the IO-LEAF review).
+         [UkStep.uk_step_obl] hands this leaf [Kcx ∧ ukc]: the retiring
+         path's continuation on the left, the engine's re-entry slot on the
+         right.  The pair travels down HERE rather than being split at the
+         obligation, because the deposit this arm owes is itself an
+         ADDITIVE pair ([UexecRet.uexec_kill_arm_F]) -- so a LINEAR left
+         side (a process paying for its own death with its own exit
+         payload) reaches the credential without costing the slot. *)
+      (Kcx : iProp Σ) :
     ustore_width kk ->
     uv_redirect i o ->
     uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
@@ -795,7 +804,11 @@ Section UkStorePostFetch.
        beside the slot.  At a payload that is free at the kill status
        ([UkRun.ukn_pay_free_of_triv]) the right side costs exactly that
        persistent fact and nothing else. *)
-    (⊢ (ChildTok.my_pay gn Qp -∗
+    (* ...AND THE LEFT OF THE PAIR IS WHAT IT MAY SPEND (the IO-LEAF
+       review): [Kcx] is a RESOURCE here, so the payload's route works at
+       a LINEAR payload -- a forked child hands over [Qp (-1)] itself
+       rather than a proof that it is free. *)
+    (⊢ (Kcx ∗ ChildTok.my_pay gn Qp -∗
         (□ riscv_kill_cred ∨ ChildTok.kill_owed gn) : iProp Σ)) ->
     Z.rem (uint va) 4096 <= 4096 - kk ->
     uva_inj pt Mp ->
@@ -831,7 +844,8 @@ Section UkStorePostFetch.
     uk_pt_pure pt sz M Mp ->
     gen_cert -∗ uv_amb -∗
     (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv cw gn cs pidv false ∗
-          UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false))) -∗
+          UkStep.uk_paycont Qp gn
+            (Kcx ∧ uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false))) -∗
     resv_any cpu_id -∗
     TsoCtx.own_context XI -∗
     uv_bytes pt Mp t' -∗
@@ -1081,10 +1095,11 @@ Section UkStorePostFetch.
        the deposit premise and the right from the engine's Löb slot. *)
     iSplit.
     { iPoseProof Hkcw as "Hkcw".
-      iDestruct ("Hkcw" with "Hmyp") as "[#Hkl | Hkr]";
+      iDestruct "Hret" as "[Hkcx _]".
+      iDestruct ("Hkcw" with "[$Hkcx $Hmyp]") as "[#Hkl | Hkr]";
         [ iApply (ukill_cred_at_of_cred _ _ with "Hkl")
         | iApply (ukill_cred_at_of_owed _ _ with "Hkr") ]. }
-    iExact "Hret".
+    iDestruct "Hret" as "[_ Hret]". iExact "Hret".
   Qed.
 
 End UkStorePostFetch.
@@ -1112,7 +1127,11 @@ Section UkStoreObl.
       (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
       (sr1 sr2 : mword 5) (va wval : mword 64)
       (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
-      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
+      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32)
+      (* THE STEP'S OWN LEFT SIDE, carried whole to the fault leaf (lane
+         TRAP-ROWS, T3 / the IO-LEAF review) -- see
+         [uk_store_fault_post_fetch]. *)
+      (Kcx : iProp Σ) :
     uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
     uk_pt_pure pt sz M Mp ->
     udecode_base w i ->
@@ -1136,8 +1155,11 @@ Section UkStoreObl.
        refutes all three flavors ([UmodeMem.uva_canon],
        [UserPerm.lazy_free_wmapped], [UserPtTree.uleaf_ok_denied_excl]) and
        discharges this by [False]. *)
+    (* ...AND IT MAY SPEND THE PAIR'S LEFT SIDE (the IO-LEAF review): the
+       deposit is a RESOURCE, not a Coq-level [⊢ Qp (-1)], so a child that
+       dies at a LINEAR payload can pay for its own death. *)
     (u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va ->
-     ⊢ (ChildTok.my_pay gn Qp -∗
+     ⊢ (Kcx ∗ ChildTok.my_pay gn Qp -∗
         (□ riscv_kill_cred ∨ ChildTok.kill_owed gn) : iProp Σ)) ->
     uva_canon va ->
     Z.rem (uint va) 4096 <= 4096 - kk ->
@@ -1148,7 +1170,8 @@ Section UkStoreObl.
           ((⌜uk_store_retires pt Mp va kk⌝ -∗
             uvb C pt Rfd Rut sz π fdv cw gn cs pidv false (uM_store M (uint va) kk wval) m (add_vec_int pc 4) -∗
             WP (Loop : expr riscv_lang))
-           ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false)))) -∗
+           ∧ UkStep.uk_paycont Qp gn
+               (Kcx ∧ uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false)))) -∗
     resv_any cpu_id -∗
     hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
     TsoCtx.own_context XI -∗
@@ -1242,7 +1265,7 @@ Section UkStoreObl.
       exists w_st. exact (conj Hl (conj Hchk (conj Hntx HMb))).
     - iApply (uk_store_fault_post_fetch C pt Rfd R Rut sz π M Mp m pc 4 kk i o imm sr1 sr2 va wval
               (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2 fdv cw gn cs pidv
-              Hkw Hred Hexp Hva Hwval Hfault (Hkcf Hfault) Hpg Hinj Hg1
+              Kcx Hkw Hred Hexp Hva Hwval Hfault (Hkcf Hfault) Hpg Hinj Hg1
               Hpins2
               (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
               (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
@@ -1273,7 +1296,11 @@ Section UkStoreObl.
       (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
       (sr1 sr2 : mword 5) (va wval : mword 64)
       (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
-      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
+      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32)
+      (* THE STEP'S OWN LEFT SIDE, carried whole to the fault leaf (lane
+         TRAP-ROWS, T3 / the IO-LEAF review) -- see
+         [uk_store_fault_post_fetch]. *)
+      (Kcx : iProp Σ) :
     uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
     uk_pt_pure pt sz M Mp ->
     udecode_rvc h i ->
@@ -1297,8 +1324,11 @@ Section UkStoreObl.
        refutes all three flavors ([UmodeMem.uva_canon],
        [UserPerm.lazy_free_wmapped], [UserPtTree.uleaf_ok_denied_excl]) and
        discharges this by [False]. *)
+    (* ...AND IT MAY SPEND THE PAIR'S LEFT SIDE (the IO-LEAF review): the
+       deposit is a RESOURCE, not a Coq-level [⊢ Qp (-1)], so a child that
+       dies at a LINEAR payload can pay for its own death. *)
     (u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va ->
-     ⊢ (ChildTok.my_pay gn Qp -∗
+     ⊢ (Kcx ∗ ChildTok.my_pay gn Qp -∗
         (□ riscv_kill_cred ∨ ChildTok.kill_owed gn) : iProp Σ)) ->
     uva_canon va ->
     Z.rem (uint va) 4096 <= 4096 - kk ->
@@ -1309,7 +1339,8 @@ Section UkStoreObl.
           ((⌜uk_store_retires pt Mp va kk⌝ -∗
             uvb C pt Rfd Rut sz π fdv cw gn cs pidv false (uM_store M (uint va) kk wval) m (add_vec_int pc 2) -∗
             WP (Loop : expr riscv_lang))
-           ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false)))) -∗
+           ∧ UkStep.uk_paycont Qp gn
+               (Kcx ∧ uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false)))) -∗
     resv_any cpu_id -∗
     hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
     TsoCtx.own_context XI -∗
@@ -1408,7 +1439,7 @@ Section UkStoreObl.
       exists w_st. exact (conj Hl (conj Hchk (conj Hntx HMb))).
     - iApply (uk_store_fault_post_fetch C pt Rfd R Rut sz π M Mp m pc 2 kk i o imm sr1 sr2 va wval
               (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2 fdv cw gn cs pidv
-              Hkw Hred Hexp Hva Hwval Hfault (Hkcf Hfault) Hpg Hinj Hg1
+              Kcx Hkw Hred Hexp Hva Hwval Hfault (Hkcf Hfault) Hpg Hinj Hg1
               Hpins2
               (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
               (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
@@ -1573,7 +1604,7 @@ Section UkStore.
              in the map at all ([UptTree.upt_map_wf_not_tramp] / [_not_tf]).
        So a verified program pays NOTHING for the kill it cannot suffer. *)
     assert (Hkcf : u_fault_flavor (Store Data) (ud_tfp pt') (ud_um pt') va ->
-                   ⊢ (ChildTok.my_pay gn Qp -∗
+                   ⊢ ((True : iProp Σ) ∗ ChildTok.my_pay gn Qp -∗
                       (□ riscv_kill_cred ∨ ChildTok.kill_owed gn) : iProp Σ)).
     { intros Hfl. exfalso.
       destruct (lazy_free_wmapped pt' sz (svpn_of va) q Hwf' Hlf'
@@ -1605,7 +1636,8 @@ Section UkStore.
                uvb (CID := CIDo) C' pt' Rfd' Rut' sz π fdv cw gn cs pidv false (uM_store M (uint va) k wval) m
                  (add_vec_int pc (if is_rvc then 2 else 4)) -∗
                WP (Loop : expr riscv_lang))
-              ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false))))%I with "[Hk]" as "Hk".
+              ∧ UkStep.uk_paycont Qp gn
+                  (True ∧ uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false))))%I with "[Hk]" as "Hk".
     { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
       iFrame "Hrut Hfdr Hkb". iSplit.
       - (* the RETIRE leg: the continuation's own side.  The guard is free
@@ -1616,8 +1648,12 @@ Section UkStore.
         iIntros "_ Hb". rewrite /ukc.
         iApply ("Hkc" $! CIDo XIo C' pt' Rfd' Rut' HRut' with "[%] [%] [%] Hb");
           [ exact Hlo' | exact Hpm' | intros _; exact Hlf' ].
-      - (* the FAULT leg: the slot goes to the kernel with the pay fact *)
+      - (* the FAULT leg: the slot goes to the kernel with the pay fact.
+           THE PAIR'S LEFT SIDE IS EMPTY HERE (the IO-LEAF review): this
+           leaf's key says the page is WRITABLE, so the fault arm is
+           unreachable and the deposit it would owe is [True]. *)
         iDestruct "Hkc" as "(#Hmyp & Hkc)". iFrame "Hmyp".
+        iSplit; [done |].
         iDestruct "Hkc" as "[_ Hkc]".
         rewrite (uslot_run m pc M π sz fdv cw gn cs pidv Hx0 Hal2). iExact "Hkc". }
     iPoseProof (uv_swp_fetch_uinstr (CID := CIDo) (XI := XIo) pt' Mp' t (uc_dqc C')
@@ -1626,12 +1662,14 @@ Section UkStore.
     destruct is_rvc.
     - iDestruct "Hf" as (h) "[[%HisRVC %Hdecrvc] Hbridge]".
       iApply (uk_store_obl_rvc C' pt' Rfd' R Rut' sz π M Mp' m pc h i o k imm rs1 rs2 va wval
-                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv Hpre Hpure Hdecrvc Hkw Hred Hg1 Hexp
+                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv (True : iProp Σ)
+                Hpre Hpure Hdecrvc Hkw Hred Hg1 Hexp
                 Hva Hwval Hdisp Hkcf Hcanon Hpg Hal
                 with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
     - iDestruct "Hf" as (w) "[[%HnRVC %Hdecbase] Hbridge]".
       iApply (uk_store_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w i o k imm rs1 rs2 va wval
-                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv Hpre Hpure Hdecbase Hkw Hred Hg1 Hexp
+                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv (True : iProp Σ)
+                Hpre Hpure Hdecbase Hkw Hred Hg1 Hexp
                 Hva Hwval Hdisp Hkcf Hcanon Hpg Hal
                 with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
   Qed.
@@ -1723,18 +1761,23 @@ Section UkStore.
     uva_canon va ->
     Z.rem (uint va) 4096 <= 4096 - k ->
     is_aligned_vaddr (Virtaddr va) k = true ->
-    (* the payload at the kill status, free at a forked child's record *)
-    (⊢ (Qp (-1) : iProp Σ)) ->
     uvb C pt Rfd Rut sz π fdv cw gn cs pidv false M m pc -∗
     ChildTok.my_pay gn Qp -∗
+    (* THE PAYLOAD AT THE KILL STATUS, AS A RESOURCE (the IO-LEAF review).
+       It used to be the Coq-level [⊢ Qp (-1)] -- "the payload is free" --
+       which a child that dies at a LINEAR payload cannot supply.  It
+       travels as [UkStep.uk_step_obl]'s [Kc], the LEFT of the pair the
+       fault leaf is handed, so it reaches the credential without costing
+       the resume slot. *)
+    Qp (-1) -∗
     WP (Loop : expr riscv_lang).
   Proof.
-    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hden Hcanon Hpg Hal Hpay.
+    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hden Hcanon Hpg Hal.
     pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
     pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
-    iIntros "Hb #Hmy".
-    iApply (wp_uk_step C pt Rfd Rut π sz Hlo Hpm HRut Hlf0 True%I Qp M m pc
-              fdv cw gn cs pidv Hal2 with "Hb [] [$Hmy]").
+    iIntros "Hb #Hmy Hpay".
+    iApply (wp_uk_step C pt Rfd Rut π sz Hlo Hpm HRut Hlf0 (Qp (-1)) Qp M m pc
+              fdv cw gn cs pidv Hal2 with "Hb [] [$Hmy $Hpay]").
     iModIntro.
     rewrite /uk_step_obl.
     iIntros (R CIDo XIo C' pt' Rfd' Rut' HRut' Mp' t rs1s rsA usatp pcfg paddr)
@@ -1758,10 +1801,10 @@ Section UkStore.
       exact (uleaf_ok_denied_excl (Store Data) w_st Hchk Hd0). }
     (* THE PRICE, and it is the process's own ([ChildTok.kill_owed]) *)
     assert (Hkcf : u_fault_flavor (Store Data) (ud_tfp pt') (ud_um pt') va ->
-                   ⊢ (ChildTok.my_pay gn Qp -∗
+                   ⊢ (Qp (-1) ∗ ChildTok.my_pay gn Qp -∗
                       (□ riscv_kill_cred ∨ ChildTok.kill_owed gn) : iProp Σ)).
-    { intros _. iIntros "#Hm". iRight.
-      iApply (ChildTok.kill_owed_of gn Qp with "Hm"). iApply Hpay. }
+    { intros _. iIntros "(Hp & #Hm)". iRight.
+      iApply (ChildTok.kill_owed_of gn Qp with "Hm Hp"). }
     iPoseProof "Hamb" as "(#Hhw & _ & _)".
     iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
       "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
@@ -1774,7 +1817,8 @@ Section UkStore.
                uvb (CID := CIDo) C' pt' Rfd' Rut' sz π fdv cw gn cs pidv false (uM_store M (uint va) k wval) m
                  (add_vec_int pc (if is_rvc then 2 else 4)) -∗
                WP (Loop : expr riscv_lang))
-              ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false))))%I with "[Hk]" as "Hk".
+              ∧ UkStep.uk_paycont Qp gn
+                  (Qp (-1) ∧ uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv false))))%I with "[Hk]" as "Hk".
     { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
       iFrame "Hrut Hfdr Hkb". iSplit.
       - (* the RETIRE leg is UNREACHABLE and says so *)
@@ -1782,20 +1826,27 @@ Section UkStore.
       - (* the FAULT leg: the slot goes to the kernel with the pay fact,
            and the slot is the engine's own Löb hypothesis *)
         iDestruct "Hkc" as "(#Hmyp & Hkc)". iFrame "Hmyp".
-        iDestruct "Hkc" as "[_ Hkc]".
-        rewrite (uslot_run m pc M π sz fdv cw gn cs pidv Hx0 Hal2). iExact "Hkc". }
+        (* the pair travels WHOLE: the credential comes off its left, the
+           slot off its right, and the leaf's own deposit is additive too
+           (lane TRAP-ROWS, T3) *)
+        iSplit.
+        + iDestruct "Hkc" as "[$ _]".
+        + iDestruct "Hkc" as "[_ Hkc]".
+          rewrite (uslot_run m pc M π sz fdv cw gn cs pidv Hx0 Hal2). iExact "Hkc". }
     iPoseProof (uv_swp_fetch_uinstr (CID := CIDo) (XI := XIo) pt' Mp' t (uc_dqc C')
                   rsA pc is_rvc i Hinj Hui' LpcA LcpA (proj1 HmsokA) LmenvA
                   HpinsA Htok) as "Hf".
     destruct is_rvc.
     - iDestruct "Hf" as (h) "[[%HisRVC %Hdecrvc] Hbridge]".
       iApply (uk_store_obl_rvc C' pt' Rfd' R Rut' sz π M Mp' m pc h i o k imm rs1 rs2 va wval
-                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv Hpre Hpure Hdecrvc Hkw Hred Hg1 Hexp
+                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv (Qp (-1))
+                Hpre Hpure Hdecrvc Hkw Hred Hg1 Hexp
                 Hva Hwval Hdisp Hkcf Hcanon Hpg Hal
                 with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
     - iDestruct "Hf" as (w) "[[%HnRVC %Hdecbase] Hbridge]".
       iApply (uk_store_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w i o k imm rs1 rs2 va wval
-                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv Hpre Hpure Hdecbase Hkw Hred Hg1 Hexp
+                t usatp pcfg paddr rs1s rsA fdv cw gn cs pidv (Qp (-1))
+                Hpre Hpure Hdecbase Hkw Hred Hg1 Hexp
                 Hva Hwval Hdisp Hkcf Hcanon Hpg Hal
                 with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
   Qed.
@@ -1894,19 +1945,20 @@ Section UkStore.
     wval = m !!! Regidx rs2 ->
     uk_store_denied va ->
     uva_canon va ->
-    (⊢ (Qp (-1) : iProp Σ)) ->
     uvb C pt Rfd Rut sz π fdv cw gn cs pidv false M m pc -∗
     ChildTok.my_pay gn Qp -∗
+    (* the payload at the kill status, as a RESOURCE (the IO-LEAF review) *)
+    Qp (-1) -∗
     WP (Loop : expr riscv_lang).
   Proof.
-    intros Hui Hva Hwval Hden Hcanon Hpay.
-    iIntros "Hb Hmy".
+    intros Hui Hva Hwval Hden Hcanon.
+    iIntros "Hb Hmy Hpay".
     iApply (wp_uk_store_denied M m pc fdv cw gn cs pidv false
               (STORE (imm, Regidx rs2, Regidx rs1, 1)) None
               imm rs1 rs2 1 va wval
               ustore_width_1 Hui ltac:(intro s; exact I) I eq_refl eq_refl
-              Hva Hwval Hden Hcanon (uinpage_byte va) (is_aligned_vaddr_1 va) Hpay
-              with "Hb Hmy").
+              Hva Hwval Hden Hcanon (uinpage_byte va) (is_aligned_vaddr_1 va)
+              with "Hb Hmy Hpay").
   Qed.
 
   Lemma wp_uk_csdsp (M : gmap Z (bv 8)) (m : regfile)
diff --git a/iris/UserChildren.v b/iris/UserChildren.v
index c30564d1f..086823b46 100644
--- a/iris/UserChildren.v
+++ b/iris/UserChildren.v
@@ -168,24 +168,70 @@ Proof. right. exists γ'. reflexivity. Qed.
 Section WaitAns.
   Context `{!ctokG Σ}.
 
-  Definition wait_ans (rv : mword 32) (xs : Z) (cs cs' : gset gname) : iProp Σ :=
-    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝
+  (* ...AND THE FAILING ARM CARRIES ITS REASON, at a NULL status pointer
+     (lane TRAP-ROWS, T4).  wait() returns -1 on THREE exits, not two:
+       * [!havekids] -- the caller's own children column is empty;
+       * [killed(p)] -- the caller is dead, and [killed()] hands back this
+         incarnation's one-shot;
+       * a failing [copyout] of the status word -- which happens with a
+         ZOMBIE child present and no shot at all.
+     The third is what the row is CONDITIONED on: it is guarded by
+     [addr != 0] in the C, and every wait leaf in the tree forces
+     [uint a1 = 0] ([UkRunSys.wp_uk_ecall_wait_null] / [_any],
+     [UkInit.wp_kinit_wait]), so at a null status pointer it is
+     unreachable and the other two are the whole story.
+     [nullst] IS THE GUARD, not a claim: a caller that passed a real
+     pointer gets the landed row back and nothing more.
+     BOTH INFORMATIVE DISJUNCTS ARE PERSISTENT, so a caller reads the
+     reason off without spending the arm. *)
+  (* THE REASON ITSELF, named once: the -1 arm's second conjunct, and the
+     only thing the three failing tails have to produce. *)
+  Definition wait_why (cs : gset gname) (gn : gname) (nullst : bool) : iProp Σ :=
+    (⌜nullst = false⌝ ∨ ⌜cs = (∅ : gset gname)⌝ ∨ kill_shot gn)%I.
+
+  Global Instance wait_why_persistent (cs : gset gname) (gn : gname) (b : bool) :
+    Persistent (wait_why cs gn b).
+  Proof. rewrite /wait_why. apply _. Qed.
+
+  Definition wait_ans (rv : mword 32) (xs : Z) (cs cs' : gset gname)
+      (gn : gname) (nullst : bool) : iProp Σ :=
+    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝ ∗ wait_why cs gn nullst
      ∨ ∃ γ' : gname,
          ⌜cs' = cs ∖ {[γ']}⌝ ∗ exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.
 
   (* the pure row, which is all the twenty-odd relays between kwait and the
      program ever look at *)
-  Lemma wait_ans_reaped (rv : mword 32) (xs : Z) (cs cs' : gset gname) :
-    wait_ans rv xs cs cs' -∗ ⌜ch_reaped cs cs'⌝.
+  Lemma wait_ans_reaped (rv : mword 32) (xs : Z) (cs cs' : gset gname)
+      (gn : gname) (nullst : bool) :
+    wait_ans rv xs cs cs' gn nullst -∗ ⌜ch_reaped cs cs'⌝.
   Proof.
-    iIntros "[[_ %He] | (%γ' & %He & _)]"; iPureIntro.
+    iIntros "[[[_ %He] _] | (%γ' & %He & _)]"; iPureIntro.
     - left. exact He.
     - right. exists γ'. exact He.
   Qed.
 
-  (* the failing arm, for the three exits that reap nothing *)
-  Lemma wait_ans_neg (xs : Z) (cs : gset gname) :
-    ⊢ wait_ans (mword_of_int (-1) : mword 32) xs cs cs.
-  Proof. iLeft. iPureIntro. split; reflexivity. Qed.
+  (* the failing arm, for the three exits that reap nothing.  Each supplies
+     its OWN reason: the childless exit the empty column, the killed exit
+     the one-shot, the copyout exit the guard's refutation. *)
+  Lemma wait_ans_neg (xs : Z) (cs : gset gname) (gn : gname) (nullst : bool) :
+    wait_why cs gn nullst -∗
+    wait_ans (mword_of_int (-1) : mword 32) xs cs cs gn nullst.
+  Proof.
+    iIntros "Hwhy". iLeft. iSplitR; [ iPureIntro; split; reflexivity | ].
+    iExact "Hwhy".
+  Qed.
+
+  (* ...and the three ways to build that reason *)
+  Lemma wait_why_notnull (cs : gset gname) (gn : gname) (nullst : bool) :
+    nullst = false -> ⊢ wait_why cs gn nullst.
+  Proof. intros ->. rewrite /wait_why. by iLeft. Qed.
+
+  Lemma wait_why_empty (cs : gset gname) (gn : gname) (nullst : bool) :
+    cs = (∅ : gset gname) -> ⊢ wait_why cs gn nullst.
+  Proof. intro He. rewrite /wait_why. iRight. by iLeft. Qed.
+
+  Lemma wait_why_shot (cs : gset gname) (gn : gname) (nullst : bool) :
+    kill_shot gn -∗ wait_why cs gn nullst.
+  Proof. iIntros "H". rewrite /wait_why. iRight. iRight. iExact "H". Qed.
 
 End WaitAns.
