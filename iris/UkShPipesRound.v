(* ===================================================================== *)
(* UkShPipesRound.v -- THE CHILD WALK AT ANY NUMBER OF STAGES, lane       *)
(* PIPES-C3b (design/pipes-general.md §1.1 and §5, cut C3), claim-free    *)
(* and model-free.                                                        *)
(*                                                                        *)
(* [UkShPipeRound.wp_kshm_child_pipe] and [UShPipeChild.                  *)
(* wp_kshm_child_pipe_paid_at_sz] are the mould, one pipe over: sh's      *)
(* forked child enters at 0x9c0 with the line in s1, parses it, and runs  *)
(* [runcmd] on the answer.  At N stages the parse is                      *)
(* [UkShPipesCmd.wp_kshp_parsecmd_pipes] and the seam                     *)
(* [UkShPipesSeam.ush_cmd_of_ushp_pipes], whose cut premise is            *)
(* [UkShPipesCmd.ushq_cuts_ok_bars] -- so from the raw line bytes the     *)
(* child reaches [runcmd] on [UkShPipe.ush_pipes] (§1).                   *)
(*                                                                        *)
(* §2 is [runcmd] on that right spine, by INDUCTION ON THE STAGES: each   *)
(* node is [UkShPipe.wp_kshr_pipe_arm_g2]; its LEFT child is a stage (an  *)
(* EXEC leaf, a law of the caller's); its RIGHT child is either the last  *)
(* stage (a law of the caller's) or THE SUFFIX -- the forked sh re-       *)
(* entering [runcmd] on a shorter spine with fd 0 the pipe's read end --  *)
(* which is the induction hypothesis.  What a node's process holds beyond *)
(* the structural rows (its credential, split, pipe(2) call, wait law,    *)
(* panic tails and exit at 0xea) is ONE bundle, [ush_node_obl], at an     *)
(* abstract payment: the node's children owe [Qc k st0], indexed by the   *)
(* node and by what its fd 0 is (so an inner node's payment may name the  *)
(* pipe it reads).  The ENTRY law turns what the right child of node [k]  *)
(* was handed into node [k+1]'s bundle, under a fancy update so a round   *)
(* can allocate there.  Nothing here names the console family or a model. *)
(*                                                                        *)
(* §3 is the TAINT instance, which is both the check that §2's premises   *)
(* are satisfiable (every law discharged, [UkShPipe.                      *)
(* wp_kshr_runcmd_pipes_closed]'s statement re-proved through the law)    *)
(* and the end-to-end walk: raw line bytes of [echo ws | cat | ... | cat] *)
(* at 0x9c0 to every process's exit.                                      *)
(*                                                                        *)
(* WHAT IS LEFT FOR THE ROUND (C5-C7): the laws themselves at a paying    *)
(* instance.  The left and last laws are the stage entries at the         *)
(* N-writer console family, the entry law is where node [k+1]'s pipe       *)
(* names, protocol and console writers are allocated, and the bundle's    *)
(* wait law is the free reading unless the fork arm relays the child's    *)
(* pid (see the lane report).                                             *)
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
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.     (* [PIDMAX] *)
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import UkShMain.
Require Import UkShMalloc.
Require Import UserPtTree.
Require Import UserPerm.     (* [usz_ok] *)
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShPipe.
Require Import UkShPipesLex.
Require Import UkShPipesParse.
Require Import UkShPipesSeam.
Require Import UkShPipesCmd.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UexecSG.
Require Import UexecRet.     (* [uwait_ans] *)
Local Open Scope Z_scope.
Import Defs.

(* the spine's height: one more than its number of bars *)
Lemma ush_ht_pipes (a : list uarg) (rest : list (list uarg)) :
  ush_ht (ush_pipes a rest) = S (length rest).
Proof using.
  revert a. induction rest as [| b rest IH ]; intros a; [ reflexivity | ].
  cbn [ush_pipes ush_ht length]. rewrite IH. cbn [ush_ht]. lia.
Qed.

Section UkShPipesRound.
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
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  (* A FANCY UPDATE IN FRONT OF THE TRIVIAL-POST WP
     ([UShPipeChild]'s, restated: that file is not in this one's cone). *)
  Local Lemma fupd_mwp_ps (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* ===================================================================== *)
  (* §2 THE SUFFIX, BY INDUCTION ON THE STAGES                              *)
  (* ===================================================================== *)

  (* WHAT THE PROCESS RUNNING ONE NODE HOLDS beyond the structural rows:
     [UkShPipe.wp_kshr_pipe_arm_g2]'s premises at the node's ledger [ld],
     its children's payment [Qc] and the two lends [RcL]/[RcR] the caller's
     stage laws read, with every other family of the arm existential. *)
  Definition ush_node_obl (N : uk_names Σ) (ld : list fdstate) (szv cwdv : Z)
      (Sc : gset gname) (av : nat) (Qc : Z -> iProp Σ)
      (RcL RcR : pipe_names -> iProp Σ) : iProp Σ :=
    (∃ (Cr Wr : iProp Σ) (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ)
       (R Rk Cx : pipe_names -> iProp Σ),
       □ (app_taint -∗ Qc (-1)) ∗
       Cr ∗
       (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) ∗
       ush_pipe_call N ld R ∗
       Wr ∗
       ush_wait0_law N Wr Pw ∗
       (* panic("pipe") *)
       □ (∀ (h' : CpuId) (m' : regfile),
            ⌜ uint (m' !!! Regidx a0_idx) = 0x12c8 ⌝ -∗
            UserFd.ustd (ukn_fd N) ld -∗
            Cr -∗
            urun N h' m' (mword_of_int ShSyms.panic)
              (UkShDiag.ush_Dg + (2 + av)) -∗
            mWP (Loop : expr riscv_lang)) ∗
       (* the first fork1's panic("fork") *)
       □ (∀ (h' : CpuId) (m' : regfile) (r : mword 64) (γp : pipe_names),
            ⌜ uint (m' !!! Regidx a0_idx) = 0x1298 ⌝ -∗
            ⌜ r = (mword_of_int (-1) : mword 64) ⌝ -∗
            ((⌜r = (mword_of_int (-1) : mword 64)⌝
                ∗ UserChildren.uch (ukn_ch N) Sc ∗ RcL γp)
             ∨ ∃ (γ : gname) (pidv : mword 32),
                 ⌜r = (sign_extend' 64 pidv : mword 64)⌝
                 ∗ ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝
                 ∗ ⌜γ ∉ Sc⌝
                 ∗ child_tok γ pidv Qc
                 ∗ UserChildren.uch (ukn_ch N) (Sc ∪ {[γ]})) -∗
            UserFd.ustd (ukn_fd N) ld -∗
            RcR γp -∗
            Cx γp -∗
            urun N h' m' (mword_of_int ShSyms.panic) (UkShDiag.ush_Dg + av) -∗
            mWP (Loop : expr riscv_lang)) ∗
       (* the second fork1's panic("fork") *)
       □ (∀ (h' : CpuId) (m' : regfile) (r : mword 64) (γp : pipe_names)
            (S1 : gset gname),
            ⌜ uint (m' !!! Regidx a0_idx) = 0x1298 ⌝ -∗
            ⌜ r = (mword_of_int (-1) : mword 64) ⌝ -∗
            ((⌜r = (mword_of_int (-1) : mword 64)⌝
                ∗ UserChildren.uch (ukn_ch N) S1 ∗ RcR γp)
             ∨ ∃ (γ : gname) (pidv : mword 32),
                 ⌜r = (sign_extend' 64 pidv : mword 64)⌝
                 ∗ ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝
                 ∗ ⌜γ ∉ S1⌝
                 ∗ child_tok γ pidv Qc
                 ∗ UserChildren.uch (ukn_ch N) (S1 ∪ {[γ]})) -∗
            UserFd.ustd (ukn_fd N) ld -∗
            Cx γp -∗
            urun N h' m' (mword_of_int ShSyms.panic) (UkShDiag.ush_Dg + av) -∗
            mWP (Loop : expr riscv_lang)) ∗
       (* the parent at 0xea, after both waits *)
       (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
          (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
          ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
          ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
          ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
          ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
          Pw rw1 S2 S3 -∗
          Pw rw2 S3 S4 -∗
          UserChildren.uch (ukn_ch N) S4 -∗
          ush_jtab (ukn_t N) -∗
          usz (ukn_s N) szv -∗
          UserFd.ustd (ukn_fd N) ld -∗
          UserCwd.ucwd (ukn_cwd N) cwdv -∗
          Rk γp -∗
          Cx γp -∗
          Wr -∗
          urun N h' m' (mword_of_int 0xea) (2 + (UkShDiag.ush_Dg + av)) -∗
          mWP (Loop : expr riscv_lang)))%I.

  Section Law.
    (* THE PIPELINE: its stages [stgs], sh's ledger [ld0] at the top node
       (fd 1 the console at every node, fd 0 replaced node by node), the
       break and cwd every fork inherits, and the node-and-input-indexed
       payment and lends. *)
    Context (stgs : list (list uarg)) (ld0 : list fdstate) (st1 : fdstate)
      (szv cwdv : Z) (n : nat)
      (Qc : nat -> fdstate -> Z -> iProp Σ)
      (RcL RcR : nat -> fdstate -> pipe_names -> iProp Σ).
    Hypothesis HQc : forall (k : nat) (st : fdstate) (x y : Z),
      Qc k st x = Qc k st y.
    Hypothesis Hl1 : ld0 !! 1%nat = Some st1.
    Hypothesis Hne1 : st1 <> FdClosed.
    Hypothesis Hnp1 : forall (rb wb : bool) (gp : pipe_names),
      st1 <> FdOpen rb wb (FdPipe gp).
    Hypothesis Hl0len : (0 < length ld0)%nat.

    Local Notation rd γp := (FdOpen true false (FdPipe γp)).
    Local Notation wr γp := (FdOpen false true (FdPipe γp)).

    (* THE LEFT STAGE of node [k]: runcmd on its EXEC leaf, fd 1 the pipe's
       write end, at the lend the node's split gave it *)
    Definition ush_left_law : iProp Σ :=
      (∀ (k : nat) (st0 : fdstate) (args : list uarg) (N' : uk_names Σ)
         (h' : CpuId) (m' : regfile) (γ' : gname) (γp : pipe_names) (q : Z)
         (av : nat),
         ⌜ stgs !! k = Some args ⌝ -∗
         ⌜ (S k < length stgs)%nat ⌝ -∗
         ⌜ (n <= av)%nat ⌝ -∗
         ⌜ ukn_pay N' = Qc k st0 ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
         my_pay γ' (Qc k st0) -∗
         shk_code (ukn_t N') -∗
         ush_jtab (ukn_t N') -∗
         ush_cmd (ukn_d N') q (UExec args) -∗
         usz (ukn_s N') szv -∗
         UserFd.ustd (ukn_fd N') (<[1%nat := wr γp]> (<[0%nat := st0]> ld0)) -∗
         UserCwd.ucwd (ukn_cwd N') cwdv -∗
         UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
         ush_cldep (rd γp) -∗
         ush_cldep (wr γp) -∗
         RcL k st0 γp -∗
         urun N' h' m' (mword_of_int ShSyms.runcmd)
           (2 + (UkShDiag.ush_Dg + av)) -∗
         mWP (Loop : expr riscv_lang))%I.

    (* THE LAST STAGE: the right child of the last node, fd 0 the last
       pipe's read end *)
    Definition ush_last_law : iProp Σ :=
      (∀ (k : nat) (st0 : fdstate) (args : list uarg) (N' : uk_names Σ)
         (h' : CpuId) (m' : regfile) (γ' : gname) (γp : pipe_names) (q : Z)
         (av : nat),
         ⌜ stgs !! S k = Some args ⌝ -∗
         ⌜ length stgs = S (S k) ⌝ -∗
         ⌜ (n <= av)%nat ⌝ -∗
         ⌜ ukn_pay N' = Qc k st0 ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
         my_pay γ' (Qc k st0) -∗
         shk_code (ukn_t N') -∗
         ush_jtab (ukn_t N') -∗
         ush_cmd (ukn_d N') q (UExec args) -∗
         usz (ukn_s N') szv -∗
         UserFd.ustd (ukn_fd N') (<[0%nat := rd γp]> ld0) -∗
         UserCwd.ucwd (ukn_cwd N') cwdv -∗
         UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
         ush_cldep (rd γp) -∗
         ush_cldep (wr γp) -∗
         RcR k st0 γp -∗
         urun N' h' m' (mword_of_int ShSyms.runcmd)
           (2 + (UkShDiag.ush_Dg + av)) -∗
         mWP (Loop : expr riscv_lang))%I.

    (* THE ENTRY: the right child of node [k] is node [k+1]'s process;
       what it was handed becomes node [k+1]'s bundle *)
    Definition ush_entry_law : iProp Σ :=
      (∀ (k : nat) (st0 : fdstate) (N' : uk_names Σ) (γ' : gname)
         (γp : pipe_names) (av : nat),
         ⌜ (S (S k) < length stgs)%nat ⌝ -∗
         ⌜ (n <= av)%nat ⌝ -∗
         ⌜ ukn_pay N' = Qc k st0 ⌝ -∗
         my_pay γ' (Qc k st0) -∗
         RcR k st0 γp -∗
         shk_code (ukn_t N') -∗
         ush_jtab (ukn_t N') -∗
         |={⊤}=> ush_node_obl N' (<[0%nat := rd γp]> ld0) szv cwdv ∅ av
                   (Qc (S k) (rd γp)) (RcL (S k) (rd γp)) (RcR (S k) (rd γp)))%I.

    Lemma wp_kshr_runcmd_pipes_law :
      forall (rest : list (list uarg)) (a b : list uarg) (k : nat)
             (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
             (t : Z) (st0 : fdstate) (Sc : gset gname),
        drop k stgs = a :: b :: rest ->
        m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
        st0 <> FdClosed ->
        □ ush_left_law -∗
        □ ush_last_law -∗
        □ ush_entry_law -∗
        shk_code (ukn_t N) -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (ush_pipes a (b :: rest)) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) (<[0%nat := st0]> ld0) -∗
        ush_cldep st0 -∗
        UserCwd.ucwd (ukn_cwd N) cwdv -∗
        UserChildren.uch (ukn_ch N) Sc -∗
        ush_node_obl N (<[0%nat := st0]> ld0) szv cwdv Sc
          (6 * length rest + n) (Qc k st0) (RcL k st0) (RcR k st0) -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + (6 * length rest + n)))) -∗
        mWP (Loop : expr riscv_lang).
    Proof using Hpsok_free HQc Hl1 Hne1 Hnp1 Hl0len.
      induction rest as [| c rest IH ];
        intros a b k N Hcst h m t st0 Sc Hdrop Ha0 Hne0;
        iIntros "#Hleft #Hlast #Hent #Hcode #Hjt #Htree Hsz Hstd #Hcd0 Hcwd Hch
                 Hobl Hrun".
      all: rewrite /ush_left_law /ush_last_law /ush_entry_law.
      (* the stage facts off the drop *)
      all: assert (Hka : stgs !! k = Some a)
             by (rewrite -(Nat.add_0_r k) -lookup_drop Hdrop; reflexivity).
      all: assert (Hkb : stgs !! S k = Some b)
             by (rewrite -(Nat.add_1_r k) -lookup_drop Hdrop; reflexivity).
      all: pose proof (f_equal length Hdrop) as Hlen;
           rewrite length_drop in Hlen; cbn [length] in Hlen.
      all: assert (Hl0 : (<[0%nat := st0]> ld0) !! 0%nat = Some st0)
             by exact (list_lookup_insert ld0 0%nat st0 Hl0len).
      all: assert (Hl1' : (<[0%nat := st0]> ld0) !! 1%nat = Some st1)
             by (rewrite list_lookup_insert_ne; [ exact Hl1 | lia ]).
      all: iDestruct "Hobl" as (Cr Wr Pw R Rk Cx)
             "(#Hkw & Hcr & Hsplit & Hpipe & HWr & #Hwl & #Hp1 & #Hp2 & #Hp3
               & Hpar)".
      all: iApply (wp_kshr_pipe_arm_g2 Hpsok_free N (UExec a) _ h m t szv cwdv
                     (<[0%nat := st0]> ld0) st0 st1 Sc _
                     R (RcL k st0) (RcR k st0) Rk Cx (Qc k st0) Cr Wr Pw
                     (HQc k st0) Ha0 Hl0 Hl1' Hne0 Hne1 Hnp1
                     with "Hcode Hjt Htree Hsz Hstd Hcd0 Hcwd Hch Hkw Hcr Hsplit
                           Hpipe HWr Hwl Hp1 Hp2 Hp3 Hrun [] [] Hpar").
      - (* ---- rest = []: the LEFT stage ---- *)
        iIntros (N' h' m' γ' γp q) "%Hpeq %Ha0' Hmy #Hck #Hjt2 #Hqc Hsz Hstd
                                    Hcwd Hch #Hcd1 #Hcd2 HRc Hrun".
        iApply ("Hleft" $! k st0 a N' h' m' γ' γp q (6 * 0 + n)%nat
                  with "[] [] [] [] [] Hmy Hck Hjt2 Hqc Hsz Hstd Hcwd Hch
                        Hcd1 Hcd2 HRc Hrun");
          iPureIntro; [ exact Hka | lia | lia | exact Hpeq | exact Ha0' ].
      - (* ---- rest = []: the LAST stage ---- *)
        iIntros (N' h' m' γ' γp q) "%Hpeq %Ha0' Hmy #Hck #Hjt2 #Hqc Hsz Hstd
                                    Hcwd Hch #Hcd1 #Hcd2 HRc Hrun".
        rewrite list_insert_insert.
        iApply ("Hlast" $! k st0 b N' h' m' γ' γp q (6 * 0 + n)%nat
                  with "[] [] [] [] [] Hmy Hck Hjt2 Hqc Hsz Hstd Hcwd Hch
                        Hcd1 Hcd2 HRc Hrun");
          iPureIntro; [ exact Hkb | lia | lia | exact Hpeq | exact Ha0' ].
      - (* ---- a longer spine: the LEFT stage ---- *)
        iIntros (N' h' m' γ' γp q) "%Hpeq %Ha0' Hmy #Hck #Hjt2 #Hqc Hsz Hstd
                                    Hcwd Hch #Hcd1 #Hcd2 HRc Hrun".
        iApply ("Hleft" $! k st0 a N' h' m' γ' γp q
                  (6 * length (c :: rest) + n)%nat
                  with "[] [] [] [] [] Hmy Hck Hjt2 Hqc Hsz Hstd Hcwd Hch
                        Hcd1 Hcd2 HRc Hrun");
          iPureIntro; [ exact Hka | lia | lia | exact Hpeq | exact Ha0' ].
      - (* ---- a longer spine: THE SUFFIX, the induction hypothesis ---- *)
        iIntros (N' h' m' γ' γp q) "%Hpeq %Ha0' Hmy #Hck #Hjt2 #Hqc Hsz Hstd
                                    Hcwd Hch #Hcd1 #Hcd2 HRc Hrun".
        pose proof (ukn_const_of_eq N' (Qc k st0) Hpeq (HQc k st0)) as Hcst'.
        rewrite list_insert_insert.
        iApply fupd_mwp_ps.
        iMod ("Hent" $! k st0 N' γ' γp (6 * length rest + n)%nat
                with "[] [] [] Hmy HRc Hck Hjt2") as "Hobl'".
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. exact Hpeq. }
        iModIntro.
        assert (Hdrop' : drop (S k) stgs = b :: c :: rest).
        { rewrite -(Nat.add_1_r k) -drop_drop Hdrop. reflexivity. }
        assert (E : (2 + (UkShDiag.ush_Dg + (6 * length (c :: rest) + n)))%nat
                    = (6 + (2 + (UkShDiag.ush_Dg + (6 * length rest + n))))%nat)
          by (cbn [length]; lia).
        rewrite E.
        iApply (IH b c (S k) N' Hcst' h' m' q (rd γp) ∅ Hdrop' Ha0'
                  ltac:(discriminate)
                  with "Hleft Hlast Hent Hck Hjt2 Hqc Hsz Hstd Hcd1 Hcwd Hch
                        Hobl' Hrun").
    Qed.

  End Law.

  (* ===================================================================== *)
  (* §3 THE TAINT INSTANCE                                                  *)
  (* ===================================================================== *)

  (* the bundle at the FREE instance: [UkShPipe.wp_kshr_pipe_arm2]'s own
     discharge of the arm's premises, out of [UkSh.sh_deps] *)
  Lemma ush_node_obl_free (N : uk_names Σ) `{!ukn_const N} (ld : list fdstate)
      (szv cwdv : Z) (Sc : gset gname) (av : nat) :
    (⊢ ukn_pay N (-1)) ->
    fd_lowest_closed ld = None ->
    UkSh.sh_deps -∗
    shk_code (ukn_t N) -∗
    ush_jtab (ukn_t N) -∗
    □ (app_taint -∗ ukn_pay N (-1)) -∗
    app_taint -∗
    udepw_law 21 -∗
    ush_node_obl N ld szv cwdv Sc av (ukn_pay N)
      (fun _ => emp)%I (fun _ => emp)%I.
  Proof using Hpsok_free.
    intros Hpx Hnone.
    iIntros "#Hdp #Hcode #Hjt #Hkw #Hkc #Hcw".
    iDestruct (UkSh.ush_jtab_ro with "Hjt") as "#Hro".
    rewrite /ush_node_obl.
    iExists emp%I, emp%I, uwait_ans, (fun _ => emp%I), (fun _ => emp%I),
      (fun _ => ukn_pay N (-1)).
    iSplitR; [ iExact "Hkw" | ].
    iSplitR; [ done | ].
    iSplitR.
    { iIntros (γp) "_ _".
      iSplitR; [ done | ]. iSplitR; [ done | ]. iSplitR; [ done | ].
      iApply Hpx. }
    iSplitR.
    { iApply (ush_pipe_call_of_leaf Hpsok_free N ld Hnone with "Hkc Hcw"). }
    iSplitR; [ done | ].
    iSplitR; [ iApply (ush_wait0_law_free Hpsok_free N) | ].
    iSplitR.
    { (* panic("pipe") *)
      iIntros "!>" (h' m') "%Ha0' Hstd' _ Hrun'".
      iDestruct Hpx as "Hpay".
      iApply (UkShDiag.ush_diag_leaf_holds N h' m' ShSyms.panic (2 + av)%nat
                ltac:(left; split;
                      [ reflexivity | right; right; exact Ha0' ])
                with "Hdp Hcode Hro [] Hpay Hrun'").
      rewrite UkShRun.ush_diag_res_panic. done. }
    iSplitR.
    { (* the first fork1's panic("fork") *)
      iIntros "!>" (h' m' r γp) "%Ha0' %Hr' _ Hstd' _ Hpayv Hrun'".
      iApply (UkShDiag.ush_diag_leaf_holds N h' m' ShSyms.panic av
                ltac:(left; split; [ reflexivity | left; exact Ha0' ])
                with "Hdp Hcode Hro [] Hpayv Hrun'").
      rewrite UkShRun.ush_diag_res_panic. done. }
    iSplitR.
    { (* the second fork1's panic("fork") *)
      iIntros "!>" (h' m' r γp S1) "%Ha0' %Hr' _ Hstd' Hpayv Hrun'".
      iApply (UkShDiag.ush_diag_leaf_holds N h' m' ShSyms.panic av
                ltac:(left; split; [ reflexivity | left; exact Ha0' ])
                with "Hdp Hcode Hro [] Hpayv Hrun'").
      rewrite UkShRun.ush_diag_res_panic. done. }
    (* the parent: 0xea  c.li a0,0 ; 0xec  jal ra,<exit> *)
    iIntros (h' m' γp r1 r2 rw1 rw2 S1 S2 S3 S4)
      "_ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun".
    iApply (UkShRun.wp_kshr_exit0 N h' m' 0xea 0xec 0xf0
              (mword_of_int 0 : mword 6) (mword_of_int 2970 : mword 21)
              (2 + (UkShDiag.ush_Dg + av))%nat Hpx
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcode [] [] Hrun").
    { iApply (uis_shk_ea with "Hcode"). }
    { iApply (uis_shk_ec with "Hcode"). }
  Qed.

  (* THE LAW'S PREMISES ARE SATISFIABLE: [UkShPipe.
     wp_kshr_runcmd_pipes_closed]'s consumer test, re-proved through §2 --
     every stage law is [UkShDiag.wp_kshr_runcmd_final] and the entry law
     is [ush_node_obl_free] at the forked child. *)
  Lemma wp_kshr_runcmd_pipes_free (a b : list uarg) (rest : list (list uarg))
      (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
      (t szv cwdv : Z) (ld : list fdstate) (st0 st1 : fdstate)
      (Sc : gset gname) (n : nat) :
    (⊢ ukn_pay N (-1)) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    fd_lowest_closed ld = None ->
    UkSh.sh_deps -∗
    shk_code (ukn_t N) -∗
    uxsup_at (ukn_pay N) -∗
    □ (app_taint -∗ ukn_pay N (-1)) -∗
    app_taint -∗
    udepw_law 21 -∗
    ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (ush_pipes a (b :: rest)) -∗
    usz (ukn_s N) szv -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    UserChildren.uch (ukn_ch N) Sc -∗
    urun N h m (mword_of_int ShSyms.runcmd)
      (6 + (2 + (UkShDiag.ush_Dg + (6 * length rest + (6 + n))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hpx Ha0 Hl0 Hl1 Hne0 Hne1 Hnp1 Hnone.
    iIntros "#Hdp #Hcode #Hexs #Hkw #Hkc #Hcw #Hjt #Htree Hsz Hstd Hcwd Hch
             Hrun".
    assert (Hl0len : (0 < length ld)%nat)
      by exact (lookup_lt_Some ld 0%nat st0 Hl0).
    iAssert (UserFd.ustd (ukn_fd N) (<[0%nat := st0]> ld)) with "[Hstd]"
      as "Hstd".
    { rewrite (list_insert_id ld 0%nat st0 Hl0). iExact "Hstd". }
    iApply (wp_kshr_runcmd_pipes_law (a :: b :: rest) ld st1 szv cwdv (6 + n)
              (fun _ _ => ukn_pay N) (fun _ _ _ => emp%I) (fun _ _ _ => emp%I)
              (fun _ _ x y => ukn_const_eq (N := N) x y) Hl1 Hne1 Hnp1 Hl0len
              rest a b 0%nat N h m t st0 Sc eq_refl Ha0 Hne0
              with "[] [] [] Hcode Hjt Htree Hsz Hstd [] Hcwd Hch [] Hrun").
    - (* the LEFT stages: the landed EXEC walk *)
      iModIntro. rewrite /ush_left_law.
      iIntros (k st0' args N' h' m' γ' γp q av)
        "%Hk %Hlt %Hav %Hpeq %Ha0' _ #Hck #Hjt2 #Hqc Hsz Hstd Hcwd Hch
         _ _ _ Hrun".
      cbv beta in Hpeq.
      pose proof (ukn_const_of_eq N' (ukn_pay N) Hpeq (ukn_const_eq (N := N))) as Hcst'.
      assert (Hpx' : ⊢ ukn_pay N' (-1)) by (rewrite Hpeq; exact Hpx).
      iAssert (□ (app_taint -∗ ukn_pay N' (-1)))%I as "#Hkw'".
      { rewrite Hpeq. iExact "Hkw". }
      iAssert (uxsup_at (ukn_pay N')) as "#Hexs'".
      { rewrite Hpeq. iExact "Hexs". }
      replace (2 + (UkShDiag.ush_Dg + av))%nat
        with (6 * ush_ht (UExec args)
              + (2 + (UkShDiag.ush_Dg + (av - 6))))%nat
        by (cbn [ush_ht]; lia).
      iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free (UExec args)
                (ush_rstage_simple (UExec args) I)
                N' h' m' q szv _ (av - 6)%nat Hpx' Ha0'
                with "Hdp Hck Hexs' Hkw' Hjt2 Hqc Hsz Hstd [Hcwd] [Hch] Hrun").
      { iApply (UserCwd.ucwd_any_of with "Hcwd"). }
      { iApply (UserChildren.uch_any_of with "Hch"). }
    - (* the LAST stage: the landed EXEC walk *)
      iModIntro. rewrite /ush_last_law.
      iIntros (k st0' args N' h' m' γ' γp q av)
        "%Hk %Hlt %Hav %Hpeq %Ha0' _ #Hck #Hjt2 #Hqc Hsz Hstd Hcwd Hch
         _ _ _ Hrun".
      cbv beta in Hpeq.
      pose proof (ukn_const_of_eq N' (ukn_pay N) Hpeq (ukn_const_eq (N := N))) as Hcst'.
      assert (Hpx' : ⊢ ukn_pay N' (-1)) by (rewrite Hpeq; exact Hpx).
      iAssert (□ (app_taint -∗ ukn_pay N' (-1)))%I as "#Hkw'".
      { rewrite Hpeq. iExact "Hkw". }
      iAssert (uxsup_at (ukn_pay N')) as "#Hexs'".
      { rewrite Hpeq. iExact "Hexs". }
      replace (2 + (UkShDiag.ush_Dg + av))%nat
        with (6 * ush_ht (UExec args)
              + (2 + (UkShDiag.ush_Dg + (av - 6))))%nat
        by (cbn [ush_ht]; lia).
      iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free (UExec args)
                (ush_rstage_simple (UExec args) I)
                N' h' m' q szv _ (av - 6)%nat Hpx' Ha0'
                with "Hdp Hck Hexs' Hkw' Hjt2 Hqc Hsz Hstd [Hcwd] [Hch] Hrun").
      { iApply (UserCwd.ucwd_any_of with "Hcwd"). }
      { iApply (UserChildren.uch_any_of with "Hch"). }
    - (* the ENTRY: the free bundle at the forked child *)
      iModIntro. rewrite /ush_entry_law.
      iIntros (k st0' N' γ' γp av) "%Hlt %Hav %Hpeq _ _ #Hck #Hjt2".
      cbv beta in Hpeq |- *.
      pose proof (ukn_const_of_eq N' (ukn_pay N) Hpeq (ukn_const_eq (N := N))) as Hcst'.
      assert (Hpx' : ⊢ ukn_pay N' (-1)) by (rewrite Hpeq; exact Hpx).
      iAssert (□ (app_taint -∗ ukn_pay N' (-1)))%I as "#Hkw'".
      { rewrite Hpeq. iExact "Hkw". }
      iModIntro. rewrite -Hpeq.
      iApply (ush_node_obl_free N' _ szv cwdv ∅ av Hpx'
                (ush_fd_lowest_insert0 ld (FdOpen true false (FdPipe γp))
                   ltac:(discriminate) Hnone)
                with "Hdp Hck Hjt2 Hkw' Hkc Hcw").
    - iApply (ush_cldep_of_law with "Hcw").
    - (* the top node's bundle *)
      cbv beta.
      iApply (ush_node_obl_free N _ szv cwdv Sc _ Hpx
                (ush_fd_lowest_insert0 ld st0 Hne0 Hnone)
                with "Hdp Hcode Hjt Hkw Hkc Hcw").
  Qed.

  (* ===================================================================== *)
  (* §1 THE CHILD WALK: 0x9c0 TO runcmd, ANY NUMBER OF STAGES               *)
  (* ===================================================================== *)
  Section Child.
    Context (N : uk_names Σ).
    Context `{Hpay : !ukn_const N}.
    Local Notation γt := (ukn_t N).
    Local Notation γd := (ukn_d N).
    Local Notation γs := (ukn_s N).
    Local Notation γfd := (ukn_fd N).
    Local Notation γcwd := (ukn_cwd N).
    Local Notation γch := (ukn_ch N).
    Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

    Context (UM : nat -> iProp Σ) (K : nat).
    Hypothesis Hchain :
      forall i : nat, (i < K)%nat -> ushp_malloc_ty (UM i) (UM (S i)).

    (* the stages' argument lists, cut from the one line *)
    Definition ushq_stages (s0 : Z) (len : nat) (f : nat -> bv 8)
        (a : list (nat * nat)) (rest : list (list (nat * nat)))
        : ushcmd :=
      ush_pipes (ush_args s0 (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f)) a)
        (map (ush_args s0 (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f)))
           rest).

    Lemma wp_kshm_child_pipes_g (h : CpuId) (m : regfile) (dw dv : dfrac)
        (s0 : Z) (len : nat) (f : nat -> bv 8)
        (a : list (nat * nat)) (rest : list (list (nat * nat))) (i k : nat)
        (Cp : iProp Σ) :
      ushq_bars len f 0%nat a rest ->
      (i + 2 * length rest + 1 <= K)%nat ->
      m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
      0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
      shk_code γt -∗
      shp_code γt -∗ shp_rodata γt -∗
      ustr γd (DfracOwn 1) s0 len f -∗
      ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
      ustr γd dv ushp_symbols 7 ushp_sym_f -∗
      UM i -∗
      (* the parse's payer, whole across [parsecmd] *)
      Cp -∗
      □ (Cp -∗ ukn_pay N (-1)) -∗
      urun N h m (mword_of_int 0x9c0) (68 + (length rest * 6 + k)) -∗
      (∀ (h' : CpuId) (m' : regfile) (q : Z),
         ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
         ush_cmd γd q (ushq_stages s0 len f a rest) -∗
         ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
         ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         UM (i + 2 * length rest + 1) -∗
         Cp -∗
         urun N h' m' (mword_of_int ShSyms.runcmd)
           (68 + (length rest * 6 + k)) -∗
         mWP (Loop : expr riscv_lang)) -∗
      mWP (Loop : expr riscv_lang).
    Proof using Hchain.
      intros Hbars HK Hs1 Hs0 Hs64 Hs38.
      iIntros "#Hcode #Hpcode #Hpro Hline Hws Hsy HM Hcp #Hpxw Hrun Hcont".
      iDestruct (ustr_nonul with "Hline") as %Hnn0.
      iDestruct (ustr_len with "Hline") as %Hlen31.
      (* ---- 0x9c0  c.mv a0,s1 ---- *)
      iApply (wp_uk_cmv N h m (mword_of_int 0x9c0) a0_idx s1_idx
                (add_vec zero_reg (m !!! Regidx s1_idx))
                (68 + (length rest * 6 + k))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
      { iApply (uis_shk_9c0 with "Hcode"). }
      assert (E9c0 : add_vec_int (mword_of_int 0x9c0 : mword 64) 2
                     = mword_of_int 0x9c2)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E9c0. iIntros (h1) "Hrun".
      set (m1 := <[Regidx a0_idx
                   := regval_into_reg (add_vec zero_reg (m !!! Regidx s1_idx))]> m).
      assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int s0 : mword 64)).
      { rewrite /m1 (upd_eq m (Regidx a0_idx) _).
        rewrite Hs1. apply bv_eq. rewrite add_vec_unsigned.
        unfold bv_wrap. cbn [bv_unsigned]. rewrite Z.add_0_l.
        rewrite Z.mod_small; [ reflexivity | ].
        pose proof (bv_unsigned_in_range _ (mword_of_int s0 : mword 64)) as Hr.
        assert (Hm : bv_modulus (MachineWord.Z_idx 64) = 18446744073709551616%Z)
          by (vm_compute; reflexivity).
        rewrite Hm in Hr. exact Hr. }
      (* ---- 0x9c2  jal ra,parsecmd ---- *)
      iApply (wp_uk_jal N h1 m1 (mword_of_int 0x9c2)
                (mword_of_int 2096812 : mword 21) (mword_of_int 1 : mword 5)
                (mword_of_int ShSyms.parsecmd) (mword_of_int 0x9c6)
                (68 + (length rest * 6 + k))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_9c2 with "Hcode"). }
      iIntros (h2) "Hrun".
      set (m2 := <[Regidx (mword_of_int 1 : mword 5)
                   := regval_into_reg (mword_of_int 0x9c6 : mword 64)]> m1).
      assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
        by (rewrite /m2 (upd_ne m1 (Regidx (mword_of_int 1 : mword 5))
                           (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
            exact Ha0_1).
      assert (Hra_2 : ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))
                      = (mword_of_int 0x9c6 : mword 64))
        by (rewrite /m2 (upd_eq m1 (Regidx (mword_of_int 1 : mword 5)) _);
            apply bv_eq; vm_compute; reflexivity).
      (* ---- parsecmd, at any number of bars: the payer crosses it whole ---- *)
      iApply (UkShPipesCmd.wp_kshp_parsecmd_pipes N UM K Hchain h2 m2 dw dv
                s0 len f a rest i k Hbars HK Ha0_2 Hs0 Hs64
                with "Hpcode Hpro Hline Hws Hsy HM Hpxw Hcp Hrun").
      iIntros (p) "Htree Hbytes Hws Hsy".
      iIntros (h3 m3) "%Hcs3 %Ha0_3 HM3 Hcp Hrun".
      rewrite Hra_2.
      (* ---- 0x9c6  jal ra,runcmd ---- *)
      iApply (wp_uk_jal N h3 m3 (mword_of_int 0x9c6)
                (mword_of_int 2094792 : mword 21) (mword_of_int 1 : mword 5)
                (mword_of_int ShSyms.runcmd) (mword_of_int 0x9ca)
                (68 + (length rest * 6 + k))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_9c6 with "Hcode"). }
      iIntros (h4) "Hrun".
      set (m4 := <[Regidx (mword_of_int 1 : mword 5)
                   := regval_into_reg (mword_of_int 0x9ca : mword 64)]> m3).
      assert (Ha0_4 : m4 !!! Regidx a0_idx = (mword_of_int p : mword 64))
        by (rewrite /m4 (upd_ne m3 (Regidx (mword_of_int 1 : mword 5))
                           (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
            exact Ha0_3).
      (* ---- THE SEAM, at every node of the spine ---- *)
      iMod (UkShMain.ubytes_persist γd s0 (S len)
              (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f))
              with "Hbytes") as "#Hbytesq".
      iMod (UkShPipesSeam.ush_cmd_of_ushp_pipes N h4 m4
              (mword_of_int ShSyms.runcmd) (68 + (length rest * 6 + k))
              s0 len (ushq_nulfolds a rest (UkShParseCmd.ushp_ext len f))
              Hlen31 Hs0 Hs38 rest a p
              (ushq_cuts_ok_bars len f 0%nat a rest Hnn0 Hbars)
              with "Hrun Htree Hbytesq") as "(Hrun & #Hcmd)".
      iApply ("Hcont" $! h4 m4 p with "[] Hcmd Hws Hsy HM3 Hcp Hrun").
      iPureIntro. exact Ha0_4.
    Qed.

    (* ...AND THE WHOLE TREE AT THE TAINT INSTANCE: from the raw bytes of a
       line of two or more stages at 0x9c0, sh's forked child parses it and
       every process of the pipeline runs to its exit.  The break comes out
       of what the parse left ([UShPipeLaw.pl_usz_of_one]'s reading, a
       premise here). *)
    Lemma wp_kshm_child_pipes_closed (h : CpuId) (m : regfile)
        (dw dv : dfrac) (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
        (a b : list (nat * nat)) (rest : list (list (nat * nat)))
        (i k : nat) (ld : list fdstate) (st0 st1 : fdstate)
        (Sc : gset gname) :
      ushq_bars len f 0%nat a (b :: rest) ->
      (i + 2 * length (b :: rest) + 1 <= K)%nat ->
      m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
      0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
      (⊢ ukn_pay N (-1)) ->
      (⊢ UM (i + 2 * length (b :: rest) + 1) -∗ usz γs szv) ->
      ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
      st0 <> FdClosed -> st1 <> FdClosed ->
      (forall (rb wb : bool) (gp : pipe_names),
         st1 <> FdOpen rb wb (FdPipe gp)) ->
      fd_lowest_closed ld = None ->
      UkSh.sh_deps -∗
      shk_code γt -∗
      shp_code γt -∗ shp_rodata γt -∗
      uxsup_at (ukn_pay N) -∗
      □ (app_taint -∗ ukn_pay N (-1)) -∗
      app_taint -∗
      udepw_law 21 -∗
      ush_jtab γt -∗
      ustr γd (DfracOwn 1) s0 len f -∗
      ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
      ustr γd dv ushp_symbols 7 ushp_sym_f -∗
      UM i -∗
      UserFd.ustd γfd ld -∗
      UserCwd.ucwd γcwd cwdv -∗
      UserChildren.uch γch Sc -∗
      urun N h m (mword_of_int 0x9c0)
        (68 + (length (b :: rest) * 6 + k)) -∗
      mWP (Loop : expr riscv_lang).
    Proof using Hpay Hpsok_free Hchain.
      intros Hbars HK Hs1 Hs0 Hs64 Hs38 Hpx Hszof Hl0 Hl1 Hne0 Hne1 Hnp1
        Hnone.
      iIntros "#Hdp #Hcode #Hpcode #Hpro #Hexs #Hkw #Hkc #Hcw #Hjt Hline Hws
               Hsy HM Hstd Hcwd Hch Hrun".
      iApply (wp_kshm_child_pipes_g h m dw dv s0 len f a (b :: rest) i k emp%I
                Hbars HK Hs1 Hs0 Hs64 Hs38
                with "Hcode Hpcode Hpro Hline Hws Hsy HM [] [] Hrun
                      [Hstd Hcwd Hch]").
      { done. }
      { iIntros "!> _". iApply Hpx. }
      iIntros (h' m' q) "%Ha0' #Hcmd _ _ HM3 _ Hrun".
      iPoseProof (Hszof with "HM3") as "Hsz".
      set (g := ushq_nulfolds a (b :: rest) (UkShParseCmd.ushp_ext len f)).
      change (ushq_stages s0 len f a (b :: rest))
        with (ush_pipes (ush_args s0 g a)
                (ush_args s0 g b :: map (ush_args s0 g) rest)).
      assert (E : (68 + (length (b :: rest) * 6 + k))%nat
                  = (6 + (2 + (UkShDiag.ush_Dg
                               + (6 * length (map (ush_args s0 g) rest)
                                  + (6 + (32 + k))))))%nat)
        by (rewrite length_map; cbn [length]; unfold UkShDiag.ush_Dg; lia).
      rewrite E.
      iApply (wp_kshr_runcmd_pipes_free (ush_args s0 g a) (ush_args s0 g b)
                (map (ush_args s0 g) rest) N h' m' q szv cwdv ld st0 st1 Sc
                (32 + k) Hpx Ha0' Hl0 Hl1 Hne0 Hne1 Hnp1 Hnone
                with "Hdp Hcode Hexs Hkw Hkc Hcw Hjt Hcmd Hsz Hstd Hcwd Hch
                      Hrun").
    Qed.

  End Child.

  (* ...AT THE LANDED ALLOCATOR: [UkShPipesSeam.ushq_um_chain] from the
     fresh heap -- 340 links, so every line of up to 170 stages -- whose
     every link after the first holds the break the pipe arm wants
     ([UShPipeLaw.pl_usz_of_one]'s reading).  Nothing of the chain is a
     premise any more. *)
  Lemma ushq_um_usz (N : uk_names Σ) (sz : Z) (j : nat) :
    ⊢ UkShPipesSeam.ushq_um N sz (S j) -∗ usz (ukn_s N) (sz + 65536).
  Proof using .
    iIntros "H". rewrite /UkShPipesSeam.ushq_um.
    rewrite /UkShMalloc.ushm_one_ge. iDestruct "H" as (R) "[_ H]".
    rewrite /UkShMalloc.ushm_one.
    iDestruct "H" as (c) "(_ & _ & _ & _ & _ & $)".
  Qed.

  Lemma wp_kshm_child_pipes_closed_um (N : uk_names Σ) `{!ukn_const N}
      (sz : Z) (h : CpuId) (m : regfile) (dw dv : dfrac) (s0 cwdv : Z)
      (len : nat) (f : nat -> bv 8)
      (a b : list (nat * nat)) (rest : list (list (nat * nat)))
      (k : nat) (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) :
    8328 + 16 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (2 * length (b :: rest) + 1 <= 340)%nat ->
    ushq_bars len f 0%nat a (b :: rest) ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (⊢ ukn_pay N (-1)) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    fd_lowest_closed ld = None ->
    UkSh.sh_deps -∗
    shk_code (ukn_t N) -∗
    shp_code (ukn_t N) -∗ shp_rodata (ukn_t N) -∗
    uxsup_at (ukn_pay N) -∗
    □ (app_taint -∗ ukn_pay N (-1)) -∗
    app_taint -∗
    udepw_law 21 -∗
    ush_jtab (ukn_t N) -∗
    ustr (ukn_d N) (DfracOwn 1) s0 len f -∗
    ustr (ukn_d N) dw ushp_whitespace 5 ushp_ws_f -∗
    ustr (ukn_d N) dv ushp_symbols 7 ushp_sym_f -∗
    UkShMalloc.ushm_fresh N sz -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    UserChildren.uch (ukn_ch N) Sc -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (length (b :: rest) * 6 + k)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hszlo Hszal Hszok HK Hbars Hs1 Hs0 Hs64 Hs38 Hpx Hl0 Hl1 Hne0
      Hne1 Hnp1 Hnone.
    iIntros "Hdp Hcode Hpcode Hpro Hexs Hkw Hkc Hcw Hjt Hline Hws Hsy HM
             Hstd Hcwd Hch Hrun".
    iApply (wp_kshm_child_pipes_closed N (UkShPipesSeam.ushq_um N sz) 340
              (UkShPipesSeam.ushq_um_chain N Hpsok_free sz Hszlo Hszal Hszok)
              h m dw dv s0 (sz + 65536) cwdv len f a b rest 0%nat k
              ld st0 st1 Sc Hbars ltac:(lia) Hs1 Hs0 Hs64 Hs38 Hpx
              (ushq_um_usz N sz _) Hl0 Hl1 Hne0 Hne1 Hnp1 Hnone
              with "Hdp Hcode Hpcode Hpro Hexs Hkw Hkc Hcw Hjt Hline Hws Hsy
                    HM Hstd Hcwd Hch Hrun").
  Qed.

End UkShPipesRound.
