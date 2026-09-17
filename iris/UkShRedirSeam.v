(* ===================================================================== *)
(* UkShRedirSeam.v -- the SEAM and the CHILD at the redirect shape,       *)
(* lane SH-PARSE-2 (design/app-file.md SS5.1).                            *)
(*                                                                        *)
(* [UkShMain.ush_cmd_of_ushp] turns the parser's EXEC node into the       *)
(* runner's tree; this file does the same for a REDIR node over one.  The *)
(* exec half is [UkShMain.ush_cmd_of_ushp_gen] -- the conversion at what   *)
(* it actually needs, which is three facts about the cut line and not the *)
(* cut itself -- and what is added here is the REDIR node's own five      *)
(* fields and the FILE NAME as a [UserHeap.uarg].                          *)
(*                                                                        *)
(* THE SEPARATION FACT IS REUSED, NOT RE-PROVED.  The argument tokens all *)
(* end below the '>', and every scan that measures them stops below it    *)
(* too, so they are [ushp_tokens] of the line TRUNCATED at the '>' --     *)
(* whose only symbol byte is the one the truncation cut off.  That is     *)
(* [ushs_toks_below], and it puts [UkShMain.ushp_tokens_gap] back in      *)
(* scope unchanged.                                                       *)
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
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShRedirCmd.
Require Import UkShRedirPc.
Require Import UkShRedir.
Require Import UkShLoop.
Require Import UkShRedirLine.
Require Import LineWords.
Require Import UkShMain.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShRedirSeam.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* the four ghost names a program proof runs at, as every file in the
     lane binds them *)
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_triv]). *)
  Context `{Hpay : !ukn_const N}.
  (* THE CHILD'S PAYLOAD IS NOT TRIVIAL ANY MORE (lane IO-LEAF, M3b).
     There used to be a second class here, [UkRun.ukn_triv N], because the
     generic exec supply [UkRun.uxsup] is the exec bundle at the trivial
     payload and this file walks the process sh FORKED.  A child that has
     to ECHO A LINE cannot be at the trivial payload: what it owes its
     parent is the era's credential at the alternative it took.  So the
     two things the class was used for -- the free exit row and the exec
     supply -- are PREMISES of the two lemmas below, at whatever payload
     sh chose for its child. *)
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

(*ALIASES-BEGIN*)

  (* ===================================================================== *)
  (* §1 THE TOKEN MODEL, RESTRICTED TO THE PREFIX BEFORE THE '>'.           *)
  (*                                                                       *)
  (* The argument tokens of `w1 ... wn > f' all end before the '>', and     *)
  (* every scan that measures them stops before it too -- so they are       *)
  (* [UkShParse.ushp_tokens] of the line TRUNCATED at [gp], whose symbol    *)
  (* byte is the one the truncation cut off.  That is what lets the         *)
  (* separation fact ([UkShMain.ushp_tokens_gap]) be REUSED rather than     *)
  (* re-proved: it is a fact about token indices, and the indices are the   *)
  (* same on both readings.                                                 *)
  (* ===================================================================== *)

  Lemma ushs_skipws_trunc (n n' i : nat) (f : nat -> bv 8) :
    (n' <= n)%nat -> (ushp_skipws n i f <= n')%nat ->
    ushp_skipws n' i f = ushp_skipws n i f.
  Proof using .
    revert n i. induction n' as [| n' IH ]; intros n i Hle Hb.
    - cbn [ushp_skipws]. lia.
    - destruct n as [| n ]; [ lia | ].
      cbn [ushp_skipws] in Hb |- *.
      destruct (ushp_is_ws (f i)) eqn:Hw; [ | reflexivity ].
      f_equal. apply IH; lia.
  Qed.

  Lemma ushs_toklen_trunc (n n' i : nat) (f : nat -> bv 8) :
    (n' <= n)%nat -> (ushp_toklen n i f <= n')%nat ->
    ushp_toklen n' i f = ushp_toklen n i f.
  Proof using .
    revert n i. induction n' as [| n' IH ]; intros n i Hle Hb.
    - cbn [ushp_toklen]. lia.
    - destruct n as [| n ]; [ lia | ].
      cbn [ushp_toklen] in Hb |- *.
      destruct (ushp_is_ws (f i) || ushp_is_sym (f i)) eqn:Hw;
        [ reflexivity | ].
      f_equal. apply IH; lia.
  Qed.

  Lemma ushs_toks_below (len gp : nat) (f : nat -> bv 8) (off : nat)
      (toks : list (nat * nat)) :
    (off <= gp)%nat -> (gp <= len)%nat ->
    ushs_toks len f gp off toks -> ushp_tokens gp f off toks.
  Proof using .
    intros Hoff Hgp H. revert Hoff.
    induction H as [ off Hnil | off toks k n Hn Htoks IH ]; intro Hoff.
    - apply UshpTokNil.
      rewrite (ushs_skipws_trunc (len - off) (gp - off) off f
                 ltac:(lia) ltac:(lia)). exact Hnil.
    - assert (Hle : (off + k + n <= gp)%nat)
        by exact (ushs_toks_le len f gp (off + k + n)%nat toks Htoks).
      assert (Ek : ushp_skipws (gp - off) off f = k)
        by exact (ushs_skipws_trunc (len - off) (gp - off) off f
                    ltac:(lia) ltac:(lia)).
      assert (En : ushp_toklen (gp - (off + k)) (off + k) f = n)
        by exact (ushs_toklen_trunc (len - (off + k)) (gp - (off + k))
                    (off + k) f ltac:(lia) ltac:(lia)).
      assert (C := UshpTokCons gp f off toks).
      cbv zeta in C. rewrite Ek En in C.
      exact (C Hn (IH ltac:(lia))).
  Qed.


  (* ===================================================================== *)
  (* §2 THE SEAM AT THE REDIRECT SHAPE.                                     *)
  (*                                                                       *)
  (* [UkShMain.ush_cmd_of_ushp_gen] does the exec node; what is left is the *)
  (* REDIR node's own five fields and the FILE NAME as a string.  The cut   *)
  (* the redirect parse leaves is one byte longer than the symbol-free one  *)
  (* -- nulterminate's REDIR arm zeroes [efile] too -- and that byte is     *)
  (* exactly what terminates the file name.                                 *)
  (* ===================================================================== *)

  Local Notation ushs_nulcut := UkShRedirPc.ushs_nulcut.

  (* the file name, as the runner reads it *)
  Definition ushs_file (s0 : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat) : uarg :=
    UArg (s0 + Z.of_nat (S (S gp))) (fe - S (S gp))%nat
         (fun j : nat => ushs_nulcut args len f fe (S (S gp) + j)%nat).

  (* no argument token's end lands inside another token's body -- the
     separation fact, on the TRUNCATED line, where it is stage 4's own *)
  Lemma ushs_arg_gap (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
    forall (q : nat) (t : nat * nat), args !! q = Some t ->
    forall x : nat, (fst tk <= x < snd tk)%nat -> x <> snd t.
  Proof using .
    intros Hred Htoks.
    assert (Hgl : (gp < len)%nat) by exact (ushs_redir_lt len f gp fe Hred).
    exact (UkShMain.ushp_tokens_gap gp f 0%nat args
             (ushs_one_nosym_below len f gp (ushs_redir_one len f gp fe Hred))
             (ushs_toks_below len gp f 0%nat args ltac:(lia) ltac:(lia) Htoks)
             ltac:(lia)).
  Qed.

  (* ...and every argument lies strictly below the '>' *)
  Lemma ushs_arg_below (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
      (fst tk < snd tk)%nat /\ (snd tk <= gp)%nat.
  Proof using .
    intros Hred Htoks i tk Hi.
    assert (Hgl : (gp < len)%nat) by exact (ushs_redir_lt len f gp fe Hred).
    destruct (ushp_tokens_in gp f 0%nat args
                (ushs_toks_below len gp f 0%nat args ltac:(lia) ltac:(lia)
                   Htoks) ltac:(lia) i tk Hi) as [ Hlo Hhi ].
    split; lia.
  Qed.

  Lemma ushs_nulcut_body (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
    forall j : nat, (j < snd tk - fst tk)%nat ->
      ushs_nulcut args len f fe (fst tk + j)%nat <> ubyte0.
  Proof using .
    intros Hred Htoks Hnn i tk Hi j Hj.
    destruct (ushs_arg_below len f gp fe args Hred Htoks i tk Hi)
      as [ Hlo Hhi ].
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    rewrite /ushs_nulcut /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq (fst tk + j)%nat fe) ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
               (fst tk + j)%nat
               ltac:(intros q t Hq;
                     exact (ushs_arg_gap len f gp fe args Hred Htoks
                              i tk Hi q t Hq (fst tk + j)%nat ltac:(lia)))).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((fst tk + j) < len)%nat ltac:(lia)).
    apply Hnn. lia.
  Qed.

  Lemma ushs_nulcut_filebody (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (args : list (nat * nat)) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    forall j : nat, (j < fe - S (S gp))%nat ->
      ushs_nulcut args len f fe (S (S gp) + j)%nat <> ubyte0.
  Proof using .
    intros Hred Htoks Hnn j Hj.
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    rewrite /ushs_nulcut /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq (S (S gp) + j)%nat fe) ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
               (S (S gp) + j)%nat
               ltac:(intros q t Hq;
                     destruct (ushs_arg_below len f gp fe args Hred Htoks
                                 q t Hq) as [ _ Hhi ]; lia)).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((S (S gp) + j) < len)%nat ltac:(lia)).
    apply Hnn. lia.
  Qed.

  (* the REDIR row, INTRODUCED rather than unfolded: [c1] is a variable
     here, so [cbn] reduces the outer node and cannot touch the sub-tree *)
  Lemma ush_cmd_redir_intro (g : gname) (t q : Z) (c1 : ushcmd)
      (file : uarg) (mode fd : Z) :
    0 < t < 2 ^ 38 -> t mod 8 = 0 ->
    ush_w32 g t 2 -∗ ush_ptr g (t + 8) q -∗ ush_cmd g q c1 -∗
    ush_ptr g (t + 16) (ua_ptr file) -∗ ush_str g file -∗
    ush_w32 g (t + 32) mode -∗ ush_w32 g (t + 36) fd -∗
    ush_cmd g t (URedir c1 file mode fd).
  Proof using .
    intros Ht38 Ht8.
    iIntros "#Hty #Hp #Hc #Hfp #Hfs #Hm #Hf".
    cbn [ush_cmd ush_ty].
    iSplit; [ iPureIntro; exact Ht38 | ].
    iSplit; [ iPureIntro; exact Ht8 | ].
    iSplit; [ iExact "Hty" | ].
    iSplit; [ iExists q; iSplit; [ iExact "Hp" | iExact "Hc" ] | ].
    iSplit; [ iExact "Hfp" | ].
    iSplit; [ iExact "Hfs" | ].
    iSplit; [ iExact "Hm" | iExact "Hf" ].
  Qed.

  (* THE CONVERSION at the redirect shape. *)
  Lemma ush_cmd_of_ushs_redir (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 t pe : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat) :
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    urun N h m pc avail -∗
    UkShRedirCmd.ushp_redir_node N s0 t pe (S (S gp)) fe 1537 1 -∗
    UkShParse.ushp_tree N s0 pe (UshpExec args) -∗
    ubytes γd s0 (S len) (ushs_nulcut args len f fe) ==∗
    urun N h m pc avail ∗
    ush_cmd γd t
      (URedir (UExec (ush_args s0 (ushs_nulcut args len f fe) args))
              (ushs_file s0 len f args gp fe) 1537 1).
  Proof using .
    intros Hred Htoks Hnn Hlen31 Hs0 Hs0hi.
    pose proof Hred as HR.
    destruct HR as (Hone & Hgp0 & Hb1 & Hb2 & Hlo2 & Hhi2 & Hfw & Htail).
    assert (Hgl : (gp < len)%nat) by exact (ushs_redir_lt len f gp fe Hred).
    iIntros "Hrun Hn Hnode Hline".
    iMod (UkShMain.ubytes_persist γd s0 (S len) _ with "Hline") as "#Hline".
    rewrite /UkShRedirCmd.ushp_redir_node.
    iDestruct "Hn" as "(%Ht0 & %Ht8 & %Htz & [Hty Hpad] & Hcmd & Hfile
                        & Hefile & Hmode & Hfd)".
    iClear "Hpad". iClear "Hefile".
    iDestruct (UkShMain.urun_ubytes_bnd N h m pc avail t 4 _ with "Hrun Hty")
      as %Htb.
    assert (Ht38 : 0 < t < 2 ^ 38)
      by (split; [ exact Ht0
                 | destruct (Htb 0%nat ltac:(lia)) as [ _ Hh ]; lia ]).
    iMod (UkShMain.ush_cmd_of_ushp_gen N h m pc avail s0 pe len
            (ushs_nulcut args len f fe) args
            ltac:(intros i tk Hi;
                  destruct (ushs_arg_below len f gp fe args Hred Htoks i tk Hi)
                    as [ Hl Hh ]; split; lia)
            ltac:(intros i tk Hi;
                  exact (UkShRedirPc.ushs_nulcut_arg args len f fe i tk Hi))
            ltac:(exact (ushs_nulcut_body len f gp fe args Hred Htoks Hnn))
            Hlen31 Hs0 Hs0hi
            with "Hrun Hnode Hline") as "(Hrun & #Hexec)".
    iMod (UkShMain.ubytes_persist γd t 4 _ with "Hty") as "#Htyq".
    iMod (UkShMain.uword_persist γd (t + 8) _ with "Hcmd") as "#Hcmdq".
    iMod (UkShMain.uword_persist γd (t + 16) _ with "Hfile") as "#Hfileq".
    iMod (UkShMain.ubytes_persist γd (t + 32) 4 _ with "Hmode") as "#Hmodeq".
    iMod (UkShMain.ubytes_persist γd (t + 36) 4 _ with "Hfd") as "#Hfdq".
    iAssert (ush_str γd (ushs_file s0 len f args gp fe))%I as "#Hfstr".
    { rewrite /ush_str /ushs_file. cbn [ua_ptr ua_len ua_bytes].
      iSplit; [ iPureIntro; lia | ].
      rewrite /ustr.
      iSplit;
        [ iPureIntro;
          exact (ushs_nulcut_filebody len f gp fe args Hred Htoks Hnn) | ].
      iSplit; [ iPureIntro; lia | ].
      iSplit.
      - iApply (UkShMain.ubytesq_sub γd s0 (S len)
                  (ushs_nulcut args len f fe) (S (S gp)) (fe - S (S gp))%nat
                  ltac:(lia) with "Hline").
      - iDestruct (UkShMain.ubytesq_at γd s0 (S len)
                     (ushs_nulcut args len f fe) fe ltac:(lia) with "Hline")
          as "Hb".
        rewrite (UkShRedirPc.ushs_nulcut_file args len f fe).
        assert (Ea : (s0 + Z.of_nat fe)%Z
                     = (s0 + Z.of_nat (S (S gp))
                        + Z.of_nat (fe - S (S gp)))%Z) by lia.
        iEval (rewrite Ea) in "Hb". iExact "Hb". }
    iModIntro. iFrame "Hrun".
    iApply (ush_cmd_redir_intro γd t pe
              (UExec (ush_args s0 (ushs_nulcut args len f fe) args))
              (ushs_file s0 len f args gp fe) 1537 1 Ht38 Ht8
              with "[] [] Hexec [] Hfstr [] []").
    - rewrite /ush_w32. iExact "Htyq".
    - rewrite /ush_ptr. iExact "Hcmdq".
    - rewrite /ush_ptr /ushs_file. cbn [ua_ptr]. iExact "Hfileq".
    - rewrite /ush_w32. iExact "Hmodeq".
    - rewrite /ush_w32. iExact "Hfdq".
  Qed.


  (* ===================================================================== *)
  (* §3 THE CHILD, at the redirect shape.                                   *)
  (*                                                                       *)
  (*   0x9c0  c.mv a0,s1        the line                                    *)
  (*   0x9c2  jal  ra,parsecmd  -> the REDIR node over the exec node        *)
  (*   0x9c6  jal  ra,runcmd    -> close(1), open(file), and the sub-tree   *)
  (*                                                                       *)
  (* [UkShMain.wp_kshm_child]'s two parser premises become [ushs_redir] /   *)
  (* [ushs_toks] (and the count is bounded BELOW as well, because the       *)
  (* redirect parse needs at least one argument), and ONE premise is new:   *)
  (* the open, as a CALL ([UkShRedir.ush_open_call]) at the file name the   *)
  (* line itself names.                                                     *)
  (*                                                                       *)
  (* THE TWO CAPABILITIES ARE BOUNDED (lane SH-MALLOC-3): each is           *)
  (* [UkShParse.ushp_malloc_ty_le N 168], not [ushp_malloc_ty], because     *)
  (* two unbounded ones cannot both be discharged from one 64 KiB chunk     *)
  (* (iris/UkShMalloc.v §7) and 168 is the larger of the two sizes sh's     *)
  (* constructors ask for.  [wp_kshm_child_alloc_redir] below is this       *)
  (* lemma with both of them spent out of [UkShMalloc.ushm_fresh].          *)
  (*                                                                        *)
  (* THE RECEIPT IS NOT DROPPED.  [UkShRedir.wp_kshr_redir_arm] hands its   *)
  (* caller the run back at runcmd's own entry pc with the SUB-TREE, the    *)
  (* ledger the open left and the application's receipt [K ty]; this walk   *)
  (* relays all four to ITS caller rather than spending them on             *)
  (* [wp_kshr_runcmd_final], which would drop [K ty].  That continuation is *)
  (* what the application lane fills with its own EXEC walk.                *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_redir (UM0 UM1 UM2 : iProp Σ)
      (Hm0 : UkShParse.ushp_malloc_ty_le N 168 UM0 UM1)
      (Hm1 : UkShParse.ushp_malloc_ty_le N 168 UM1 UM2)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (ld : list fdstate) (st1 : fdstate) (n : nat)
      (K : fdtype -> iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (⊢ ukn_pay N (-1)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UM0 -∗
    UkShRedir.ush_open_call N cwdv (s0 + Z.of_nat (S (S gp))) 1537
      (<[1%nat := FdClosed]> ld) K -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UM2 -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp Hpx.
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             Hrun Hcont".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    iDestruct (ustr_len with "Hline") as %Hlen31.
    (* ---- 0x9c0  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x9c0) a0_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx))
              (68 + (8 + (UkShDiag.ush_Dg + n)))
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
              (68 + (8 + (UkShDiag.ush_Dg + n)))
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
    (* ---- parsecmd, at the redirect shape ---- *)
    iPoseProof Hpx as "Hpay".
    iAssert (□ (ukn_pay N (-1) -∗ ukn_pay N (-1)))%I as "#Hpxw";
      [ iIntros "!> $" | ].
    iApply (UkShRedirPc.wp_kshp_parsecmd_gt N UM0 UM1 UM2 Hm0 Hm1
              h2 m2 dw dv s0 len f args gp fe
              (8 + (UkShDiag.ush_Dg + n))
              Ha0_2 Hred Htoks Hpos Htlen Hs0 Hs64
              with "Hpcode Hpro Hline Hws Hsy HM Hpxw Hpay Hrun").
    iIntros (p pe) "Hrnode Hnode Hline Hws Hsy".
    iIntros (h3 m3) "%Hcs3 %Ha0_3 HM2 _ Hrun".
    rewrite Hra_2.
    (* ---- 0x9c6  jal ra,runcmd ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x9c6)
              (mword_of_int 2094792 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.runcmd) (mword_of_int 0x9ca)
              (68 + (8 + (UkShDiag.ush_Dg + n)))
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
    (* ---- THE SEAM, at the REDIR node ---- *)
    iMod (ush_cmd_of_ushs_redir h4 m4 (mword_of_int ShSyms.runcmd)
            (68 + (8 + (UkShDiag.ush_Dg + n))) s0 p pe len f args gp fe
            Hred Htoks Hnn0 Hlen31 Hs0 Hs38
            with "Hrun Hrnode Hnode Hline") as "(Hrun & #Htree)".
    (* ---- runcmd's REDIR arm: close(1), open(file), then the sub-tree ---- *)
    replace (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (UkShDiag.ush_Dg + (70 + n)))%nat by lia.
    iApply (UkShRedir.wp_kshr_redir_arm N
              (UExec (ush_args s0 (ushs_nulcut args len f fe) args))
              (ushs_file s0 len f args gp fe) 1537
              h4 m4 p cwdv ld st1 (70 + n) K
              ltac:(unfold Z31; lia) Hpx Ha0_4 Hst1 Hne Hnp
              with "Hdp Hcode Hjt Htree Hstd Hcwd Hopen Hrun").
    iIntros (hf mf q ty) "%Ha0f Hsub Hstd Hcwd HK Hrun".
    iApply ("Hcont" $! hf mf q ty with "[%//] Hsub Hstd Hcwd HK HM2 Hrun").
  Qed.

  (* ===================================================================== *)
  (* §4 THE CHILD AT THE REDIRECT SHAPE, WITH THE ALLOCATOR DISCHARGED.     *)
  (*                                                                       *)
  (* [wp_kshm_child_redir] is stated over TWO abstract capabilities because *)
  (* the redirect line's parse calls [malloc] twice -- [execcmd] and then,  *)
  (* from [parseredirs], [redircmd].  This is it at the CONCRETE one: the   *)
  (* heap /init handed sh's child, [UkShMalloc.ushm_fresh sz] -- [freep]    *)
  (* holding zero, the sixteen bytes of [base], the break where [exec]      *)
  (* left it.                                                              *)
  (*                                                                       *)
  (* WHAT MAKES THE CHAIN CLOSE IS THE BOUND, not a second [morecore].      *)
  (* The first call runs on an EMPTY free list, so it walks [sbrk] and      *)
  (* [free] and leaves the 64 KiB chunk [morecore] inserted minus its own   *)
  (* twelve units: [ushm_one_ge (sz + 65536) 4084].  The second runs on     *)
  (* THAT list, which is non-empty, so it is the short walk with no back    *)
  (* edge ([UkShMalloc.wp_kshm_malloc_one]) and it leaves 4072.  Neither    *)
  (* step is expressible at the unbounded contract, where a call at 65504   *)
  (* takes 4095 of the 4096 units and nothing is left for the next one --   *)
  (* see iris/UkShMalloc.v §7 and iris/UkShParse.v at                       *)
  (* [ushp_malloc_ty_le].                                                   *)
  (*                                                                       *)
  (* THE LEFTOVER IS HANDED ON.  Where [wp_kshm_child_redir]'s continuation *)
  (* has [UM2] this one has [ushm_one_ge (sz + 65536) 4072]: the free list  *)
  (* the child's own [runcmd] arm inherits, so a later lane that needs sh   *)
  (* to allocate again inside the redirect has the capability to hand.      *)
  (* The break is at [sz + 65536] because the allocator asked the kernel    *)
  (* for sixteen pages on the way through, exactly as in                    *)
  (* [UkShMain.wp_kshm_child_alloc].                                        *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_alloc_redir
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (sz : Z) (ld : list fdstate) (st1 : fdstate) (n : nat)
      (K : fdtype -> iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* the break is above [base] (0x2088, the last sixteen bytes of the
       image) and page-aligned, which [exec] leaves it -- the same three
       premises [UkShMain.wp_kshm_child_alloc] carries *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (⊢ ukn_pay N (-1)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UkShMalloc.ushm_fresh N sz -∗
    UkShRedir.ush_open_call N cwdv (s0 + Z.of_nat (S (S gp))) 1537
      (<[1%nat := FdClosed]> ld) K -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UkShMalloc.ushm_one_ge N (sz + 65536) 4072 -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
           Hszlo Hszal Hszok Hpx.
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             Hrun Hcont".
    iApply (wp_kshm_child_redir
              (UkShMalloc.ushm_fresh N sz)
              (UkShMalloc.ushm_one_ge N (sz + 65536) 4084)
              (UkShMalloc.ushm_one_ge N (sz + 65536) 4072)
              (UkShMalloc.ushm_malloc_le_exec N Hpsok_free sz
                 Hszlo Hszal Hszok)
              (UkShMalloc.ushm_malloc_le_next N (sz + 65536))
              h m dw dv s0 cwdv len f args gp fe ld st1 n K
              Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp Hpx
              with "Hdp Hcode Hjt Hpcode Hpro Hline Hws Hsy Hstd Hcwd HM
                    Hopen Hrun Hcont").
  Qed.

End UkShRedirSeam.
