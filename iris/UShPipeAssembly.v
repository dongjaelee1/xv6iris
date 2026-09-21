(* ===================================================================== *)
(*  UShPipeAssembly.v -- THE PIPELINE ROUND'S ASSEMBLY LEAVES             *)
(*  (lane SH-PIPE-ROUND-8; design claude-notes/design/app-pipe.md         *)
(*  SS4.3o-SS4.3q).                                                       *)
(*                                                                       *)
(*  SS4.3q ruled that the round's one remaining hole is a TOKEN in        *)
(*  [UShPipeChild.wp_kshm_child_pipe_paid_line] -- its exit-payment wand  *)
(*  becoming a fancy update.  Measuring the round against the landed      *)
(*  pieces found that ruling wrong in both directions (see the lane's     *)
(*  Findings block and [UShPipeChild]'s S0) and found THREE OTHER holes,  *)
(*  each of which is generic and each of which is closed here:            *)
(*                                                                       *)
(*   S1  [ksh_w1_acc] / [exf_law_fupd]: an exec-failed diagnostic law is  *)
(*       closed under a FANCY UPDATE on the credential it is paid from,   *)
(*       as long as it writes at least one byte.  This is what lets the   *)
(*       [pipe(2)]-failed tail be paid from the two-writer FAMILY: the    *)
(*       family unwinds to the lend ([UShPipeRound2.pipe_round_unwind],   *)
(*       a fupd), and the unwind happens at the diagnostic's FIRST WRITE  *)
(*       -- a WP point -- rather than at the law's pure entry.            *)
(*   S2  [ksh_w1_of_step]: one console byte of ANY step family, through   *)
(*       [UkShDiag.ksh_w1].  [UShPanic.ksh_w1_of_link_blk_at] is this at  *)
(*       the LINK RECORD's own block family; the round's three console    *)
(*       chains ([PipeBoth.pblk2_cstep_L], [pblk2_cstep_R_t] and          *)
(*       [pblk2_fork1_chain]) have the same [out_link] step shape and no  *)
(*       record behind them, so the byte is stated once at an abstract    *)
(*       family here.                                                     *)
(*   S3  the PROTOCOL'S NAMES, ALLOCATED BEFORE [pipe(2)].                *)
(*       [PipeProto.pipe_proto_alloc] mints [pnames] and the invariant    *)
(*       together, inside the [pipe(2)] registrar -- but the round's      *)
(*       family ([PipeBoth.blk2_inv]) has to be allocated BEFORE          *)
(*       [pipe(2)] (it is the lend, and the [pipe(2)]-failed tail is paid *)
(*       from it), and its two exclusion witnesses are PIPE-EXEC-ECHO's   *)
(*       [XL := wcur pn 0] / [YR := pws_lb pn (take 1 L)], which name     *)
(*       [pn].  So the allocation is split in two: the names and the      *)
(*       body's half here, the invariant at the registrar.                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl agree csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import own ghost_map ghost_var invariants.
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
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith.
Require Import ProcGeom.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun.       (* [wp_kshr_jal] -- the exit call's second half *)
Require Import UkShDiag.
Require Import UShOut.
Require Import UShPanic.           (* the mould: [ksh_w1_of_link_blk_at] *)
Require Import LinkRec.            (* the record the generic supplier reads *)
Require Import PipeNames.
Require Import PipeQueue.
Require Import PipeReg.
Require Import PipeProto.
Require Import ObsTrace.
Require Import ConsLog.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOutPure.
Require Import PipeOut.
Require Import PipeBothPure.
Require Import PipeBoth.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeLinkInst.
Require Import UkShFork.
Require Import UkShPipeFork.      (* [pterm_shape] -- the terminal payload *)
Require Import UkShPipe.           (* [ush_pipe_call] *)
Require Import UShPipeCall.        (* [ush_pipe_call_paid]: the paid stub *)
Require Import UEchoPipe.          (* [ep_pay] -- echo's own lend *)
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UShPipeRound2.     (* [blk2N] and the round's two ends *)
Require Import CtxIdDefs.
Require User.ShSyms.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1/S2  THE TWO GENERIC LEAVES                                        *)
(* ===================================================================== *)
Section UShPipeAssemblyGen.
  (* [UShPanic.v]'s [UShPanicGen] binder list, MINUS the link record --
     nothing here reads one -- and minus [echoOutG]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  (* A FANCY UPDATE IN FRONT OF THE TRIVIAL-POST WP ([UConsOpen.
     fupd_wp_triv] restated; that file is not in this one's cone). *)
  Local Lemma fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* =================================================================== *)
  (*  S1  A BYTE'S WRITE IS AN ACCESSOR ON ITS OWN PRECONDITION           *)
  (*                                                                     *)
  (*  [UkShDiag.ksh_w1]'s conclusion is a [mWP], so the resource it is    *)
  (*  paid with may be handed over under a FANCY UPDATE.  This is the     *)
  (*  whole of SS4.3q's problem, moved from the law's pure entry (where   *)
  (*  it cannot be paid) to the first byte (where it can).                *)
  (* =================================================================== *)
  Lemma ksh_w1_acc (N : uk_names Σ) (fdv : mword 64) (b : bv 8)
      (Ci Co : iProp Σ) :
    □ (Ci ={⊤}=∗ ∃ D : iProp Σ, D ∗ ksh_w1 N fdv b D Co) -∗
    ksh_w1 N fdv b Ci Co.
  Proof using .
    iIntros "#Hacc" (ua h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hb HCi] Hrun Hcont".
    iApply fupd_mwp.
    iMod ("Hacc" with "HCi") as (D) "[HD Hw]". iModIntro.
    iApply ("Hw" $! ua h m avail with "[%] [%] [%] Hcode [Hb HD] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ]. iFrame "Hb HD".
  Qed.

  (* ...AND THE LAW, AT A CREDENTIAL THAT ONLY A FUPD REACHES.  [0 < n] is
     what makes it true: the caller's own [Cr] is handed on unchanged as
     [Pf 0], and every later index is the WITNESSED law's, so the end
     ([Pf n -* Cd], a PURE wand) is the witnessed law's own end. *)
  Lemma exf_law_fupd (dg : list (bv 8)) (n : nat) (Cr Cr' Cd : iProp Σ) :
    (0 < n)%nat ->
    □ (Cr ={⊤}=∗ Cr') -∗
    ush_execfail_law_at dg n Cr' Cd -∗
    ush_execfail_law_at dg n Cr Cd.
  Proof using .
    intro Hn. iIntros "#Hup #Hlaw". rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    pose (G := fun p : nat =>
                 (∃ Pf : nat -> iProp Σ,
                    Pf p
                    ∗ □ (∀ (q : nat) (b : bv 8),
                           ⌜ dg !! q = Some b ⌝ -∗
                           ⌜ (q < n)%nat ⌝ -∗
                           ksh_w1 N (mword_of_int 2 : mword 64) b
                             (UserFd.ustd (ukn_fd N) l ∗ Pf q)
                             (UserFd.ustd (ukn_fd N) l ∗ Pf (S q)))
                    ∗ □ (Pf n -∗ Cd))%I).
    iExists (fun p : nat => match p with O => Cr | S q => G (S q) end).
    iSplitL "Hc"; [ iExact "Hc" | ].
    iSplit.
    - iIntros "!>" (p b) "%Hb %Hlt".
      iApply (ksh_w1_acc N (mword_of_int 2 : mword 64) b).
      iIntros "!> [Hl Hp]".
      destruct p as [| q].
      + (* THE FIRST BYTE: the fupd is spent here *)
        iMod ("Hup" with "Hp") as "Hp".
        iDestruct ("Hlaw" $! N l with "[%] Hp")
          as (Pf) "(H0 & #Hs & #He)"; [ exact Hfd | ].
        iModIntro. iExists (UserFd.ustd (ukn_fd N) l ∗ Pf 0%nat)%I.
        iSplitL; [ iFrame "Hl H0" | ].
        iApply (ksh_w1_mono N (mword_of_int 2 : mword 64) b
                  (UserFd.ustd (ukn_fd N) l ∗ Pf 0%nat)%I
                  (UserFd.ustd (ukn_fd N) l ∗ Pf 1%nat)%I
                  with "[] [Hs]").
        { iIntros "!> [$ Hq]". rewrite /G. iExists Pf. by iFrame "Hq Hs He". }
        { iApply ("Hs" $! 0%nat b with "[%] [%]");
            [ exact Hb | exact Hlt ]. }
      + (* EVERY LATER BYTE: the witness is opened and re-packed *)
        rewrite /G. iDestruct "Hp" as (Pf) "(Hq & #Hs & #He)".
        iModIntro. iExists (UserFd.ustd (ukn_fd N) l ∗ Pf (S q))%I.
        iSplitL; [ iFrame "Hl Hq" | ].
        iApply (ksh_w1_mono N (mword_of_int 2 : mword 64) b
                  (UserFd.ustd (ukn_fd N) l ∗ Pf (S q))%I
                  (UserFd.ustd (ukn_fd N) l ∗ Pf (S (S q)))%I
                  with "[] [Hs]").
        { iIntros "!> [$ Hq']". rewrite /G. iExists Pf.
          by iFrame "Hq' Hs He". }
        { iApply ("Hs" $! (S q) b with "[%] [%]");
            [ exact Hb | exact Hlt ]. }
    - destruct n as [| n']; [ lia | ].
      iIntros "!> Hp". rewrite /G. iDestruct "Hp" as (Pf) "(Hn & _ & #He)".
      iApply ("He" with "Hn").
  Qed.

  (* ...AND THE DIAGNOSTIC'S BYTES MAY BE TRUNCATED TO THE BLOCK.  With
     SS4.3r's guard the law only ever asks for a step at [p < n], so a
     supplier that provides the WHOLE alternative ([dg ++ u_prompt], the
     shape every link record delivers) supplies the law at [dg].  This is
     the [dg]-weakening ROUND-8's item 5 names, and items 1/2 spend it
     too: the pipeline round's consumers are stated at the ALTERNATIVE
     ([alt_execfail], [alt_execR], [wl_line dg_pipe]) while the family's
     chains are the blocks. *)
  Lemma exf_law_dg_weaken (dg u : list (bv 8)) (n : nat) (Cr Cd : iProp Σ) :
    (n <= length dg)%nat ->
    ush_execfail_law_at (dg ++ u) n Cr Cd -∗
    ush_execfail_law_at dg n Cr Cd.
  Proof using .
    intro Hn. iIntros "#Hlaw". rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hlaw" $! N l with "[%] Hc") as (Pf) "(H0 & #Hs & #He)";
      [ exact Hfd | ].
    iExists Pf. iFrame "H0 He".
    iIntros "!>" (p b) "%Hb %Hlt".
    iApply ("Hs" $! p b with "[%] [%]"); [ | exact Hlt ].
    rewrite (lookup_app_l dg u p ltac:(lia)). exact Hb.
  Qed.

  (* the mirror, used to read a block byte off its alternative *)
  Lemma exf_lookup_lt (w u : list (bv 8)) (p : nat) (b : bv 8) :
    (p < length w)%nat -> (w ++ u) !! p = Some b -> w !! p = Some b.
  Proof using . intros Hp Hb. by rewrite (lookup_app_l w u p Hp) in Hb. Qed.

  (* =================================================================== *)
  (*  S2  ONE CONSOLE BYTE OF AN ABSTRACT STEP FAMILY                     *)
  (*                                                                     *)
  (*  [UShPanic.ksh_w1_of_link_blk_at]'s proof with the record's block    *)
  (*  family and its step replaced by a parameter: the call does not      *)
  (*  care which family the byte moves, only that the byte HAS a link     *)
  (*  step.  ([UShPanic.ksh_w_of_link_prompt_fam] is the same move one    *)
  (*  call up, for the prompt's two bytes.)                               *)
  (* =================================================================== *)
  Lemma ksh_w1_of_step (N : uk_names Σ) (F : nat -> iProp Σ)
      (l : list fdstate) (rb : bool) (i : nat) (b : bv 8) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    □ (∀ Φ : iProp Σ,
         F i -∗ (F (S i) -∗ Φ) -∗ out_link Uart0 (S gen_id) b Φ) -∗
    ksh_w1 N (mword_of_int 2 : mword 64) b
      (UserFd.ustd (ukn_fd N) l ∗ F i)
      (UserFd.ustd (ukn_fd N) l ∗ F (S i)).
  Proof using .
    intros Hl2.
    iIntros "#Hstep" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hbuf [Hl Hc]] Hrun Hcont".
    subst ua.
    iDestruct (ubyte_split with "Hbuf") as "[Hb1 Hb2]".
    set (ua := m !!! Regidx a1_idx).
    set (Q := (fun k : nat =>
                 ubyteq (ukn_d N) (DfracOwn (1/2)) (uint ua) b
                 ∗ match k with
                   | O => F i
                   | _ => F (S i)
                   end)%I).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = ua)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2; vm_compute; reflexivity).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 2)
      by (rewrite Ham0; vm_compute; reflexivity).
    iApply (wp_ksh_write_chain_buf N h m avail
              (UShOut.ksh_fam N Q) l (DfracOwn (1/2)) 1%nat (fun _ => b)
              with "Hcode Hrun [Hb1 Hc] Hl [Hb2]").
    { iApply (uwrite_chain_sup N Q
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int ShSyms.write : mword 64) 2)
                l 2%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl2).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (DfracOwn (1/2)) ua 1%nat (fun _ => b)
                   with "Hheap [Hb1]") as %HM;
        [ iApply (ubytesq_of_one with "Hb1") | ].
      iFrame "Hheap".
      rewrite Ham1 Hcnt. cbn [cons_out_chain].
      iSplit.
      - rewrite /Q. iFrame "Hb1 Hc".
      - iIntros (b') "%Hb'".
        assert (Hbb : b' = b).
        { pose proof (HM 0%nat ltac:(lia)) as HM0.
          cbn in HM0. rewrite HM0 in Hb'. by injection Hb'. }
        subst b'.
        iApply ("Hstep" $! (Q 1%nat) with "Hc [Hb1]").
        iIntros "Hres". rewrite /Q. iFrame "Hb1". iExact "Hres". }
    { iApply (ubytesq_of_one with "Hb2"). }
    iIntros (h' ret W cw' cs') "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hl Hb2 Hpost Hrun".
    iDestruct (uwrite_no_short Q (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 2%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl2
                 ltac:(rewrite Hka2 Ha2; vm_compute; reflexivity)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    rewrite /Q. iDestruct "HQ" as "[Hb1 Hc]".
    iDestruct (ubytesq_to_one with "Hb2") as "Hb2".
    iDestruct (ubyte_join with "Hb1 Hb2") as "Hbuf".
    iApply ("Hcont" $! h' ret with "[Hbuf Hl Hc] Hrun").
    iFrame "Hbuf Hl". iExact "Hc".
  Qed.

  (* =================================================================== *)
  (*  S2a  ...AND THE SAME AT A MULTI-BYTE CALL                           *)
  (*                                                                     *)
  (*  [UShPanic.prompt_chain] with the prompt taken out: a run of bytes   *)
  (*  written by ONE [write(2, buf, n)] is a [cons_out_chain] over the    *)
  (*  same step family, and cat's console turn                            *)
  (*  ([UCatPipe.pcat_round_at_g]'s [Hw], whose FILE-era discharge is     *)
  (*  [UCatKernel.cat_w_of_link]) is exactly that at the pipeline         *)
  (*  family's RIGHT chain.  This is the half of that discharge which is  *)
  (*  not cat's geometry.                                                 *)
  (* =================================================================== *)
  Definition out_step (bs : list (bv 8)) (F : nat -> iProp Σ) : iProp Σ :=
    (□ (∀ (p : nat) (b : bv 8) (Φ : iProp Σ),
          ⌜ bs !! p = Some b ⌝ -∗
          F p -∗ (F (S p) -∗ Φ) -∗ out_link Uart0 (S gen_id) b Φ))%I.

  Lemma out_chain_of_step (bs : list (bv 8)) (F : nat -> iProp Σ)
      (M : gmap Z (bv 8)) (ua : mword 64) (fb : nat -> bv 8) :
    forall (c i : nat),
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat -> bs !! j = Some (fb j)) ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (fb j)) ->
    out_step bs F -∗ F i -∗ cons_out_chain (S gen_id) M ua F i c.
  Proof using .
    intros c. induction c as [| c IH]; intros i Hline HM.
    - iIntros "_ Hc". cbn [cons_out_chain]. iExact "Hc".
    - iIntros "#Hst Hc". cbn [cons_out_chain]. iSplit.
      + iExact "Hc".
      + iIntros (b) "%Hbm".
        assert (Hbb : b = fb i).
        { rewrite (HM i ltac:(lia) ltac:(lia)) in Hbm. by injection Hbm. }
        subst b.
        iApply ("Hst" $! i (fb i) _ with "[%] Hc").
        { exact (Hline i ltac:(lia) ltac:(lia)). }
        iIntros "Hc".
        iApply (IH (S i) ltac:(intros j H1 H2; apply Hline; lia)
                  ltac:(intros j H1 H2; apply HM; lia) with "Hst Hc").
  Qed.

  (* =================================================================== *)
  (*  S2b  THE RUNCMD CHILD'S OWN EXIT, PAID                              *)
  (*                                                                     *)
  (*  [UkShRun.wp_kshr_exit0] -- the [c.li a0,0; jal ra,<exit>] every     *)
  (*  [runcmd] arm ends at, and where the pipeline round's parent lands   *)
  (*  (0xea, [UkShPipe]'s own parent continuation) -- takes the exit      *)
  (*  payload FREE, as a Prop [(⊢ ukn_pay N (-1))].  A PAID round holds   *)
  (*  it as a RESOURCE (the family closed at the two cursors, i.e.        *)
  (*  [UShPipeRound2.pipe_round_exit]'s [pipe_Wcl_at g I 0]), so the      *)
  (*  landed walk cannot end the round.  This is the same two             *)
  (*  instructions with the payload linear; [UkSh.wp_ksh_exit] already    *)
  (*  takes it that way, so the only thing that was free is the Prop.     *)
  (* =================================================================== *)
  Lemma wp_kshr_exit0_paid (N : uk_names Σ) `{!ukn_const N}
      (h : CpuId) (m : regfile)
      (pc0 pc1 ret : Z) (k : mword 6) (imm : mword 21) (avail : nat) :
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    (mword_of_int ShSyms.exit : mword 64)
      = add_vec (mword_of_int pc1 : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64)
      = add_vec_int (mword_of_int pc1 : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int ShSyms.exit : mword 64) 0) ('b"0")
      = true ->
    shk_code (ukn_t N) -∗
    uinstr_is (ukn_t N) (mword_of_int pc0) true (C_LI (k, Regidx a0_idx)) -∗
    uinstr_is (ukn_t N) (mword_of_int pc1) false (JAL (imm, Regidx ra_idx)) -∗
    ukn_pay N (-1) -∗
    urun N h m (mword_of_int pc0) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros E01 Hsym Hret Hal. iIntros "#Hcode #Hi0 #Hi1 Hpay Hrun".
    iApply (wp_uk_cli N h m (mword_of_int pc0) k a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Hi0 Hrun").
    rewrite E01. iIntros (h1) "Hrun".
    iApply (UkShRun.wp_kshr_jal N h1 _ pc1 ShSyms.exit ret imm avail
              Hsym Hret Hal with "Hi1 Hrun").
    iIntros (h2) "Hrun".
    iApply (UkSh.wp_ksh_exit N h2 _ avail with "Hcode Hpay Hrun").
  Qed.

End UShPipeAssemblyGen.

(* ===================================================================== *)
(*  S2c  THE RECORD'S DIAGNOSTIC LAW AT AN ARBITRARY ALTERNATIVE          *)
(*                                                                       *)
(*  [UShPanic.ush_execfail_law_holds_at] is this at [a := lk_exf L I].    *)
(*  The proof never reads WHICH alternative it is -- only [lk_apr L I a]  *)
(*  (it ends with the prompt, so the block's last index is               *)
(*  [length (lk_ab L I a) - 2]) -- so the alternative is a parameter, and *)
(*  the [panic("pipe")] tail (ROUND-8's item 5) is the same law at        *)
(*  [PipeDisc.PPipe]'s code.                                             *)
(* ===================================================================== *)
Section UShPipeAssemblyLink.
  (* [UShPanic.v]'s [UShPanicGen] binder list VERBATIM. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (L : LinkRec Σ).
  Context `{PS : uprogSG Σ}.

  Lemma ush_execfail_law_holds_alt (I : list (bv 8)) (a : nat) :
    lk_apr L I a ->
    lk_links L -∗
    ush_execfail_law_at (lk_ab L I a) (length (lk_ab L I a) - 2)%nat
      (lk_lcred L (S gen_id) I 3%nat)
      (lk_lcred L (S gen_id) I 0%nat).
  Proof using .
    intro Hapr. iIntros "#Hlk". rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 Hc". destruct Hfd2 as [rb Hl2].
    iDestruct (lk_lcred_blk_open L (S gen_id) I a with "Hc")
      as (v) "[#Hpin Hc]".
    iExists (fun p : nat => lk_blk L (S gen_id) v I a p).
    iSplitL "Hc"; [ iExact "Hc" | ].
    iSplit.
    - (* the guard is DROPPED: the record's block family steps every byte
         of the alternative, the shell's next prompt included *)
      iIntros "!>" (p b) "%Hb %Hlt".
      iApply (UShPanic.ksh_w1_of_link_blk_at L N v I l rb a p b Hl2 Hb
                with "Hpin Hlk").
    - iIntros "!> Hp".
      iApply (lk_lcred_of_post_a L (S gen_id) I a v Hapr with "Hpin").
      rewrite /lk_post. iExact "Hp".
  Qed.

End UShPipeAssemblyLink.

(* ===================================================================== *)
(*  S3  THE PROTOCOL'S NAMES, BEFORE [pipe(2)]                           *)
(* ===================================================================== *)
Section UShPipeAssemblyProto.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{!pipeProtoG Σ}.

  (* THE BODY'S OWN HALF at the initial state, which is what
     [PipeProto.pipe_proto_alloc] puts inside the invariant it allocates.
     Splitting the allocation in two is what lets the round name [pn]
     BEFORE [pipe(2)] -- see the header. *)
  Definition pipe_pre (pn : pnames) : iProp Σ :=
    (pws_auth pn [] ∗ PipeProto.wcur pn 0%nat ∗ PipeProto.rcur pn 0%nat
     ∗ eof_pending pn ∗ ro_pending pn)%I.

  Lemma pipe_names_alloc :
    ⊢ |==> ∃ pn : pnames,
        pipe_pre pn ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn.
  Proof using .
    iIntros "".
    iMod (own_alloc (●ML ([] : list (leibnizO (bv 8))))) as (gh) "Hh";
      [ apply mono_list_auth_valid |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_eofR)) as (ge) "He"; [ done |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_roR)) as (go) "Ho"; [ done |].
    iMod (ghost_var_alloc (0%nat)) as (gw) "Hw".
    iMod (ghost_var_alloc (0%nat)) as (gr) "Hr".
    iMod (own_alloc (Excl ())) as (gl) "Hsl"; [ done |].
    iMod (own_alloc (Excl ())) as (gs) "Hsr"; [ done |].
    iDestruct (ghost_var_split (pn_wcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hw]") as "[Hw1 Hw2]";
      [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split (pn_rcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hr]") as "[Hr1 Hr2]";
      [ by rewrite Qp.half_half | ].
    iModIntro. iExists (MkPNames gh ge go gw gr gl gs).
    rewrite /pipe_pre /wtok /rtok /side_L /side_R /pws_auth /PipeProto.wcur
            /PipeProto.rcur /eof_pending /ro_pending /=.
    by iFrame "Hh Hw1 Hr1 He Ho Hw2 Hr2 Hsl Hsr".
  Qed.

  (* ...AND THE SECOND HALF, at the registrar: the queue's fragment joins
     the names and the invariant is allocated.  [PipeProto.pipe_proto_alloc]
     is this composed with the one above. *)
  Lemma pipe_inv_alloc_at (pn : pnames) (gp : pipe_names)
      (L : list (bv 8)) :
    pipe_pre pn -∗ pipe_qfrag (pn_queue gp) pst0 ={⊤}=∗
    pipe_inv pn gp L ∗ pipe_reg gp.
  Proof using .
    iIntros "(Hh & Hw & Hr & He & Ho) Hfrag".
    iMod (inv_alloc pipeN ⊤ (pipe_body pn gp L)
            with "[Hfrag Hh Hw Hr He Ho]") as "#Hinv".
    { iNext. iExists pst0. rewrite /pst0 /=. iFrame "Hfrag Hh Hw Hr".
      iSplitR; [ iPureIntro; apply prefix_nil | ].
      iSplitR; [ iPureIntro; cbn; lia | ].
      iSplitL "He"; [ by iLeft | by iLeft ]. }
    iModIntro. rewrite /pipe_inv. iFrame "Hinv".
    iApply (pipe_reg_of_inv pn gp L with "Hinv").
  Qed.

End UShPipeAssemblyProto.

(* ===================================================================== *)
(*  S4  THE RUNCMD CHILD'S OWN [fork1] PANIC, AS A DIAGNOSTIC LAW        *)
(*                                                                       *)
(*  The round hands each [fork1] tail [Cx gp] and takes back             *)
(*  [ukn_pay N (-1)] through [Bx gp] ([UShPipeChild.                     *)
(*  wp_kshm_child_pipe_paid_line]'s last two premises).  At the pipeline *)
(*  era the payload is [UkShPipeFork.pterm_pay I], whose SECOND ARM is   *)
(*  the terminal shape at cursor 5 -- so this law IS design SS4.3h's      *)
(*  terminal round, in the shape the walk consumes:                      *)
(*                                                                       *)
(*    [Cx gp] := the family's right and mode halves, both at 0           *)
(*    [Bx gp] := [UkShPipeFork.pterm_shape g I 5]                        *)
(*                                                                       *)
(*  It needs TWO of this file's leaves and nothing else: the mode's fire *)
(*  to 3 ([PipeBoth.blk2_mode_fire]) is a FANCY UPDATE and is spent at   *)
(*  the first byte through [exf_law_fupd]; each of `fork\n''s five bytes *)
(*  is [PipeBoth.pblk2_cstep_R_t] through [ksh_w1_of_step].              *)
(* ===================================================================== *)
Section UShPipeAssemblyFork.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = pecl g).
  Context `{PS : uprogSG Σ}.

  Local Notation PT := (echo_taint γ).

  (* the five bytes of `fork\n' are [alt_forkc]'s first five *)
  Local Lemma fork_panic_byte (p : nat) (b : bv 8) :
    alt_panic !! p = Some b -> alt_forkc !! p = Some b.
  Proof using .
    intro Hb. rewrite alt_forkc_panic. by apply lookup_app_l_Some.
  Qed.

  (* THE LAW.  Everything persistent the family's byte step asks for is a
     premise here, so what the round lends the two [fork1] tails is the
     two ghost halves and nothing else. *)
  Lemma pipe_fork_panic_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (gL gR gM : gname) (XL YR : iProp Σ) :
    Timeless XL -> Timeless YR ->
    pline_at I = LPipe ws ->
    pipe_link_taint g -∗
    era_pin γ (S gen_id) v -∗
    inp_lb v I -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    ush_execfail_law_at alt_panic 5%nat
      (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)
      (UkShPipeFork.pterm_shape g I 5%nat).
  Proof using Hcons.
    intros HTX HTY Hline.
    iIntros "#Ht #Hpin #Hlb #Hinv".
    assert (Hbl : pboth_line I) by (exists ws; exact Hline).
    assert (Hwitt : forall sel : list bool,
               sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel)
      by (intros sel Hs; exact (pblk2_wit_t_forkc I ws sel Hline Hs)).
    (* ---- (1) THE MODE FIRES AT THE FIRST BYTE, under [exf_law_fupd] ---- *)
    iApply (exf_law_fupd alt_panic 5%nat
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)%I
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 3%nat)%I
              (UkShPipeFork.pterm_shape g I 5%nat) ltac:(lia) with "[] []").
    { iIntros "!> [HcR HcM]".
      iMod (blk2_mode_fire g ⊤ blk2N (S gen_id) v I L gL gR gM XL YR 3%nat
              HTX HTY ltac:(apply top_subseteq) ltac:(by right; right)
              with "Hinv HcM HcR []") as "[HcM HcR]".
      { iIntros "%Hq". discriminate Hq. }
      iModIntro. iFrame "HcR HcM". }
    (* ---- (2) THE FIVE BYTES, each [pblk2_cstep_R_t] ---- *)
    rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 Hc". destruct Hfd2 as [rb Hl2].
    iExists (fun p : nat =>
               (PipeBoth.wcur gR (1/2) p ∗ PipeBoth.wcur gM (1/2) 3%nat
                ∗ (match p with
                   | O => True
                   | _ => cs_frozen_at v (nlines I - 1)%nat ∨ PT
                   end))%I)%I.
    iSplitL "Hc"; [ by iDestruct "Hc" as "[$ $]" | ].
    iSplit.
    - iIntros "!>" (p b) "%Hb %Hlt".
      (* THE FAMILY IS NAMED AND NOT SEARCHED: with [_] here the elaborator
         has to solve [?F p =?= ...] and [?F (S p) =?= ...] together and
         does not come back (measured: >10 min, then [Set Default Timeout]
         cut it). *)
      iApply (ksh_w1_of_step N
                (fun q : nat =>
                   (PipeBoth.wcur gR (1/2) q ∗ PipeBoth.wcur gM (1/2) 3%nat
                    ∗ (match q with
                       | O => True
                       | _ => cs_frozen_at v (nlines I - 1)%nat ∨ PT
                       end))%I)
                l rb p b Hl2).
      iIntros "!>" (Φ) "Hf HΦ".
      iDestruct "Hf" as "(HcR & HcM & _)".
      iApply (pblk2_cstep_R_t g Hcons blk2N (S gen_id) v I L gL gR gM XL YR
                p b Φ HTX HTY blk2N_uart (fork_panic_byte p b Hb) Hwitt
                with "[] Ht Hpin Hinv HcR HcM").
      { iApply pblk2_ecl_R_t_holds. }
      iIntros "HcR HcM #Hfz". iApply "HΦ". iFrame "HcR HcM". iExact "Hfz".
    - iIntros "!> (HcR & HcM & #Hfz)".
      rewrite /UkShPipeFork.pterm_shape.
      iExists v, L, gL, gR, gM, XL, YR.
      iSplitR; [ iPureIntro; split_and!; assumption | ].
      iFrame "Hpin Hlb". rewrite /pwc_fork_exit.
      by iFrame "Hinv HcR HcM Hfz".
  Qed.

End UShPipeAssemblyFork.

(* ===================================================================== *)
(*  S5  THE ROUND'S THREE DIAGNOSTIC LAWS                                *)
(*  (ROUND-8's bill, items 1, 2 and 5; design SS4.3r.)                    *)
(*                                                                       *)
(*  Each is [UkShDiag.ush_execfail_law_at] at ONE of the round's three    *)
(*  console chains, and each is the same three moves:                    *)
(*                                                                       *)
(*    (a) the ALTERNATIVE the consumer names is the BLOCK plus the        *)
(*        shell's prompt, and the prompt is the PARENT's to write -- so   *)
(*        the law is built at the block and weakened to the alternative   *)
(*        by [exf_law_dg_weaken], which is exactly what SS4.3r's [p < n]   *)
(*        guard makes possible;                                          *)
(*    (b) a MODE FIRE, where there is one, is a fancy update and is spent *)
(*        at the first byte through [exf_law_fupd];                      *)
(*    (c) each byte is one of [PipeBoth]'s family steps through           *)
(*        [ksh_w1_of_step], with the family WRITTEN OUT (ROUND-8's        *)
(*        operational note: an unnamed one does not return).             *)
(* ===================================================================== *)
(* [EchoDisc.alt_execfail] IS the left block plus the shell's prompt *)
Lemma alt_execfail_app : EchoDisc.alt_execfail = dg_execL ++ u_prompt.
Proof using. exact (eq_sym alt_execL_echo). Qed.

(* ===================================================================== *)
(*  ITEM 6 STOPS AT THE ARM'S SPLIT, AND THIS IS THE ARITHMETIC           *)
(*  (lane SH-PIPE-ROUND-9; ROUND-8's bill item 6.)                        *)
(*                                                                       *)
(*  [UkShPipe.wp_kshr_pipe_arm_g] splits the runcmd child's lend ONCE,    *)
(*  before either [fork1], into [RcL gp * (RcR gp * (Rk gp * Cx gp))],    *)
(*  and pays BOTH [panic("fork")] tails from [Cx gp] alone.  The family's *)
(*  RIGHT CHAIN is what writes `fork\n' ([PipeBoth.rsrc L 3 = alt_forkc], *)
(*  mode 3) and it is also what writes CAT'S OUTPUT ([rsrc L 1 = L], mode *)
(*  1) -- by design, since the two are alternatives.  The resource that   *)
(*  says <<I am the right-chain writer>> is [wcur gR (1/2) * wcur gM      *)
(*  (1/2)], and there is exactly ONE of it (the other half of each is in  *)
(*  [blk2_inv]).  So the split must give it to [RcR gp] (or cat cannot    *)
(*  print) AND to [Cx gp] (or a fork panic cannot print), and it cannot   *)
(*  do both.  The left chain is no escape: it is hard-wired to            *)
(*  [dg_execL], whose first byte is not the panic's.                      *)
(*                                                                       *)
(*  THE RESOURCES ARE IN HAND AT BOTH PANICS and are DROPPED, exactly as  *)
(*  in SS4.3s and SS4.3t: [wp_kshr_pipe_arm_g]'s SECOND fork-panic        *)
(*  continuation already passes the fork answer, whose [r = -1] arm       *)
(*  carries [RcR gp] (the walk's own statement, and [r = -1] is one of    *)
(*  its pure premises, so the other disjunct is refutable); its FIRST     *)
(*  fork-panic continuation passes [RcL gp] and holds [RcR gp] unspent.   *)
(*  [UkShPipePaid.wp_kshr_pipe_arm_paid] is what drops them, when it      *)
(*  collapses the two continuations to one law at [Cx gp].                *)
(* ===================================================================== *)
Lemma pipe_right_chain_is_shared (L : list (bv 8)) :
  PipeBoth.rsrc L 1%nat = L /\ PipeBoth.rsrc L 3%nat = alt_forkc.
Proof using. split; reflexivity. Qed.

Lemma pipe_fork_byte_not_left :
  alt_forkc !! 0%nat = alt_panic !! 0%nat
  /\ dg_execL !! 0%nat <> alt_panic !! 0%nat.
Proof using.
  split; [ vm_compute; reflexivity | vm_compute; discriminate ].
Qed.

(* the padded selector's length, at a VARIABLE bound (see the note on
   [PipeBoth.length_pad]: a [wl_line] in the goal is split by
   [rewrite length_app] and [lia] then sees two atoms for one number) *)
Lemma pad_false_len (sel : list bool) (n : nat) :
  (length sel <= n)%nat ->
  length (sel ++ replicate (n - length sel) false) = n.
Proof using. intro H. rewrite length_app length_replicate. lia. Qed.

Section UShPipeAssemblyDiag.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = pecl g).
  Context `{PS : uprogSG Σ}.

  Local Notation PT := (echo_taint γ).

  (* ---- the PRan witness at EVERY short selector: pad with the right
          side's remaining bytes, exactly as [pblk2_wit_both] pads.  The
          padded length is stated at a VARIABLE [n] ([PipeBoth.length_pad]'s
          own note: with a [wl_line] in the goal, [rewrite length_app]
          walks into it and [lia] then has two atoms for one number). ---- *)
  Lemma pblk2_wit_ran_at (I : list (bv 8)) (ws : list (list (bv 8)))
      (sel : list bool) :
    pline_at I = LPipe ws ->
    count_true sel = 0%nat ->
    (length sel <= length (wl_line (drop 1 ws)))%nat ->
    pblk2_wit I (wl_line (drop 1 ws)) sel.
  Proof using .
    intros Hl Hc Hlen.
    pose (sel' := sel ++ replicate (length (wl_line (drop 1 ws))
                                    - length sel) false).
    assert (Hc' : count_true sel' = 0%nat).
    { rewrite /sel' count_true_app count_true_replicate_false. lia. }
    assert (Hlen' : length sel' = length (wl_line (drop 1 ws)))
      by exact (pad_false_len sel (length (wl_line (drop 1 ws))) Hlen).
    apply (pblk2_wit_mono I (wl_line (drop 1 ws)) sel sel').
    - rewrite /sel'. by eexists.
    - rewrite /sel_wf2 Hc' Hlen'. split; lia.
    - exact (pblk2_wit_of_code I (wl_line (drop 1 ws)) sel'
               (palt_code PRan)
               (pblk2_code_ran I ws sel' Hl Hc' Hlen')).
  Qed.

  (* =================================================================== *)
  (*  ITEM 1  THE LEFT CHILD'S DIAGNOSTIC, at the family's LEFT chain     *)
  (*                                                                     *)
  (*  echo's exec failed, so the child still holds its whole lend and the *)
  (*  write permit at ZERO is inside it -- that permit IS [XL], the left  *)
  (*  side's exclusion witness, and it is spent into the family at the    *)
  (*  FIRST byte ([pblk2_cstep_L]'s [(c1 = 0) -* XL]).  Seventeen bytes   *)
  (*  later the left cursor is at [length dg_execL] and that, and not     *)
  (*  [PipeProto.pipe_payL], is what the round reads [PExecL] off         *)
  (*  ([UShPipeRound2.pround_case]'s second disjunct).                    *)
  (* =================================================================== *)
  Lemma pipe_execL_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (gL gR gM : gname) (XL YR : iProp Σ) :
    Timeless XL -> Timeless YR ->
    pline_at I = LPipe ws ->
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    pipe_link_taint g -∗
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    ush_execfail_law_at EchoDisc.alt_execfail 17%nat
      (PipeBoth.wcur gL (1/2) 0%nat ∗ XL)
      (PipeBoth.wcur gL (1/2) 17%nat).
  Proof using Hcons.
    intros HTX HTY Hline.
    iIntros "#Hex #Ht #Hpin #Hinv".
    assert (Hwit : forall sel : list bool,
               sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel)
      by (intros sel Hs; exact (pblk2_wit_both I ws sel Hline Hs)).
    assert (Hwitt : forall sel : list bool,
               sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel)
      by (intros sel Hs; exact (pblk2_wit_t_forkc I ws sel Hline Hs)).
    rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 Hc". destruct Hfd2 as [rb Hl2].
    iExists (fun p : nat =>
               (PipeBoth.wcur gL (1/2) p
                ∗ (match p with O => XL | _ => True end))%I).
    iSplitL "Hc"; [ by iDestruct "Hc" as "[$ $]" | ].
    iSplit.
    - iIntros "!>" (p b) "%Hb %Hlt".
      (* THE GUARD IS WHAT MAKES THIS PROVABLE (design SS4.3r).  The
         alternative is the block plus the shell's PROMPT -- nineteen
         bytes -- and at a pipeline round the prompt is the PARENT's to
         write ([pwc_line2]'s third arm), so only the block's seventeen
         are steps of this chain. *)
      assert (Hb' : dg_execL !! p = Some b).
      { apply (exf_lookup_lt dg_execL u_prompt p b
                 ltac:(rewrite dg_execL_len; lia)).
        rewrite -alt_execfail_app. exact Hb. }
      (* THE FAMILY IS NAMED AND NOT SEARCHED (ROUND-8's operational note) *)
      iApply (ksh_w1_of_step N
                (fun q : nat =>
                   (PipeBoth.wcur gL (1/2) q
                    ∗ (match q with O => XL | _ => True end))%I)
                l rb p b Hl2).
      iIntros "!>" (Φ) "Hf HΦ".
      iDestruct "Hf" as "[HcL HX]".
      iApply (pblk2_cstep_L g Hcons blk2N (↑pipeN) (S gen_id) v I L
                gL gR gM XL YR p b Φ HTX HTY blk2N_uart blk2N_pipeN
                Hb' Hwit Hwitt
                with "Hex [] [] Ht Hpin Hinv HcL [HX]").
      { iApply pblk2_ecl_L_holds. }
      { iApply pblk2_ecl_L_t_holds. }
      { destruct p as [| q]; [ iIntros "_"; iExact "HX" | ].
        iIntros "%Hq". discriminate Hq. }
      (* [iFrame] closes the [True] the family's later indices carry *)
      iIntros "HcL". iApply "HΦ". iFrame "HcL".
    - iIntros "!> [$ _]".
  Qed.

  (* =================================================================== *)
  (*  ITEM 2  THE RIGHT CHILD'S DIAGNOSTIC, at MODE 2                     *)
  (*                                                                     *)
  (*  cat's exec failed.  The right child fires the mode to 2 -- a fancy  *)
  (*  update, spent at the first byte through [exf_law_fupd] -- which     *)
  (*  fixes the family's right source at [dg_execR] and deposits nothing  *)
  (*  (the [YR] arm is mode 1's).                                        *)
  (* =================================================================== *)
  Lemma pipe_execR_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (gL gR gM : gname) (XL YR : iProp Σ) :
    Timeless XL -> Timeless YR ->
    pline_at I = LPipe ws ->
    L = wl_line (drop 1 ws) ->
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    pipe_link_taint g -∗
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    ush_execfail_law_at PipeDisc.alt_execR 16%nat
      (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)
      (PipeBoth.wcur gR (1/2) 16%nat ∗ PipeBoth.wcur gM (1/2) 2%nat).
  Proof using Hcons.
    intros HTX HTY Hline HL.
    iIntros "#Hex #Ht #Hpin #Hinv".
    assert (Hwit2 : forall sel : list bool,
               sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel)
      by (intros sel Hs; exact (pblk2_wit_both I ws sel Hline Hs)).
    assert (Hwit1 : forall sel : list bool,
               count_true sel = 0%nat -> (length sel <= length L)%nat ->
               pblk2_wit I L sel).
    { rewrite HL. intros sel Hc Hlen.
      exact (pblk2_wit_ran_at I ws sel Hline Hc Hlen). }
    (* ---- (1) THE MODE FIRES AT THE FIRST BYTE ---- *)
    iApply (exf_law_fupd PipeDisc.alt_execR 16%nat
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)%I
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 2%nat)%I
              (PipeBoth.wcur gR (1/2) 16%nat ∗ PipeBoth.wcur gM (1/2) 2%nat)%I
              ltac:(lia) with "[] []").
    { iIntros "!> [HcR HcM]".
      iMod (blk2_mode_fire g ⊤ blk2N (S gen_id) v I L gL gR gM XL YR 2%nat
              HTX HTY ltac:(apply top_subseteq) ltac:(by right; left)
              with "Hinv HcM HcR []") as "[HcM HcR]".
      { iIntros "%Hq". discriminate Hq. }
      iModIntro. iFrame "HcR HcM". }
    (* ---- (2) THE SIXTEEN BYTES, each [pblk2_cstep_R] at mode 2 ---- *)
    rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 Hc". destruct Hfd2 as [rb Hl2].
    iExists (fun p : nat =>
               (PipeBoth.wcur gR (1/2) p ∗ PipeBoth.wcur gM (1/2) 2%nat)%I).
    iSplitL "Hc"; [ by iDestruct "Hc" as "[$ $]" | ].
    iSplit.
    - iIntros "!>" (p b) "%Hb %Hlt".
      (* as in item 1: the sixteen block bytes, not the alternative's
         eighteen -- SS4.3r's guard *)
      assert (Hb' : dg_execR !! p = Some b).
      { apply (exf_lookup_lt dg_execR u_prompt p b
                 ltac:(rewrite dg_execR_len; lia)). exact Hb. }
      iApply (ksh_w1_of_step N
                (fun q : nat =>
                   (PipeBoth.wcur gR (1/2) q
                    ∗ PipeBoth.wcur gM (1/2) 2%nat)%I)
                l rb p b Hl2).
      iIntros "!>" (Φ) "Hf HΦ".
      iDestruct "Hf" as "[HcR HcM]".
      iApply (pblk2_cstep_R g Hcons blk2N (↑pipeN) (S gen_id) v I L
                gL gR gM XL YR 2%nat p b Φ HTX HTY blk2N_uart blk2N_pipeN
                ltac:(by right) ltac:(cbn [rsrc]; exact Hb')
                ltac:(cbn [rsrc]; exact dg_execR_nodollar) Hwit2 Hwit1
                with "Hex [] Ht Hpin Hinv HcR HcM").
      { iApply pblk2_ecl_R_holds. }
      iIntros "HcR HcM". iApply "HΦ". iFrame "HcR HcM".
    - by iIntros "!> $".
  Qed.

  (* =================================================================== *)
  (*  ITEM 5  THE [panic("pipe")] LAW, AT THE ERA'S CREDENTIAL             *)
  (*                                                                     *)
  (*  [pipe(2)] itself failed: NO child exists, nothing has been written, *)
  (*  and the family is still the round's LEND at both cursors -- so it   *)
  (*  unwinds ([UShPipeRound2.pipe_round_unwind], a fancy update, spent   *)
  (*  at the first byte) and what writes the five bytes is the LINK       *)
  (*  RECORD, at [PipeDisc.PPipe]'s alternative.                          *)
  (* =================================================================== *)
  Lemma pipe_panic_pipe_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (gL gR gM : gname) (XL YR : iProp Σ) :
    Timeless XL -> Timeless YR ->
    pline_at I = LPipe ws ->
    PipeLinks.pipe_links g -∗
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat
      (PipeBoth.wcur gL (1/2) 0%nat ∗ PipeBoth.wcur gR (1/2) 0%nat)
      (pipe_Wcl_at g I 0%nat).
  Proof using .
    intros HTX HTY Hline. iIntros "#Hlk #Hpin #Hinv".
    (* the record's own law at [PPipe] -- [alt_pipe = wl_line dg_pipe ++
       u_prompt], so the block's last index is 5 *)
    assert (Hgd : pab_gd I (palt_code PPipe)).
    { rewrite /pab_gd (palt_of_code PPipe) Hline. by split. }
    assert (Hapr : papr I (palt_code PPipe)).
    { rewrite /papr (palt_of_code PPipe) Hline. by split_and!. }
    iPoseProof (ush_execfail_law_holds_alt (pipe_link_inst_at g)
                  (PS := PS) I (palt_code PPipe) Hapr with "[]") as "#Hx";
      [ cbn [lk_links pipe_link_inst_at]; iExact "Hlk" | ].
    rewrite (pipe_inst_ab g) (pab_is I (palt_code PPipe) Hgd)
            (palt_of_code PPipe) Hline /pcont /alt_pipe.
    assert (Hl5 : (length (wl_line PipeDisc.dg_pipe ++ u_prompt) - 2)%nat
                  = 5%nat) by (vm_compute; reflexivity).
    rewrite Hl5.
    iPoseProof (exf_law_dg_weaken (wl_line PipeDisc.dg_pipe) u_prompt 5%nat
                  _ _ ltac:(vm_compute; lia) with "Hx") as "#Hy".
    (* ...and the credential it is paid from is the round's own lend *)
    iApply (exf_law_fupd (wl_line PipeDisc.dg_pipe) 5%nat
              (PipeBoth.wcur gL (1/2) 0%nat ∗ PipeBoth.wcur gR (1/2) 0%nat)%I
              (pipe_Wcl_at g I 3%nat) (pipe_Wcl_at g I 0%nat)
              ltac:(lia) with "[] [Hy]"); [ | iExact "Hy" ].
    iIntros "!> [HcL HcR]".
    iApply (pipe_round_unwind g ⊤ I L gL gR gM XL YR v HTX HTY
              ltac:(apply top_subseteq) with "Hpin Hinv HcL HcR").
  Qed.

  (* =================================================================== *)
  (*  THE EXIT'S ONE MISSING READING (bill item 6; STOP rule 2 of the     *)
  (*  brief, answered).  [UShPipeRound2.pround_case] has FOUR arms and    *)
  (*  the two children's exit payloads offer five combinations: the       *)
  (*  fifth -- the LEFT child's exec failed ([c1 = length dg_execL]) and  *)
  (*  cat RAN ([mode 1], [R = L], [c2] arbitrary) -- is not one of them,  *)
  (*  and it is the one the round has to refute.  It refutes ITSELF, out  *)
  (*  of the children's own exclusion: a left cursor past zero means the  *)
  (*  family is holding [XL] (the write permit at zero, which the left    *)
  (*  diagnostic's first byte deposited), and mode 1 means it is holding  *)
  (*  [YR] (the reader got a byte) -- and those two are what               *)
  (*  [PipeProto.pipe_excl_wtok_lb] says cannot coexist.                  *)
  (* =================================================================== *)
  Lemma blk2_no_L_at_mode1 (v : era_pins) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ) (c1 : nat) :
    Timeless XL -> Timeless YR ->
    (0 < c1)%nat ->
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    PipeBoth.wcur gL (1/2) c1 -∗ PipeBoth.wcur gM (1/2) 1%nat ={⊤}=∗ False.
  Proof using .
    intros HTX HTY Hc1. iIntros "#Hex #Hinv HcL HcM".
    iMod (inv_acc ⊤ blk2N _ ltac:(apply top_subseteq) with "Hinv")
      as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_L gL gR c1 with "HcL Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1' c2 tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iDestruct (wcur_agree with "HcL HgL") as %<-.
    iDestruct "Hxl" as "[%Hz | HXL]"; [ exfalso; lia | ].
    rewrite {1}/rmode. iDestruct "Hrm" as (n) "(HgM & %Htmb & Harm)".
    iDestruct (wcur_agree with "HcM HgM") as %<-.
    iDestruct "Harm" as "[%Ha | [[%Ha HYR] | [%Ha | %Ha]]]";
      [ destruct Ha as [Ha _]; discriminate Ha
      | | destruct Ha as [Ha _]; discriminate Ha
      | destruct Ha as [Ha _]; discriminate Ha ].
    iMod (fupd_mask_subseteq (↑pipeN : coPset)) as "_";
      [ etrans; [ exact blk2N_pipeN | set_solver ] | ].
    iMod ("Hex" with "HXL HYR") as %[].
  Qed.

End UShPipeAssemblyDiag.

(* ===================================================================== *)
(*  S6  ITEM 4  THE [pipe(2)] REGISTRAR AT A *PRE-ALLOCATED* [pn]        *)
(*                                                                       *)
(*  [UShEchoPipePay.ep_registrar_of_wq] mints the protocol's names        *)
(*  INSIDE the registrar ([PipeProto.pipe_proto_alloc]).  A round cannot: *)
(*  [PipeBoth.blk2_inv]'s two exclusion witnesses are PIPE-EXEC-ECHO's    *)
(*  [XL := PipeProto.wcur pn 0] and [YR := pws_lb pn (take 1 L)], both of *)
(*  which NAME [pn], while the family has to exist before [pipe(2)] (it   *)
(*  IS the lend, and the [pipe(2)]-failed tail is paid from it -- S5's    *)
(*  [pipe_panic_pipe_law]).  S3's split is what makes this statable, and  *)
(*  this is its second half read as [UkShPipe.ush_pipe_call]'s            *)
(*  registration parameter.  [Wq] is [emp] here, as design SS4.3r's item 4 *)
(*  says: the era's console credential is NOT in echo's lend at a         *)
(*  pipeline round -- the round's own left cursor half is, and            *)
(*  [UShPipeRound2.ep_pay_frame] is what joins them afterwards.           *)
(* ===================================================================== *)
Section UShPipeAssemblyReg.
  (* [UShPipeCall.v]'s binder list VERBATIM (it applies that file's leaf,
     so every class must resolve exactly as it resolved there), plus
     [pipeProtoG] for the protocol's own ghosts. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!pipeProtoG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  (* what the registrar answers, at the round's own [pn] *)
  Definition pipe_reg_pay (pn : pnames) (Wq : iProp Σ) (L : list (bv 8))
      (gp : pipe_names) : iProp Σ :=
    (rtok pn ∗ side_R pn ∗ UEchoPipe.ep_pay Wq pn gp L)%I.

  Lemma pipe_registrar_at (pn : pnames) (Wq : iProp Σ) (L : list (bv 8)) :
    pipe_pre pn -∗ wtok pn -∗ side_L pn -∗ rtok pn -∗ side_R pn -∗ Wq -∗
    ∀ gp : pipe_names,
      pipe_qfrag (pn_queue gp) pst0 ={⊤}=∗
      pipe_reg gp ∗ pipe_reg_pay pn Wq L gp.
  Proof using .
    iIntros "Hpre Hw Hsl Hr HR HWq" (gp) "Hfrag".
    iMod (pipe_inv_alloc_at pn gp L with "Hpre Hfrag") as "[#Hinv Hreg]".
    rewrite /wtok.
    iMod (pws_lb_of_inv pn gp L 0%nat with "Hinv Hw") as "[Hw #Hlb]".
    iModIntro. iFrame "Hreg Hr HR".
    rewrite /UEchoPipe.ep_pay /UEchoPipe.ep_frame.
    iFrame "Hinv Hsl HWq Hw". rewrite take_0. iExact "Hlb".
  Qed.

  Lemma ush_pipe_call_pipe_pay (N : uk_names Σ) `{!ukn_const N}
      (pn : pnames) (Wq : iProp Σ) (l : list fdstate) (L : list (bv 8)) :
    fd_lowest_closed l = None ->
    pipe_pre pn -∗ wtok pn -∗ side_L pn -∗ rtok pn -∗ side_R pn -∗ Wq -∗
    udepw_law (PS := PS) 21 -∗
    UkShPipe.ush_pipe_call (SG := uexecSG_xv6) (PS := PS) N l
      (pipe_reg_pay pn Wq L).
  Proof using Hpsok_free.
    intro Hnone.
    iIntros "Hpre Hw Hsl Hr HR HWq Hcl".
    iApply (UShPipeCall.ush_pipe_call_paid (PS := PS) Hpsok_free N l
              (pipe_reg_pay pn Wq L) Hnone with "[Hpre Hw Hsl Hr HR HWq] Hcl").
    iApply (pipe_registrar_at pn Wq L with "Hpre Hw Hsl Hr HR HWq").
  Qed.

End UShPipeAssemblyReg.

(* ===================================================================== *)
(*  S7  ITEM 3 IS BLOCKED AT A PREMISE, AND HERE IS THE WITNESS          *)
(*  (lane SH-PIPE-ROUND-9; design SS4.3r's item 3.)                       *)
(*                                                                       *)
(*  ROUND-8 priced item 3 as the copy of [UCatKernel.cat_w_of_link] at    *)
(*  [Ch c := wcur gR (1/2) c * wcur gM (1/2) 1] over [out_chain_of_step]. *)
(*  The copy is mechanical; what is NOT available is the premise it must  *)
(*  be copied at.  [UCatPipe.pcat_round_at_g] is generic in the cursor    *)
(*  family [Ch], and hands its [Hw] the pure fact                          *)
(*                                                                       *)
(*    forall j < cnt, pcont (pcat_line I0) (palt_of pcat_alt)             *)
(*                      !! (c + j) = Some (fbb j)                        *)
(*                                                                       *)
(*  -- a lookup into the ALTERNATIVE, which is [L ++ u_prompt].  The       *)
(*  two-writer family's right chain at mode 1 steps [PipeBoth.rsrc L 1 =  *)
(*  L] and nothing else ([pblk2_cstep_R]'s [rsrc L n !! c2 = Some b]),    *)
(*  and it also demands [Forall nodollar (rsrc L n)].  The three          *)
(*  conjuncts below are the gap: AT [c + j = length L] THE PREMISE IS     *)
(*  SATISFIED AND THE STEP IS UNAVAILABLE, and the byte in question is    *)
(*  the prompt's '$', which the chain's own [nodollar] premise excludes.  *)
(*                                                                       *)
(*  NO CHOICE OF [Ch] REPAIRS IT.  What rules that index out is           *)
(*  [c + cnt <= length L], and that is the READER's fact: it comes from   *)
(*  [PipeProto.pipe_rQ]'s [acc = take (length acc) (drop c L)].           *)
(*  [pcat_round_at_g] HAS it -- its content arm derives                   *)
(*  [L !! (c + j) = Some (gb j)] ([UCatPipe.pcat_acc_line]) and then       *)
(*  WEAKENS it with [UCatPipe.pcat_round_line] before calling [Hw] --      *)
(*  and it keeps the reader's permit in [pcat_hold], which [Hw] never      *)
(*  sees.  So the fact is unreachable from [Ch], whatever [Ch] is.        *)
(*                                                                       *)
(*  THE REPAIR IS ONE LINE, in a file this lane does not own: state       *)
(*  [pcat_round_at_g]'s [Hw] premise at [L] ([pcat_out I0] is already a    *)
(*  parameter of that lemma) instead of at [pcont ... (palt_of            *)
(*  pcat_alt)]; the content arm passes [Hbytes] straight through and the  *)
(*  landed instance [UCatPipe.pcat_round_at] weakens it back with         *)
(*  [pcat_round_line], so NO STATEMENT outside [pcat_round_at_g]'s own    *)
(*  premise moves.  It is SS4.3r's [p < n] guard once more, one file over. *)
(* ===================================================================== *)
Lemma pcat_hw_gap (l : pline) :
  pcont l PRan !! length (wl_line (drop 1 (pline_ws l)))
    = Some (u_prompt !!! 0%nat)
  /\ wl_line (drop 1 (pline_ws l))
       !! length (wl_line (drop 1 (pline_ws l))) = None
  /\ ~ nodollar (u_prompt !!! 0%nat).
Proof using.
  split_and!.
  - cbn [pcont].
    rewrite (lookup_app_r (wl_line (drop 1 (pline_ws l))) u_prompt
               (length (wl_line (drop 1 (pline_ws l)))) ltac:(lia)).
    rewrite Nat.sub_diag. by vm_compute.
  - apply lookup_ge_None_2. lia.
  - intro Hq. apply Hq. by vm_compute.
Qed.
