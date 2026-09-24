(* ===================================================================== *)
(* UkPipeConsOut.v -- THE PIPELINE'S CONSOLE as an output device of the   *)
(* endpoint interface (program-specs SS3.4d).                             *)
(*                                                                        *)
(* The pipeline's claim is [pecl = gcl ∨ popen]: the generic claim        *)
(* between rounds and at every single-writer round, [popen] while a       *)
(* two-writer round is open.  [UkConsOut.cons_write] is claim-free (its   *)
(* device is abstract: three laws), so this file is two instances of it:  *)
(*                                                                        *)
(*   S1  the SINGLE-WRITER rounds: [UkConsOut.cons_dev] at the pipeline's *)
(*       link parameters ([PipeLinksLine.pipe_params]) and its links      *)
(*       bundle ([PipeLinks.pipe_links], which entails [glinks]);          *)
(*   S2  the RIGHT WRITER OF A TWO-WRITER ROUND ([popen]): the device      *)
(*       [pcons_dev [drop c L]] is cat's cursor half of the two-writer     *)
(*       family ([UShPipeCatRound.pcat_ch] at [c]) beside the round's      *)
(*       persistent context -- the era's pin, the link taint, the family's *)
(*       invariant ([PipeBoth.blk2_inv]), the exclusion between the left   *)
(*       writer's fact and the reader's, and the READER'S FACT [YR] itself *)
(*       -- and one byte is [UShPipeCatRound.pcat_step_at].  The           *)
(*       alternative is the writer's OWN source (the line [L]), never the  *)
(*       merge: the pipe module files the merge at the prompt.             *)
(*                                                                        *)
(* [YR] IN THE DEVICE (design SS3.4d's OPEN paragraph).  The mode fires at *)
(* the right writer's first byte and needs [YR], a fact about the READ    *)
(* side (a byte reached the reader), which a write law cannot produce: a  *)
(* tree at [DOut [L]] may write before it reads.  Today's supply is        *)
(* [UShPipeCatRound.pipe_cat_w]'s -- [YR] handed in from outside -- and   *)
(* the device carries it as a persistent conjunct, so this instance is    *)
(* for a program that holds [YR] when it writes, i.e. one that read       *)
(* before it wrote (cat).  The coupled device kind is an owner ruling and *)
(* is not attempted here.                                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys.
Require Import VcGen.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
Require Import FdSlots ProcGeom UserFd.
Require Import UexecSG UexecSlot UexecRet.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import ObsTrace ConsLog.
Require Import LineWords LineBytes EchoDisc.
Require Import EchoOut AppEcho.
Require Import EchoOutPure.
Require Import LineModel LineModelLinks.
Require Import GenOutPure GenOut GenLinksLine.
Require Import PipeDisc.
Require Import PipeOutPure PipeOut.
Require Import PipeBothPure PipeBoth.
Require Import PipeNames PipeQueue PipeProto.  (* [pipeN] *)
Require Import PipeLinks PipeLinksLine PipeLinkInst.
Require Import UShPipeRound2.      (* [blk2N] *)
Require Import UShPipeCatRound.    (* [pcat_ch], [pcat_step_at] *)
Require Import CtxIdDefs.
(* [UserHeap] LAST among the U-tier libraries, as [UkConsOut] has it *)
Require Import UserHeap.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Require Import UkConsOut.
Local Open Scope Z_scope.

Section UkPipeConsOut.
  (* [UShPipeCatRound.v]'s binder list *)
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).

  Local Notation PT := (echo_taint γ).

  (* =================================================================== *)
  (*  S1  THE SINGLE-WRITER ROUNDS: the generic device at the pipeline's  *)
  (*      parameters and links                                            *)
  (* =================================================================== *)
  Lemma pipe_links_gl_w : pipe_links g -∗ gl_w pipe_lm (pipe_params g).
  Proof using .
    iIntros "Hlk". iDestruct (pipe_links_gl g with "Hlk") as "(H & _)". iExact "H".
  Qed.
  Lemma pipe_links_gl_blk : pipe_links g -∗ gl_blk pipe_lm (pipe_params g).
  Proof using .
    iIntros "Hlk". iDestruct (pipe_links_gl g with "Hlk") as "(_ & H & _)". iExact "H".
  Qed.
  Lemma pipe_links_gl_taint : pipe_links g -∗ gl_taint pipe_lm (pipe_params g).
  Proof using .
    iIntros "Hlk". iDestruct (pipe_links_gl g with "Hlk") as "(_ & _ & _ & _ & H)".
    iExact "H".
  Qed.

  (* the generic device, at the pipeline's single-writer rounds *)
  Local Notation pcons_dev1 := (cons_dev pipe_lm (pipe_params g) (pipe_links g)).

  Section single_writer.
    Context (N : uk_names Σ).

    Local Instance cat_prog_code_persistent1 : Persistent (up_code (cat_prog N)).
    Proof using . simpl. apply _. Qed.

    Lemma pcons1_write_echo (l : list fdstate) (fd : nat) (rb : bool)
        (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
      (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
      a ∈ alts -> bs `prefix_of` a ->
      UserFd.ustd (ukn_fd N) l -∗ pcons_dev1 alts -∗
      (UserFd.ustd (ukn_fd N) l -∗ pcons_dev1 [drop (length bs) a]
       -∗ K (Z.of_nat (length bs))) -∗
      wr_obl N (echo_prog N) (Z.of_nat fd) bs K.
    Proof using .
      exact (cons_write_gl pipe_lm (pipe_params g) (pipe_links g)
               (LINKS_pers := pipe_links_persistent g)
               pipe_links_gl_w pipe_links_gl_blk pipe_links_gl_taint
               N (echo_prog N) (echo_stub_write N) l fd rb alts a bs K).
    Qed.

    Lemma pcons1_write_cat (l : list fdstate) (fd : nat) (rb : bool)
        (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
      (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
      a ∈ alts -> bs `prefix_of` a ->
      UserFd.ustd (ukn_fd N) l -∗ pcons_dev1 alts -∗
      (UserFd.ustd (ukn_fd N) l -∗ pcons_dev1 [drop (length bs) a]
       -∗ K (Z.of_nat (length bs))) -∗
      wr_obl N (cat_prog N) (Z.of_nat fd) bs K.
    Proof using .
      exact (cons_write_gl pipe_lm (pipe_params g) (pipe_links g)
               (LINKS_pers := pipe_links_persistent g)
               pipe_links_gl_w pipe_links_gl_blk pipe_links_gl_taint
               N (cat_prog N) (cat_stub_write N) l fd rb alts a bs K).
    Qed.
  End single_writer.

  (* =================================================================== *)
  (*  S2  THE RIGHT WRITER OF A TWO-WRITER ROUND ([popen])                *)
  (* =================================================================== *)
  Section popen.
    (* the round: its pins, its line, the family's three ghosts, the two
       sides' facts *)
    Context (v : era_pins) (I L : list (bv 8)).
    Context (gL gR gM : gname) (XL YR : iProp Σ).
    Context {XL_tl : Timeless XL} {YR_tl : Timeless YR} {YR_pers : Persistent YR}.
    #[local] Existing Instance XL_tl.
    #[local] Existing Instance YR_tl.
    #[local] Existing Instance YR_pers.
    (* ...and the pure facts [UShPipeCatRound.pipe_cat_w] takes, exactly as
       [UShPipeLaw.pl_cat_kround] discharges them *)
    Context (Hnd : Forall nodollar L).
    Context (Hwit2 : forall sel : list bool,
               sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel).
    Context (Hwit1 : forall sel : list bool,
               count_true sel = 0%nat -> (length sel <= length L)%nat ->
               pblk2_wit I L sel).

    (* THE DEVICE: cat's cursor half at [c], owing the rest of the line *)
    Definition pcons_dev (alts : list (list (bv 8))) : iProp Σ :=
      (⌜cons_short alts⌝
       ∗ era_pin γ (S gen_id) v
       ∗ pipe_link_taint g
       ∗ blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR
       ∗ □ (XL -∗ YR ={↑pipeN}=∗ False)
       ∗ YR
       ∗ (∃ c : nat, ⌜alts = [drop c L]⌝ ∗ pcat_ch g gR gM c))%I.

    (* the device from the cursor, at a line the kernel can count *)
    Lemma pcons_dev_of_ch (c : nat) :
      (Z.of_nat (length L) < 2 ^ 31)%Z ->
      era_pin γ (S gen_id) v -∗
      pipe_link_taint g -∗
      blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
      □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
      YR -∗
      pcat_ch g gR gM c -∗
      pcons_dev [drop c L].
    Proof using YR_pers.
      intros HL. iIntros "#Hpin #Ht #Hinv #Hex #HYR Hc".
      iSplit.
      { iPureIntro. apply Forall_singleton.
        eapply Z.le_lt_trans; [| exact HL].
        apply Nat2Z.inj_le. rewrite length_drop. lia. }
      iFrame "Hpin Ht Hinv HYR". iSplitR; [iExact "Hex" |].
      iExists c. iSplit; [done |]. iExact "Hc".
    Qed.

    Lemma pcons_dev_short (alts : list (list (bv 8))) :
      pcons_dev alts -∗ ⌜cons_short alts⌝.
    Proof using . iIntros "($ & _)". Qed.

    (* the device owes ONE alternative: narrowing is the identity *)
    Lemma pcons_dev_sub (alts : list (list (bv 8))) (a : list (bv 8)) :
      a ∈ alts -> pcons_dev alts -∗ pcons_dev [a].
    Proof using YR_pers.
      intros Ha. iIntros "(%Hs & #Hpin & #Ht & #Hinv & #Hex & #HYR & %c & %Hal & Hc)".
      subst alts. apply elem_of_list_singleton in Ha as ->.
      iSplit; [iPureIntro; exact Hs |].
      iFrame "Hpin Ht Hinv HYR". iSplitR; [iExact "Hex" |].
      iExists c. iSplit; [done |]. iExact "Hc".
    Qed.

    (* ONE BYTE: [UShPipeCatRound.pcat_step_at] at the cursor *)
    Lemma pcons_dev_step (x : list (bv 8)) (b : bv 8) :
      x !! 0%nat = Some b ->
      pcons_dev [x] -∗ out_link Uart0 (S gen_id) b (pcons_dev [drop 1 x]).
    Proof using Hcons Hnd Hwit1 Hwit2 XL_tl YR_pers YR_tl.
      intros Hb. iIntros "(%Hs & #Hpin & #Ht & #Hinv & #Hex & #HYR & %c & %Hal & Hc)".
      injection Hal as Hx. subst x.
      rewrite lookup_drop Nat.add_0_r in Hb.
      assert (Hs' : cons_short [drop 1 (drop c L)]).
      { unfold cons_short in *. apply Forall_singleton. rewrite Forall_singleton in Hs.
        eapply Z.le_lt_trans; [| exact Hs].
        apply Nat2Z.inj_le. rewrite length_drop. lia. }
      iApply (pcat_step_at g Hcons v I L gL gR gM XL YR c b _ Hb Hnd Hwit2 Hwit1
                with "Hex Ht Hpin Hinv HYR Hc").
      iIntros "Hc".
      iSplit; [iPureIntro; exact Hs' |].
      iFrame "Hpin Ht Hinv HYR". iSplitR; [iExact "Hex" |]. iExists (S c).
      iSplit.
      { iPureIntro. f_equal. rewrite drop_drop. f_equal. lia. }
      iExact "Hc".
    Qed.

    (* THE CORE AT THIS DEVICE: the write law of any program instance *)
    Section popen_prog.
      Context (N : uk_names Σ) (P : uprog Σ).
      Context `{HPc : !Persistent (up_code P)}.
      Context (Hstub : ⊢ stub_law N (up_code P) 16 (up_write P)).

      Lemma pcons_write (l : list fdstate) (fd : nat) (rb : bool)
          (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
        (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
        a ∈ alts -> bs `prefix_of` a ->
        UserFd.ustd (ukn_fd N) l -∗ pcons_dev alts -∗
        (UserFd.ustd (ukn_fd N) l -∗ pcons_dev [drop (length bs) a]
         -∗ K (Z.of_nat (length bs))) -∗
        wr_obl N P (Z.of_nat fd) bs K.
      Proof using HPc Hcons Hnd Hstub Hwit1 Hwit2 XL_tl YR_pers YR_tl.
        exact (cons_write N P Hstub pcons_dev pcons_dev_short pcons_dev_sub
                 pcons_dev_step l fd rb alts a bs K).
      Qed.
    End popen_prog.

    (* the witness: cat, the right writer the pipeline runs *)
    Section popen_cat.
      Context (N : uk_names Σ).

      Local Instance cat_prog_code_persistent2 : Persistent (up_code (cat_prog N)).
      Proof using . simpl. apply _. Qed.

      Lemma pcons_write_cat (l : list fdstate) (fd : nat) (rb : bool)
          (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
        (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
        a ∈ alts -> bs `prefix_of` a ->
        UserFd.ustd (ukn_fd N) l -∗ pcons_dev alts -∗
        (UserFd.ustd (ukn_fd N) l -∗ pcons_dev [drop (length bs) a]
         -∗ K (Z.of_nat (length bs))) -∗
        wr_obl N (cat_prog N) (Z.of_nat fd) bs K.
      Proof using Hcons Hnd Hwit1 Hwit2 XL_tl YR_pers YR_tl.
        exact (pcons_write N (cat_prog N) (cat_stub_write N) l fd rb alts a bs K).
      Qed.
    End popen_cat.
  End popen.
End UkPipeConsOut.
