(* ===================================================================== *)
(*  UShPipeCatRound.v -- CAT'S CONSOLE BYTE AT THE PIPELINE ROUND'S      *)
(*  TWO-WRITER FAMILY (lane SH-PIPE-ROUND-9, ROUND-8's bill item 3;      *)
(*  design claude-notes/design/app-pipe.md SS4.3r/SS4.3s).                *)
(*                                                                       *)
(*  A pipeline round has no link record behind its right chain: cat's    *)
(*  console bytes belong to the two-writer family ([PipeBoth.blk2_inv])  *)
(*  at MODE 1.  This file holds the family cat's turn carries            *)
(*  ([pcat_ch]: the right cursor and the mode, or the taint) and ONE     *)
(*  BYTE of cat's output at it ([pcat_step_at]), which the tree route's  *)
(*  console device reads.  The multi-byte discharge of the old per-      *)
(*  program round's write ([pipe_cat_w] over [UCatPipe]) was deleted by  *)
(*  the pipe sweep.                                                      *)
(*                                                                       *)
(*  TWO THINGS A BYTE HERE DOES THAT THE FILE ERA'S DOES NOT.            *)
(*                                                                       *)
(*   - THE MODE HAS TO FIRE, and it fires at cat's FIRST BYTE.           *)
(*     [PipeBoth.blk2_mode_fire] is a FANCY UPDATE, and the only fupd    *)
(*     site is INSIDE the byte: [WpUart.out_link]'s conclusion is a      *)
(*     [={⊤ ∖ ↑uartN Uart0}=∗], and [↑blk2N] misses [↑uartN Uart0]       *)
(*     ([UShPipeRound2.blk2N_uart]).  [fupd_out_link] is the peel and    *)
(*     [pcat_ch]'s index carries the mode: 0 at cursor 0, 1 after.       *)
(*   - THE TAINT ARM IS NOT FREE.  The family here is two EXCLUSIVE      *)
(*     cursor halves, so [pcat_ch] gets the taint as its own second arm, *)
(*     and at a tainted turn the halves are simply dropped -- which is   *)
(*     sound because a tainted round's exit is                           *)
(*     [PipeLinksLine.pwc_line2_taint] and wants no family at all.       *)
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
Require Import UserHeap UkRun UkRunSys.
Require Import VcGen.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeCat.
Require User.CatSyms User.CatInstrs.
Require Import FdSlots ProcGeom UserFd UserCwd.
Require Import UexecSG UexecSlot UexecRet.
Require Import UkCat.
Require Import UkCatCat.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import ObsTrace ConsLog.
Require Import LineWords EchoDisc.
Require Import EchoOut AppEcho.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeOutPure PipeOut.
Require Import PipeBothPure PipeBoth.
Require Import PipeNames PipeQueue PipeProto.  (* [pipeN] *)
Require Import PipeLinks PipeLinksLine PipeLinkInst.
Require Import UShPipeRound2.      (* [blk2N] and its two mask facts *)
Require Import UShPipeAssembly.
Require Import CtxIdDefs.
Local Open Scope Z_scope.

Section UShPipeCatRound.
  (* [UCatKernel.v]'s binder list, with the FILE claim's two classes
     replaced by the pipeline's one.  NO [uexecSG] and NO [uprogSG]
     section variable, for that file's reason. *)
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* ...AND THE TWO [ghost_var] CLASSES [UkCat.kcat_wr] IS INDEXED BY
     (lane SH-PIPE-ROUND-14): bound here so a statement naming
     [kcat_wr] takes them from its CALL SITE instead of resolving them
     through the [xv6G] bundle -- two [ghost_varG Sigma Z] terms print
     identically and do not unify (SH-PIPE-ROUND-13). *)
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ}.
  (* ...AND THE PROGRAM INSTANCE IS A SECTION VARIABLE (design SS4.3z item
     2, one file over; lane SH-PIPE-ROUND-13).  The header above said "NO
     [uprogSG] section variable, for [UCatKernel.v]'s reason" -- and
     ROUND-12 STRUCK that reason for cat's whole entry chain
     ([UShCat.v], [UShCatPay.v], [UCatPipe.v], [UCatKernel.v] SS7 all bind
     one now).  This file is the last of the chain and it was left behind:
     every [UkCat.kcat_wr] in its statements was elaborating at the
     AMBIENT [UexecExecInst.uprogSG_gen], while the pipeline round enters
     cat's image at [uprogSG_free], and the two print identically and do
     not unify.  A [Context] variable is what stops the resolution search;
     the geometry never reads the instance, so nothing else moves. *)
  Context `{PS : UexecSG.uprogSG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).
  Local Notation PT := (echo_taint γ).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S1  A FANCY UPDATE IN FRONT OF A CONSOLE BYTE                       *)
  (* =================================================================== *)
  Lemma fupd_out_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    (|={⊤ ∖ ↑uartN Uart0}=> out_link Uart0 k b Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    rewrite /out_link. iIntros "H" (o H0) "Hlb Hres".
    iMod "H". iApply ("H" $! o H0 with "Hlb Hres").
  Qed.

  Lemma blk2N_in_uart : (↑blk2N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset).
  Proof using .
    apply subseteq_difference_r; [ exact blk2N_uart | apply top_subseteq ].
  Qed.

  (* =================================================================== *)
  (*  S2  THE FAMILY CAT'S TURN CARRIES                                   *)
  (*                                                                     *)
  (*  The two-writer family's RIGHT cursor, and the mode -- 0 before      *)
  (*  cat's first byte, 1 after it -- or the taint.                       *)
  (* =================================================================== *)
  Definition pcat_ch (gR gM : gname) (c : nat) : iProp Σ :=
    ((PipeBoth.wcur gR (1/2) c
      ∗ PipeBoth.wcur gM (1/2) (match c with O => 0%nat | _ => 1%nat end))
     ∨ PT)%I.

  Lemma pcat_ch_taint (gR gM : gname) (c : nat) : PT -∗ pcat_ch gR gM c.
  Proof using . iIntros "#HT". rewrite /pcat_ch. by iRight. Qed.

  (* =================================================================== *)
  (*  S3  ONE BYTE OF CAT'S OUTPUT                                        *)
  (*                                                                     *)
  (*  [PipeBoth.pblk2_cstep_R] at mode 1, with the mode's FIRE folded     *)
  (*  into the first byte.                                               *)
  (* =================================================================== *)
  Lemma pcat_step_at (v : era_pins) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ)
      `{!Timeless XL} `{!Timeless YR} `{!Persistent YR}
      (i : nat) (b : bv 8) (Φ : iProp Σ) :
    L !! i = Some b ->
    Forall nodollar L ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    (forall sel : list bool,
       count_true sel = 0%nat -> (length sel <= length L)%nat ->
       pblk2_wit I L sel) ->
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    pipe_link_taint g -∗
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    YR -∗
    pcat_ch gR gM i -∗
    (pcat_ch gR gM (S i) -∗ Φ) -∗
    out_link Uart0 (S gen_id) b Φ.
  Proof using Hcons.
    intros Hb Hnd Hwit2 Hwit1.
    iIntros "#Hex #Ht #Hpin #Hinv #HYR Hf HΦ".
    rewrite {1}/pcat_ch. iDestruct "Hf" as "[Hcur | #HT]"; last first.
    { iApply ("Ht" $! (S gen_id) b Φ with "HT").
      iIntros "#HT2". iApply "HΦ". iApply (pcat_ch_taint gR gM with "HT2"). }
    (* the byte, at the family's right chain and mode 1 *)
    iAssert (|={⊤ ∖ ↑uartN Uart0}=>
               PipeBoth.wcur gR (1/2) i ∗ PipeBoth.wcur gM (1/2) 1%nat)%I
      with "[Hcur]" as "Hfire".
    { destruct i as [| q].
      - iDestruct "Hcur" as "[HcR HcM]".
        iMod (blk2_mode_fire g (⊤ ∖ ↑uartN Uart0) blk2N (S gen_id) v I L
                gL gR gM XL YR 1%nat _ _ blk2N_in_uart ltac:(by left)
                with "Hinv HcM HcR []") as "[HcM HcR]".
        { iIntros "_". iExact "HYR". }
        iModIntro. iFrame "HcR HcM".
      - iModIntro. iExact "Hcur". }
    iApply fupd_out_link. iMod "Hfire" as "[HcR HcM]". iModIntro.
    iApply (pblk2_cstep_R g Hcons blk2N (↑pipeN) (S gen_id) v I L
              gL gR gM XL YR 1%nat i b Φ _ _ blk2N_uart blk2N_pipeN
              ltac:(by left) ltac:(cbn [rsrc]; exact Hb)
              ltac:(cbn [rsrc]; exact Hnd) Hwit2 Hwit1
              with "Hex [] Ht Hpin Hinv HcR HcM").
    { iApply pblk2_ecl_R_holds. }
    iIntros "HcR HcM". iApply "HΦ". rewrite /pcat_ch. iLeft.
    iFrame "HcR HcM".
  Qed.

End UShPipeCatRound.
