(* ===================================================================== *)
(*  UShPipeCatRound.v -- CAT'S CONSOLE TURN AT THE PIPELINE ROUND'S      *)
(*  TWO-WRITER FAMILY (lane SH-PIPE-ROUND-9, ROUND-8's bill item 3;      *)
(*  design claude-notes/design/app-pipe.md SS4.3r/SS4.3s).                *)
(*                                                                       *)
(*  [UCatKernel.cat_w_of_link] is the FILE era's discharge of            *)
(*  [UCatPipe.pcat_round_at_g]'s [Hw] -- the multi-byte [write(1, buf,   *)
(*  n)] cat's loop makes -- and it writes through the LINK RECORD's own  *)
(*  block family.  A pipeline round has no record behind its right       *)
(*  chain: the bytes belong to the two-writer family                     *)
(*  ([PipeBoth.blk2_inv]) at MODE 1.  This file is that discharge, and   *)
(*  it is the mould's proof with three substitutions and nothing else:   *)
(*                                                                       *)
(*    [UCatOut.cch … (p + j)]      ->  [pcat_ch gR gM (c + j)]           *)
(*    [UCatOut.cch_chain]          ->  [UShPipeAssembly.out_chain_of_step] *)
(*    [UCatOut.cch_chain_taint]    ->  [pcat_chain_taint]                *)
(*                                                                       *)
(*  TWO THINGS THE MOULD DOES NOT HAVE TO DO.                            *)
(*                                                                       *)
(*   - THE MODE HAS TO FIRE, and it fires at cat's FIRST BYTE.           *)
(*     [PipeBoth.blk2_mode_fire] is a FANCY UPDATE, and the round's      *)
(*     entry into cat ([UShCatPay.sh_exec_sup_cat_wq_holds_at]'s         *)
(*     [Hround]) is a PURE wand -- so there is no fupd site before the   *)
(*     walk.  There is one INSIDE: [WpUart.out_link]'s conclusion is a   *)
(*     [={⊤ ∖ ↑uartN Uart0}=∗], and [↑blk2N] misses [↑uartN Uart0]       *)
(*     ([UShPipeRound2.blk2N_uart]).  [fupd_out_link] is the peel and    *)
(*     [pcat_ch]'s index carries the mode: 0 at cursor 0, 1 after.       *)
(*   - THE TAINT ARM IS NOT FREE.  [UCatOut.cch] has a taint disjunct of *)
(*     its own, so the mould's taint chain is [by iRight] at every byte; *)
(*     the family here is two EXCLUSIVE cursor halves.  So [pcat_ch]     *)
(*     gets the taint as its own second arm, and at a tainted turn the   *)
(*     halves are simply dropped -- which is sound because a tainted     *)
(*     round's exit is [PipeLinksLine.pwc_line2_taint] and wants no      *)
(*     family at all.                                                    *)
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
Require Import UCatKernel.         (* [cat_fam] / [cat_count_is] / [cat_moi_uint] *)
Require Import UShPipeRound2.      (* [blk2N] and its two mask facts *)
Require Import UShPipeAssembly.    (* [out_step] / [out_chain_of_step] *)
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
     (lane SH-PIPE-ROUND-14; design SS4.3ab's ruling REFUTED at its own
     guess -- see below).  [UkCat.kcat_wr]'s implicit list is
     [{Sigma riscvGS ufdG GEN ghost_varG0 ghost_varG1} N {ctokG SG PS}],
     and THIS file bound neither [ghost_var] class, so both were resolved
     THROUGH the [xv6G] bundle ([Xv6Cameras.offbox_offG (Xv6G.xv6_offbox
     ...)] and [Xv6Cameras.uch_inG (Xv6G.xv6_uch ...)]) and BAKED INTO
     [pipe_cat_w]'s conclusion.  [UCatPipe.v] binds both as SECTION
     VARIABLES, so [pcat_round_at_g]'s [Hw] names them at whatever the
     CALL SITE has -- and the call site ([UShPipeLaw.v]) binds
     [ghost_varG Sigma Z] itself.  Two different [ghost_varG Sigma Z]
     terms, one [kcat_wr] each: that is SH-PIPE-ROUND-13's "they print
     identically and do not unify".  [uexecSG] was NOT the second
     instance -- both sides elaborate it to [uexecSG_xv6 Sigma HRg xv6G0
     fileG0 GEN], measured with [Set Printing Implicit] -- and a
     [Context {SG}] here would in fact CREATE one, because
     [UCatKernel.cat_fam], which this file's proof applies, binds none. *)
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

  (* the mould's [cch_chain_taint]: at a tainted era every byte goes out
     on the link's own taint leaf and the family is the taint arm *)
  Lemma pcat_chain_taint (gR gM : gname) (M : gmap Z (bv 8))
      (ua : mword 64) (c0 : nat) :
    forall (c i : nat),
    pipe_link_taint g -∗ PT -∗
    cons_out_chain (S gen_id) M ua
      (fun j : nat => pcat_ch gR gM (c0 + j)%nat) i c.
  Proof using .
    intros c. induction c as [| c IH]; intros i.
    - iIntros "#Ht #HT". cbn [cons_out_chain].
      iApply (pcat_ch_taint gR gM with "HT").
    - iIntros "#Ht #HT". cbn [cons_out_chain]. iSplit.
      + iApply (pcat_ch_taint gR gM with "HT").
      + iIntros (b) "_".
        iApply ("Ht" $! (S gen_id) b _ with "HT").
        iIntros "_". iApply (IH (S i) with "Ht HT").
  Qed.

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

  (* ...and the step family [out_chain_of_step] takes, at the OFFSET the
     write's buffer is indexed by *)
  Lemma pcat_out_step (v : era_pins) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ)
      `{!Timeless XL} `{!Timeless YR} `{!Persistent YR} (c0 : nat) :
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
    out_step (drop c0 L) (fun j : nat => pcat_ch gR gM (c0 + j)%nat).
  Proof using Hcons.
    intros Hnd Hwit2 Hwit1.
    iIntros "#Hex #Ht #Hpin #Hinv #HYR".
    rewrite /out_step. iIntros "!>" (p b Φ) "%Hb Hf HΦ".
    assert (HbL : L !! (c0 + p)%nat = Some b)
      by (rewrite -(lookup_drop L c0 p); exact Hb).
    assert (Es : (c0 + S p)%nat = S (c0 + p)%nat) by lia.
    rewrite Es.
    iApply (pcat_step_at v I L gL gR gM XL YR (c0 + p)%nat b Φ
              HbL Hnd Hwit2 Hwit1 with "Hex Ht Hpin Hinv HYR Hf HΦ").
  Qed.

  (* =================================================================== *)
  (*  S4  [Hw] ITSELF -- [UCatKernel.cat_w_of_link] at the pipeline       *)
  (*      round's right chain (ROUND-8's bill, item 3).                   *)
  (* =================================================================== *)
  Lemma pipe_cat_w (v : era_pins) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ)
      `{!Timeless XL} `{!Timeless YR} `{!Persistent YR}
      (l : list fdstate) (rb : bool)
      (c0 nb : nat) (rv : mword 64) (fbb : nat -> bv 8) :
    Forall nodollar L ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    (forall sel : list bool,
       count_true sel = 0%nat -> (length sel <= length L)%nat ->
       pblk2_wit I L sel) ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    rv = (mword_of_int (Z.of_nat nb) : mword 64) ->
    (Z.to_nat (bv_unsigned rv) <= 512)%nat ->
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    pipe_link_taint g -∗
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    (* THE READER'S BOUND, UNDER THE TAINT (design SS4.3aa, item 2).
       [YR] is used at exactly ONE place below -- inside the left arm of the
       [Hjust] split, where the family's right chain is actually stepped --
       and the only supplier the round has is [UCatPipe.pcat_round_at_g]'s
       [Hw] antecedent, which offers [pws_lb pn (take (c + cnt) L) or T].
       So the premise is taken under the same disjunction and the taint arm
       goes through [pcat_chain_taint] like the other two.  The landed form
       re-derives by [iLeft].

       ...AND A THIRD ARM, [cnt = 0] (lane SH-PIPE-ROUND-13).  The round's
       supplier holds [pws_lb pn (take (c + cnt) L)], which entails
       [YR = pws_lb pn (take 1 L)] only when [0 < c + cnt]; at a turn that
       delivered NO byte there is no bound to weaken.  There is also nothing
       to step: at [cnt = 0] the chain IS the cursor
       ([SpecConsolewrite.cons_out_chain_0]) and [out_chain_of_step] never
       looks at the step.  So the empty turn is its own arm, and the supplier
       takes it by [decide (cnt = 0)] rather than by proving a bound it
       cannot have. *)
    (YR ∨ PT ∨ ⌜(Z.to_nat (bv_unsigned rv) = 0)%nat⌝) -∗
    (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
      /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
           L !! (c0 + j)%nat = Some (fbb j)⌝
     ∨ PT) -∗
    UserFd.ustd γfd l -∗
    pcat_ch gR gM c0 -∗
    UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
      (ubytes γd CatSyms.buf 512 fbb)
      (fun wret : mword 64 =>
         (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
          ∗ UserFd.ustd γfd l
          ∗ pcat_ch gR gM (c0 + Z.to_nat (bv_unsigned rv))%nat
          ∗ ubytes γd CatSyms.buf 512 fbb)).
  Proof using Hcons.
    intros Hnd Hwit2 Hwit1 Hl1 Hrv Hcap.
    set (cnt := Z.to_nat (bv_unsigned rv)).
    pose proof (bv_unsigned_in_range 64 rv) as [Hrvnn _].
    assert (Hmoi : (mword_of_int (Z.of_nat cnt) : mword 64) = rv).
    { unfold cnt. rewrite Z2Nat.id; [ | exact Hrvnn ].
      exact (cat_moi_uint rv). }
    assert (Hcz : sys_rw_count rv = Z.of_nat cnt).
    { rewrite <- Hmoi. apply cat_count_is.
      change (2 ^ 31)%Z with 2147483648%Z. lia. }
    iIntros "#Hex #Ht #Hpin #Hinv #HYR Hjust Hstd Hc" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode Hbuf Hrun Hcont".
    assert (Hua : uint (m !!! Regidx a1_idx) = CatSyms.buf).
    { rewrite Ha1. apply uint_moi. unfold Z64, CatSyms.buf. lia. }
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx = rv).
    { rewrite Hrv. rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1)
      by (rewrite Ham0; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = cnt)
      by (rewrite Ham2 Hcz; lia).
    (* ---- THE CHAIN, from the family's right chain or from the taint ---- *)
    iAssert (∀ M : gmap Z (bv 8),
               ⌜forall j : nat, (j < cnt)%nat ->
                  M !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
                  = Some (fbb j)⌝ -∗
               cons_out_chain (S gen_id) M (m !!! Regidx a1_idx)
                 (fun j : nat => pcat_ch gR gM (c0 + j)%nat) 0%nat cnt)%I
      with "[Hc Hjust]" as "Hmk".
    { iDestruct "HYR" as "[#HYRy | [#HTy | %Hcz0]]".
      3: { (* the EMPTY turn: no byte, no step, and the chain is the cursor *)
           iIntros (M) "_". rewrite Hcz0 cons_out_chain_0 Nat.add_0_r.
           iExact "Hc". }
      2: { iIntros (M) "_".
           iApply (pcat_chain_taint gR gM M (m !!! Regidx a1_idx) c0 cnt 0%nat
                     with "Ht HTy"). }
      iDestruct "Hjust" as "[[%_ %Hline] | #HT]"; last first.
      { iIntros (M) "_".
        iApply (pcat_chain_taint gR gM M (m !!! Regidx a1_idx) c0 cnt 0%nat
                  with "Ht HT"). }
      rewrite {1}/pcat_ch. iDestruct "Hc" as "[Hcur | #HT]"; last first.
      { iIntros (M) "_".
        iApply (pcat_chain_taint gR gM M (m !!! Regidx a1_idx) c0 cnt 0%nat
                  with "Ht HT"). }
      iIntros (M) "%HM".
      iApply (out_chain_of_step (drop c0 L)
                (fun j : nat => pcat_ch gR gM (c0 + j)%nat)
                M (m !!! Regidx a1_idx) fbb cnt 0%nat
                ltac:(intros j _ Hj;
                      rewrite (lookup_drop L c0 j); apply Hline; lia)
                ltac:(intros j _ Hj; apply HM; lia)
                with "[] [Hcur]").
      - iApply (pcat_out_step v I L gL gR gM XL YR c0 Hnd Hwit2 Hwit1
                  with "Hex Ht Hpin Hinv HYRy").
      - rewrite Nat.add_0_r /pcat_ch. iLeft. iExact "Hcur". }
    (* ---- THE RUN: the prefix the call writes, and its two halves ---- *)
    pose (nr := (512 - cnt)%nat).
    assert (Hsz : (cnt + nr)%nat = 512%nat) by (unfold nr; lia).
    iAssert (ubytes γd CatSyms.buf cnt fbb
             ∗ ubytes γd (CatSyms.buf + Z.of_nat cnt) nr
                 (fun j : nat => fbb (cnt + j)%nat))%I
      with "[Hbuf]" as "[Hpre Hsuf]".
    { rewrite <- (ubytes_app γd CatSyms.buf cnt nr fbb).
      rewrite Hsz. iExact "Hbuf". }
    iAssert (ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx)) cnt fbb
             ∗ ubytesq γd (DfracOwn (1/2)) (uint (m !!! Regidx a1_idx))
                 cnt fbb)%I with "[Hpre]" as "[Hh1 Hh2]".
    { rewrite Hua. rewrite <- (ubytes_halve γd CatSyms.buf cnt fbb).
      iExact "Hpre". }
    (* ---- THE CALL ---- *)
    iApply (UkCat.wp_kcat_write_chain N h m avail
              (UCatKernel.cat_fam N
                 (fun j : nat =>
                    (pcat_ch gR gM (c0 + j)%nat
                     ∗ ubytesq γd (DfracOwn (1/2))
                         (uint (m !!! Regidx a1_idx)) cnt fbb)%I))
              l (DfracOwn (1/2)) cnt fbb
              with "Hcode Hrun [Hmk Hh2] Hstd Hh1").
    { iApply (uwrite_chain_sup_ret N
                (fun j : nat => pcat_ch gR gM (c0 + j)%nat)
                (ubytesq γd (DfracOwn (1/2))
                   (uint (m !!! Regidx a1_idx)) cnt fbb)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int CatSyms.write : mword 64) 2)
                l 1%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl1).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat γt γd (ukn_s N) M pm sz
                   (DfracOwn (1/2)) (m !!! Regidx a1_idx) cnt fbb
                   with "Hheap Hh2") as %HM.
      iFrame "Hheap Hh2".
      rewrite Ham1 Hcnt.
      iApply ("Hmk" $! M with "[%]"). exact HM. }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hh1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun j : nat =>
                    (pcat_ch gR gM (c0 + j)%nat
                     ∗ ubytesq γd (DfracOwn (1/2))
                         (uint (m !!! Regidx a1_idx)) cnt fbb)%I)
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W) cw' cs'
                 l 1%nat rb cnt
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl1
                 ltac:(rewrite Hka2 Ha2 -Hrv; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hws [Hcc Hh2]]".
    iApply ("Hcont" $! h' ret with "[Hstd Hcc Hh1 Hh2 Hsuf] Hrun").
    iSplitR.
    { iPureIntro. rewrite Hws Hmoi. exact Hrv. }
    iFrame "Hstd Hcc".
    rewrite <- Hsz. rewrite (ubytes_app γd CatSyms.buf cnt nr fbb).
    iSplitR "Hsuf"; [ | iExact "Hsuf" ].
    rewrite (ubytes_halve γd CatSyms.buf cnt fbb) -Hua.
    iFrame "Hh1 Hh2".
  Qed.

End UShPipeCatRound.
