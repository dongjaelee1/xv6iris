(* ===================================================================== *)
(*  UShPipeLawRes.v -- THE PIPELINE ROUND'S RESOURCE LAYER, split out of  *)
(*  [UShPipeLaw.v] (lane REPOINT-PIPE; design program-specs SS3.4g).      *)
(*                                                                       *)
(*  WHY A SEPARATE FILE.  [UkPipeEntries.v] states the pipeline's two     *)
(*  tree-route entries at the round's lend ([pl_RcR]) and its payload     *)
(*  conversions ([pl_qc_of_cend]), while [UShPipeLaw.v]'s two children     *)
(*  now CONSUME those entries -- an import cycle as long as both halves   *)
(*  live in one file.  So the round's names, its lend, the four-way       *)
(*  split, the two diagnostic laws read off the credential and the four   *)
(*  payload conversions live HERE, below [UkPipeEntries.v]; the           *)
(*  registrar ([UShPipeLaw.pl_pipe_call]), cat's round, the three         *)
(*  continuations and the child law stay in [UShPipeLaw.v], which         *)
(*  imports both.  Every statement is [UShPipeLaw.v]'s verbatim, in a     *)
(*  section with its binder list verbatim; only the module qualifier of   *)
(*  the names moved.                                                     *)
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
Require Import UserPtTree.
Require Import UserCwd.
Require Import UserChildren.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import ChildTok.
Require Import FsImg.
Require Import UexecSlot UexecRet UexecSG.
Require Import UexecExecInst.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import WpUart.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileDisc.
Require Import PipeDisc.
Require Import PipeUline.
Require Import PipeNames.
Require Import PipeQueue.
Require Import PipeReg.
Require Import PipeProto.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppInv.
Require Import EchoOutPure.
Require Import PipeOutPure.
Require Import PipeOut.
Require Import PipeBothPure.
Require Import PipeBoth.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeHooks.         (* S0 of [PipeLinksLine], moved *)
Require Import PipeLinkInst.
Require Import GenLinksLine.
Require Import PipeStageInst.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShParse.
Require Import UkShWords.
Require Import UkShParseCmd.
Require Import UkShEcho.
Require Import UkShCat.
Require Import UkShFork.
Require Import UkShRun.
Require Import UkShPipe.
Require Import UkShPipeSeam.
Require Import UkShPipeLex.
Require Import UkShPipeRound.
Require Import UkShPipePaid.
Require Import UkShPipeFork.
Require Import UEchoPipe.
Require Import UCatPipe.
Require Import UShEcho.
Require Import UShPanic.
Require Import UShPipeRound2.
Require Import UShPipeAssembly.
Require Import UShPipeCatRound.
Require Import CtxIdDefs.
Require User.ShSyms.
Local Open Scope Z_scope.

Section UShPipeLawRes.
  (* [UShPipeLaw.v]'s binder list VERBATIM (itself [UShPipeRound.v]'s,
     the file whose law it discharges), PLUS [pipeProtoG] for the protocol's own ghosts -- which
     [UShPipeAssembly.v] binds for the same reason.  NO [uexecSG] and NO
     [uprogSG] SECTION VARIABLE (durable-notes: either makes every
     [UkRun.urun] in this file's statements a different proposition from
     the one the lemmas it applies were proved at). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ}.
  Context `{!pipeProtoG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).

  (* the record equations the top theorem hands over -- [UInitPipe.
     pipe_Hinit_boot] derives all three from [Hiface] *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = pecl g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = echo_taint γ).

  Local Notation T := (echo_taint γ).
  Local Notation PI := (pipe_link_inst_at g).


  (* =================================================================== *)
  (*  S2a  THE FAMILY'S INVARIANT AT *PRE-ALLOCATED* CURSOR NAMES         *)
  (*                                                                     *)
  (*  [PipeBoth.blk2_inv_alloc] mints the three cursor ghosts AND the     *)
  (*  invariant in one fancy update.  A round cannot use it: its payload  *)
  (*  [UShPipeAssembly.pipe_Qc_at] NAMES [gL]/[gR]/[gM], and the payload  *)
  (*  is fixed before the walk starts, while the invariant can only be    *)
  (*  born out of the lend the walk is given.  So the three ghosts are    *)
  (*  minted at the child law's own [mWP] entry and this is the           *)
  (*  allocation at them; the landed lemma is this one composed with      *)
  (*  three [ghost_var_alloc]s.                                          *)
  (* =================================================================== *)
  Lemma blk2_inv_alloc_at (E : coPset) (v : era_pins) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ) :
    pboth_line I ->
    PipeBoth.wcur gL (1/2) 0%nat -∗ PipeBoth.wcur gR (1/2) 0%nat -∗
    PipeBoth.wcur gM (1/2) 0%nat -∗
    PipeLinksLine.pwc_lend g (S gen_id) v I ={E}=∗
    PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR.
  Proof using .
    intros Hline. iIntros "HL HR HM Hlend".
    iDestruct (PipeBoth.pwc_blk2_of_lend g (S gen_id) v I dg_execR false
                 Hline with "Hlend") as "Hf".
    rewrite /PipeBoth.blk2_inv.
    iApply (inv_alloc blk2N E
              (PipeBoth.blk2_body g (S gen_id) v I L gL gR gM XL YR)).
    iNext. rewrite /PipeBoth.blk2_body. iLeft.
    iExists dg_execR, [], 0%nat, 0%nat, false.
    iFrame "Hf HL HR".
    iSplitR; [ by iLeft | ]. rewrite /PipeBoth.rmode. iExists 0%nat.
    iFrame "HM". iSplitR; [ by iPureIntro | ]. iLeft. by iPureIntro.
  Qed.

  (* =================================================================== *)
  (*  S2b'  THE ROUND'S NAMES AND ITS LEND (lane SH-PIPE-ROUND-12)        *)
  (*                                                                     *)
  (*  ROUND-11's finding (5), as a lemma: the protocol's [pn] and the     *)
  (*  family's three cursors are minted BEFORE the walk -- the payload    *)
  (*  [UShPipeAssembly.pipe_Qc_at] names all four and is fixed when       *)
  (*  [UShPipeChild.wp_kshm_child_pipe_paid_line_at_sz] is applied --     *)
  (*  while the family's INVARIANT can only be born out of the lend, so   *)
  (*  it rides inside [Cr] and the fupd the walk takes is the one below.  *)
  (*  The era pin comes off the child law's own antecedent and agrees     *)
  (*  with the one under the lend's existential.                          *)
  (* =================================================================== *)
  Definition pl_XL (pn : pnames) : iProp Σ := PipeProto.wcur pn 0%nat.
  Definition pl_YR (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    PipeProto.pws_lb pn (take 1%nat L).

  Global Instance pl_XL_timeless pn : Timeless (pl_XL pn).
  Proof using . rewrite /pl_XL /PipeProto.wcur. apply _. Qed.
  Global Instance pl_YR_timeless pn L : Timeless (pl_YR pn L).
  Proof using . rewrite /pl_YR /PipeProto.pws_lb. apply _. Qed.
  Global Instance pl_YR_persistent pn L : Persistent (pl_YR pn L) | 0.
  Proof using . rewrite /pl_YR. apply _. Qed.

  (* NAME THE LEAF, DO NOT SEARCH ([UShPipeRound.v]'s measured rule, met
     here by lane SH-PIPE-ROUND-14): an [iAssert ... as "#"] or an
     [iPoseProof ... as "#"] on a [UkShDiag.ush_execfail_law_at] sends the
     [Persistent] search into the law's own wand tower and does NOT come
     back -- measured, [Set Default Timeout 300] fired on exactly that
     [iAssert] and on nothing else in the file.  The instance EXISTS
     ([UkShDiag.ush_execfail_law_at_persistent]); the hint net does not
     reach it through the transparent definition. *)
  #[local] Instance pl_exf_at_pers0 (PSx : UexecSG.uprogSG Σ)
      (dg : list (bv 8)) (n : nat) (Cr Cd : iProp Σ) :
    Persistent (UkShDiag.ush_execfail_law_at (PS := PSx) dg n Cr Cd) | 0
    := UkShDiag.ush_execfail_law_at_persistent (PS := PSx) dg n Cr Cd.

  Definition pl_Cr (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) : iProp Σ :=
    (PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM
       (pl_XL pn) (pl_YR pn L)
     ∗ PipeBoth.wcur gL (1/2) 0%nat ∗ PipeBoth.wcur gR (1/2) 0%nat
     ∗ PipeBoth.wcur gM (1/2) 0%nat)%I.

  Lemma pl_round_alloc (v : era_pins) (I L : list (bv 8)) :
    pboth_line I ->
    era_pin γ (S gen_id) v -∗
    |==> ∃ (pn : pnames) (gL gR gM : gname),
      UShPipeAssembly.pipe_pre pn ∗ wtok pn ∗ rtok pn
      ∗ PipeProto.side_L pn ∗ PipeProto.side_R pn
      ∗ (UkShPipeFork.pterm_wc g I 3%nat ={⊤}=∗ pl_Cr v I L pn gL gR gM).
  Proof using .
    intros Hline. iIntros "#Hpin".
    iMod (UShPipeAssembly.pipe_names_alloc)
      as (pn) "(Hpre & Hw & Hr & HsL & HsR)".
    iMod (ghost_var_alloc (0%nat)) as (gL) "HgL".
    iMod (ghost_var_alloc (0%nat)) as (gR) "HgR".
    iMod (ghost_var_alloc (0%nat)) as (gM) "HgM".
    iDestruct (ghost_var_split gL 0%nat (1/2) (1/2) with "[HgL]")
      as "[HgL1 HgL2]"; [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split gR 0%nat (1/2) (1/2) with "[HgR]")
      as "[HgR1 HgR2]"; [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split gM 0%nat (1/2) (1/2) with "[HgM]")
      as "[HgM1 HgM2]"; [ by rewrite Qp.half_half | ].
    iModIntro. iExists pn, gL, gR, gM. iFrame "Hpre Hw Hr HsL HsR".
    iIntros "Hc".
    iDestruct (UkShPipeFork.pterm_wc_3 g I with "Hc") as "Hc".
    rewrite /pipe_Wcl_at (pipe_inst_lcred g (S gen_id) I 3%nat).
    iDestruct "Hc" as (v') "[#Hpin' Hc]".
    iDestruct (era_pin_agree with "Hpin' Hpin") as %->.
    cbn [gwc_lpr] in *.
    iMod (blk2_inv_alloc_at ⊤ v I L gL gR gM (pl_XL pn) (pl_YR pn L)
            Hline with "HgL1 HgR1 HgM1 [Hc]") as "#Hinv".
    { iApply (PipeLinksLine.pwc_lend_of_blk0 g (S gen_id) v I 0%nat
                with "Hc"). }
    iModIntro. rewrite /pl_Cr. by iFrame "Hinv HgL2 HgR2 HgM2".
  Qed.

  (* =================================================================== *)
  (*  S2b''  THE FOUR-WAY SPLIT (ROUND-11's table, rows RcL/RcR/Rk/Cx)    *)
  (*                                                                     *)
  (*  What the arm's own split hands the three parties.  The family's     *)
  (*  invariant is PERSISTENT, so all three get it; the LEFT cursor half  *)
  (*  rides inside echo's own lend (that is what [UEchoPipe.ep_frame]'s   *)
  (*  [Wq] slot is for at a pipeline round -- design SS4.3r item 4 puts   *)
  (*  [emp] in the registrar's and the split puts the half in); the RIGHT *)
  (*  and MODE halves, the reader's permit and the right side token go to *)
  (*  cat; the parent keeps the protocol's handle and the [fork1] tails   *)
  (*  get nothing of their own ([Cx := emp], SS4.3u).                      *)
  (* =================================================================== *)
  Definition pl_RcL (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) (γp : pipe_names) : iProp Σ :=
    (PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM
       (pl_XL pn) (pl_YR pn L)
     ∗ UEchoPipe.ep_pay (PipeBoth.wcur gL (1/2) 0%nat) pn γp L)%I.

  (* THE RIGHT CHILD WILL ALSO NEED THE PROTOCOL'S HANDLE IN HERE (lane
     SH-PIPE-ROUND-13, measured): [UShPipeCatRound.pipe_cat_w] fires the
     family's MODE and the fire's exclusion witness
     [box (XL -* YR ={pipeN}=* False)] comes off
     [PipeProto.pipe_excl_wtok_lb_pipeN] at [pipe_inv pn gp L] -- and [gp]
     is bound by the WALK's own continuation, so the handle cannot be
     framed in from outside.  It is PERSISTENT, so adding it costs
     [pl_split] nothing (the parent keeps its own copy) and no other row
     moves.  TAKEN (lane SH-PIPE-ROUND-14): [pl_cat_kround] below spends
     it at exactly that place, and at [UShPipeCatRound.pipe_cat_w]'s
     [Hex]. *)
  Definition pl_RcR (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) (γp : pipe_names) : iProp Σ :=
    (PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM
       (pl_XL pn) (pl_YR pn L)
     ∗ PipeProto.pipe_inv pn γp L
     ∗ rtok pn ∗ PipeProto.side_R pn
     ∗ PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)%I.

  Lemma pl_split (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) (γp : pipe_names) :
    pl_Cr v I L pn gL gR gM -∗
    UShPipeAssembly.pipe_reg_pay pn emp%I L γp -∗
    pl_RcL v I L pn gL gR gM γp
    ∗ (pl_RcR v I L pn gL gR gM γp
       ∗ (PipeProto.pipe_inv pn γp L ∗ emp)).
  Proof using .
    rewrite /pl_Cr /UShPipeAssembly.pipe_reg_pay /pl_RcL /pl_RcR
            /UEchoPipe.ep_pay /UEchoPipe.ep_frame.
    iIntros "(#Hinv & HgL & HgR & HgM) (Hr & HsR & (#Hpi & [HsL _] & Hw & Hlb))".
    iSplitL "HgL HsL Hw Hlb".
    { iFrame "Hinv Hpi HsL HgL Hw Hlb". }
    iSplitL "HgR HgM Hr HsR".
    { iFrame "Hinv Hpi Hr HsR HgR HgM". }
    iSplitR; [ iExact "Hpi" | done ].
  Qed.

  (* =================================================================== *)
  (*  S2b'''  THE TWO LAWS THE WALK TAKES, AT THE ROUND'S CREDENTIALS     *)
  (*                                                                     *)
  (*  Both are read OFF the credential they are paid with, through        *)
  (*  [UShPipeAssembly.exf_law_acc]: the family's invariant is born out   *)
  (*  of the lend and so is not in hand when the law is handed to the     *)
  (*  walk (ROUND-11 finding (5)).  Everything below is pinned at         *)
  (*  [UexecExecInst.uprogSG_free] -- the instance the child law's walk   *)
  (*  runs at ([UShPipeRound.sh_pipe_child_law]) -- because this file     *)
  (*  binds no [uprogSG] section variable, exactly as [UShPipeRound.v]    *)
  (*  pins it.                                                            *)
  (* =================================================================== *)

  (* the [pipe(2)]-failed tail's *)
  Lemma pl_panic_pipe_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (pn : pnames) (gL gR gM : gname) :
    PipeHooks.pline_at I = PipeDisc.LPipe ws ->
    PipeLinks.pipe_links g -∗
    era_pin γ (S gen_id) v -∗
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (wl_line PipeDisc.dg_pipe) 5%nat
      (pl_Cr v I L pn gL gR gM) (pipe_Wcl_at g I 0%nat).
  Proof using .
    intros Hline. iIntros "#Hlk #Hpin".
    iApply (UShPipeAssembly.exf_law_acc (PS := uprogSG_free)
              (wl_line PipeDisc.dg_pipe) 5%nat
              (pl_Cr v I L pn gL gR gM)
              (PipeBoth.wcur gL (1/2) 0%nat ∗ PipeBoth.wcur gR (1/2) 0%nat)%I
              (pipe_Wcl_at g I 0%nat)).
    rewrite /pl_Cr.
    iIntros "!> (#Hinv & HgL & HgR & _)".
    iSplitR "HgL HgR"; [ | iFrame "HgL HgR" ].
    iApply (UShPipeAssembly.pipe_panic_pipe_law (PS := uprogSG_free)
              g v I L ws gL gR gM (pl_XL pn) (pl_YR pn L)
              (pl_XL_timeless pn) (pl_YR_timeless pn L) Hline
              with "Hlk Hpin Hinv").
  Qed.

  (* ...and the [panic("fork")] tails', taint and all (design SS4.3z item 3) *)
  Lemma pl_fork_panic_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (pn : pnames) (gL gR gM : gname)
      (γp : pipe_names) :
    PipeHooks.pline_at I = PipeDisc.LPipe ws ->
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    PipeLinks.pipe_links g -∗
    era_pin γ (S gen_id) v -∗
    (inp_lb v I ∨ T) -∗
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      EchoDisc.alt_panic 5%nat
      (pl_RcR v I L pn gL gR gM γp ∗ emp)
      (UkShPipeFork.pterm_shape g I 5%nat ∨ T).
  Proof using Hcons.
    intros Hline. iIntros "#Hdps #Hlk #Hpin #Hlb".
    iDestruct (PipeLinks.pipe_links_taint g with "Hlk") as "#Ht".
    iApply (UShPipeAssembly.exf_law_acc (PS := uprogSG_free)
              EchoDisc.alt_panic 5%nat
              (pl_RcR v I L pn gL gR gM γp ∗ emp)%I
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)%I
              (UkShPipeFork.pterm_shape g I 5%nat ∨ T)%I).
    rewrite /pl_RcR.
    iIntros "!> [(#Hinv & _ & _ & _ & HgR & HgM) _]".
    iSplitR "HgR HgM"; [ | iFrame "HgR HgM" ].
    iApply (UShPipeAssembly.pipe_fork_panic_law_or (PS := uprogSG_free)
              g Hcons v I L ws gL gR gM (pl_XL pn) (pl_YR pn L)
              (pl_XL_timeless pn) (pl_YR_timeless pn L) Hline
              with "Hdps Ht Hpin Hlb Hinv").
  Qed.

  (* ...AND THE PAYLOAD'S TAINT ARM, which is the walk's
     [box (app_taint -* Qc (-1))] *)
  Lemma pl_qc_of_taint (pn : pnames) (L : list (bv 8)) (gL gR gM : gname) :
    ⊢ app_taint -∗ UShPipeAssembly.pipe_Qc_at g pn L gL gR gM.
  Proof using Hkill.
    iIntros "#Ht". rewrite /UShPipeAssembly.pipe_Qc_at. iLeft.
    rewrite -Hkill. iExact "Ht".
  Qed.

  (* =================================================================== *)
  (*  S2c  THE FOUR PAYLOAD CONVERSIONS                                   *)
  (*                                                                     *)
  (*  The round's [Qc] is [UShPipeAssembly.pipe_Qc_at]; each of the four  *)
  (*  places a child can exit from has to reach it, and each is a         *)
  (*  different arm:                                                     *)
  (*                                                                     *)
  (*    echo ran        [UEchoPipe.ep_exit] -> the LEFT arm's first case  *)
  (*    echo's exec failed   the left cursor at 17 -> its second          *)
  (*    cat ran         cat's own [Cend] -> the RIGHT arm's first case    *)
  (*    cat's exec failed    the right cursor at 16 and the mode at 2     *)
  (*                                                                     *)
  (*  THE SIDE TOKENS ARE WHAT TELLS THE TWO APART at the reap            *)
  (*  ([PipeProto.pipe_Qc_two]), so each conversion carries the child's   *)
  (*  own: the left's out of [UEchoPipe.ep_frame] (inside [ep_pay], and   *)
  (*  on the failed arm FRAMED through the diagnostic --                  *)
  (*  [UShPipeAssembly.pipe_execL_law]'s [F]), the right's out of the     *)
  (*  registrar's answer.                                                 *)
  (* =================================================================== *)
  Lemma pl_qc_of_ep_exit (pn : pnames) (L : list (bv 8)) (gL gR gM : gname) :
    UEchoPipe.ep_exit (PipeBoth.wcur gL (1/2) 0%nat) pn L -∗
    UShPipeAssembly.pipe_Qc_at g pn L gL gR gM.
  Proof using Hkill.
    iIntros "He".
    iDestruct (UEchoPipe.ep_exit_payL (PipeBoth.wcur gL (1/2) 0%nat) pn L
                 with "He") as "(HsL & HgL & [Hpay | #Hta])".
    - rewrite /UShPipeAssembly.pipe_Qc_at. iRight.
      rewrite /PipeProto.pipe_Qc. iLeft. iFrame "HsL".
      rewrite /UShPipeAssembly.pipe_PL. iLeft. iFrame "Hpay HgL".
    - rewrite /UShPipeAssembly.pipe_Qc_at. iLeft. rewrite -Hkill.
      iExact "Hta".
  Qed.

  Lemma pl_qc_of_cdL (pn : pnames) (L : list (bv 8)) (gL gR gM : gname) :
    PipeBoth.wcur gL (1/2) 17%nat ∗ PipeProto.side_L pn -∗
    UShPipeAssembly.pipe_Qc_at g pn L gL gR gM.
  Proof using .
    iIntros "[HcL HsL]". rewrite /UShPipeAssembly.pipe_Qc_at. iRight.
    rewrite /PipeProto.pipe_Qc. iLeft. iFrame "HsL".
    rewrite /UShPipeAssembly.pipe_PL. iRight.
    rewrite dg_execL_len. iExact "HcL".
  Qed.

  Lemma pl_qc_of_cdR (pn : pnames) (L : list (bv 8)) (gL gR gM : gname) :
    PipeBoth.wcur gR (1/2) 16%nat ∗ PipeBoth.wcur gM (1/2) 2%nat
      ∗ PipeProto.side_R pn -∗
    UShPipeAssembly.pipe_Qc_at g pn L gL gR gM.
  Proof using .
    iIntros "(HcR & HcM & HsR)". rewrite /UShPipeAssembly.pipe_Qc_at. iRight.
    rewrite /PipeProto.pipe_Qc. iRight. iFrame "HsR".
    rewrite /UShPipeAssembly.pipe_PR. iRight.
    rewrite dg_execR_len. iFrame "HcR HcM".
  Qed.

  (* WHAT CAT'S ROUND HANDS BACK.  [UCatPipe.pcat_round_at_g]'s [Hend] is
     a PURE wand, so everything the payload needs has to be readable off
     the three things it is given -- the end-of-file shot, the reader's
     hold and the cursor family.  The READER'S PERMIT travels, because
     [UShPipeAssembly.pipe_PR] carries it rather than the cursor's BOUND:
     the bound is an invariant access and only the round's own reading is
     a fancy update ([UShPipeAssembly.pipe_rcur_bound]). *)
  Definition pl_Cend (pn : pnames) (L : list (bv 8)) (gR gM : gname)
      : iProp Σ :=
    (∃ c : nat, (eof_shot pn (take c L) ∨ T)
       ∗ (PipeProto.rcur pn c ∨ T)
       ∗ UShPipeCatRound.pcat_ch g gR gM c)%I.

  Lemma pl_qc_of_cend (pn : pnames) (L : list (bv 8)) (gL gR gM : gname) :
    pl_Cend pn L gR gM ∗ PipeProto.side_R pn -∗
    UShPipeAssembly.pipe_Qc_at g pn L gL gR gM.
  Proof using .
    iIntros "[Hce HsR]". iDestruct "Hce" as (c) "(Heof & Hrc & Hch)".
    rewrite /UShPipeAssembly.pipe_Qc_at
            /UShPipeCatRound.pcat_ch.
    iDestruct "Hch" as "[[HcR HcM] | #HT]"; [ | by iLeft ].
    iDestruct "Heof" as "[#Heof | #HT]"; [ | by iLeft ].
    iRight. rewrite /PipeProto.pipe_Qc. iRight. iFrame "HsR".
    rewrite /UShPipeAssembly.pipe_PR. iLeft. iExists c.
    iFrame "Hrc Heof HcR HcM".
  Qed.

  (* =================================================================== *)
  (*  S2d2  CAT'S ROUND AT THE FAMILY'S RIGHT CHAIN (lane                 *)
  (*        SH-PIPE-ROUND-14; SH-PIPE-ROUND-13 wrote the text).           *)
  (*                                                                     *)
  (*  What stopped ROUND-13 was ONE unification and it was not the one    *)
  (*  design SS4.3ab guessed: [UShPipeCatRound.v] bound neither           *)
  (*  [ghost_varG Sigma Z] nor [ghost_varG Sigma (gset gname)], so        *)
  (*  [UkCat.kcat_wr]'s two [ghost_var] classes were resolved through the *)
  (*  [xv6G] bundle and BAKED IN, while [UCatPipe.v] binds both as        *)
  (*  section variables and THIS file binds [ghost_varG Sigma Z] itself.  *)
  (*  [uexecSG] was the same term on both sides all along.                *)
  (* =================================================================== *)

  (* THE RIGHT CHILD'S TWO ROWS.  [UkShCat.ush_fd0p] says fd 0 is this
     pipe's read end -- what [UCatPipe.pcat_round_at_g] reads -- and cat
     also WRITES: [UShPipeCatRound.pipe_cat_w] needs fd 1 to be the
     console, which [ush_fd0p] alone does not say.  [Fd0] is a parameter
     of both [UkShCat.wp_kshr_exec_cat_at] and
     [UShCatPay.sh_exec_sup_cat_wq_holds_at], so the conjunction is free. *)
  Definition pl_cat_fd0 (gp : pipe_names) (l : list fdstate) : Prop :=
    UkShCat.ush_fd0p gp l
    /\ exists rb : bool,
         l !! 1%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)).

  (* ...AND CAT'S TWO DIAGNOSTIC TAILS, OUT OF THE TAINT.
     [UCatPipe.pcat_round_at_g]'s [Hdg] and [Hdgw] had NO producer
     anywhere in the tree.  Both are [UkCat.kcat_pay_seq]s (16 and 17
     bytes) and [UkCat.kcat_pay_seq_of_law] builds either out of the
     era's FREE WRITE LAW and a BOXED [-1] payload -- which is exactly
     what a tainted pipeline round has: [UkSh.sh_deps] IS [udepw_law 16]
     and the payload's taint arm is [pl_qc_of_taint]. *)
  Lemma pl_kcat_dg (N' : uk_names Σ) `{!ukn_const N'} :
    □ (ukn_pay N' (-1)) -∗ UkSh.sh_deps (PS := uprogSG_free) -∗
    UkCatCat.kcat_dg_cr (PS := uprogSG_free) N'
    ∗ UkCatCat.kcat_dg_cw (PS := uprogSG_free) N'.
  Proof using .
    iIntros "#HC #Hwr". rewrite /UkSh.sh_deps.
    rewrite /UkCatCat.kcat_dg_cr /UkCatCat.kcat_dg_cw.
    iAssert (□ UkCat.kcat_exit (PS := uprogSG_free) N' 1)%I as "#HC1".
    { iModIntro. iApply (UkCat.kcat_exit_of_pay with "HC"). }
    iSplitL.
    - iApply (UkCat.kcat_pay_seq_of_law (PS := uprogSG_free) N'
                _ _ 16%nat (UkCat.kcat_exit (PS := uprogSG_free) N' 1)
                0%nat with "HC1 Hwr").
    - iApply (UkCat.kcat_pay_seq_of_law (PS := uprogSG_free) N'
                _ _ 17%nat (UkCat.kcat_exit (PS := uprogSG_free) N' 1)
                0%nat with "HC1 Hwr").
  Qed.
End UShPipeLawRes.
