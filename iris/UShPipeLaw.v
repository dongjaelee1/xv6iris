(* ===================================================================== *)
(*  UShPipeLaw.v -- [UShPipeRound.sh_pipe_child_law] DISCHARGED           *)
(*  (lane SH-PIPE-ROUND-11; design claude-notes/design/app-pipe.md        *)
(*  SS4.3y, items 2 and 3).                                              *)
(*                                                                       *)
(*  The pipeline application's whole-system theorem has had ONE premise   *)
(*  since lane PIPE-CC: sh's PIPE-arm child walk, as a law               *)
(*  ([UShPipeRound.sh_pipe_child_law]).  Everything the law needs has     *)
(*  been landed by ROUND-8..ROUND-10 and the four purchases of SS4.3w..y; *)
(*  this file is the ASSEMBLY, and it is a NEW file because the law's     *)
(*  definition ([UShPipeRound.v]), the walk ([UShPipeChild.v]), the       *)
(*  round's leaves ([UShPipeAssembly.v]), cat's write                     *)
(*  ([UShPipeCatRound.v]) and the two exec supplies ([UShEchoPipePay.v],  *)
(*  [UShCatPay.v]) are five SIBLINGS -- none of them is above the others, *)
(*  so no landed file can see them all.                                  *)
(*                                                                       *)
(*  THE SHAPE OF THE ASSEMBLY, in the order the walk consumes it.         *)
(*                                                                       *)
(*   (1) THE NAMES, BEFORE THE WALK.  [PipeProto]'s [pnames] and the      *)
(*       family's three cursors [gL]/[gR]/[gM] are allocated at the law's *)
(*       own [mWP] entry, because the round's payload [Qc] NAMES them     *)
(*       ([UShPipeAssembly.pipe_Qc_at]) and [Qc] is fixed before the      *)
(*       walk starts.  The era pin [v] comes off the law's third          *)
(*       antecedent.  What the fupd [Cp ={⊤}=∗ Cr] then does is allocate  *)
(*       the family's INVARIANT alone ([blk2_inv_alloc_at] below), which  *)
(*       is why [Cr] carries it: the two diagnostic laws and the split    *)
(*       read [blk2_inv] out of the credential they consume.              *)
(*   (2) THE FOUR-WAY SPLIT.  [Cr] is the three cursor halves and the     *)
(*       invariant; [R gp] is the registrar's answer.  The left child     *)
(*       gets echo's own lend with the LEFT cursor half inside it         *)
(*       ([UShPipeRound2.ep_pay_frame] is the join), the right child the  *)
(*       reader's permit, the right side token and the right and mode     *)
(*       halves, the parent the protocol's invariant, and the [fork1]     *)
(*       tails nothing of their own ([Cx := emp], SS4.3u).                *)
(*   (3) THE FIVE LAWS and the two exec supplies, each one application.   *)
(*   (4) THE PARENT at 0xea: [UShPipeAssembly.pipe_round_parent], whose   *)
(*       [S1 <> S2] premise is now supplied by SS4.3y's relay             *)
(*       ([ush_fork_ans_sets_differ]).                                    *)
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
Require Import PipeLinkInst.
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
Require Import UShCatPay.
Require Import UShEchoPipePay.
Require Import UShPipeChild.
Require Import UShPipeRound.
Require Import UShPipeRound2.
Require Import UShPipeAssembly.
Require Import UShPipeCatRound.
Require Import CtxIdDefs.
Require User.ShSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S1  THE PURE BRIDGE: THE LOOP'S WORD LIST NAMES THE PIPELINE LINE    *)
(*                                                                       *)
(*  [FileDisc.fline_ok_redir_words] one constructor over.  The child law  *)
(*  hands its prover [ws = last_ws I], [FileDisc.fline_ok                 *)
(*  (UkSh.ush_lastbody I)] and [UShPipeRound.ushq_lp ws g 0 len] -- the   *)
(*  last of which says [ws = ws' ++ [bar; cat]] -- and every lemma the    *)
(*  round is built out of is stated at [PipeLinksLine.pline_at I = LPipe  *)
(*  ws'].  The other three constructors are refuted by their words,       *)
(*  exactly as the redirect line's twin refutes them: an echo line's are  *)
(*  all alphanumeric and the bar is not, a redirect's last but one is     *)
(*  `>', and [cat f] has two words while a pipeline's are a command's     *)
(*  plus two.                                                            *)
(* ===================================================================== *)
Lemma fline_ok_pipe_words (b : list (bv 8)) (ws : list (list (bv 8))) :
  FileDisc.fline_ok b -> EchoDisc.line_ok ws ->
  wl_words b = ws ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat] ->
  b = FileDisc.line_body (FileDisc.LPipe ws).
Proof using.
  intros (l & Hok & ->) Hws Hw.
  destruct l as [ws' | ws' | | ws'].
  - (* LEcho: its words are alphanumeric, and the bar is not *)
    exfalso. cbn [FileDisc.line_body] in Hw.
    rewrite (wl_words_body ws' (line_ok_wf _ Hok)) in Hw.
    pose proof (line_ok_wf _ Hok) as Hwf. rewrite Hw in Hwf.
    apply Forall_app in Hwf as [_ Hwf].
    apply Forall_cons_1 in Hwf as [[_ Hbar] _].
    apply Forall_cons_1 in Hbar as [Hbar _].
    revert Hbar. rewrite /wl_alnum. vm_compute. intros [H | [H | H]];
      destruct H as [H1 H2]; first [ by apply H1 | by apply H2 ].
  - (* LEchoF: the two suffixes line up and `>' is not the bar *)
    exfalso. destruct Hok as [Hok' Hlen].
    rewrite (FileDisc.uline_ws_gtf ws' Hok') in Hw. cbn [FileDisc.uline_ws] in Hw.
    replace (ws' ++ [FileDisc.fd_w_gt; FileDisc.fname_f])
      with ((ws' ++ [FileDisc.fd_w_gt]) ++ [FileDisc.fname_f]) in Hw
      by (rewrite -app_assoc; reflexivity).
    replace (ws ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat])
      with ((ws ++ [FileDisc.fd_w_bar]) ++ [FileDisc.fd_w_cat]) in Hw
      by (rewrite -app_assoc; reflexivity).
    apply app_inj_tail in Hw as [Hw _].
    apply app_inj_tail in Hw as [_ Hgt]. discriminate Hgt.
  - (* LCat: two words, so the command would have none *)
    exfalso. cbn [FileDisc.line_body] in Hw.
    apply (f_equal length) in Hw. rewrite length_app in Hw.
    pose proof (line_ok_pos ws Hws) as Hp.
    revert Hw. vm_compute (length (wl_words FileDisc.cmd_cat_f)).
    cbn [length]. lia.
  - (* LPipe: the words determine the command *)
    destruct Hok as [Hok' Hlen].
    rewrite (FileDisc.uline_ws_pipe ws' Hok') in Hw.
    cbn [FileDisc.uline_ws] in Hw.
    replace (ws' ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat])
      with ((ws' ++ [FileDisc.fd_w_bar]) ++ [FileDisc.fd_w_cat]) in Hw
      by (rewrite -app_assoc; reflexivity).
    replace (ws ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat])
      with ((ws ++ [FileDisc.fd_w_bar]) ++ [FileDisc.fd_w_cat]) in Hw
      by (rewrite -app_assoc; reflexivity).
    apply app_inj_tail in Hw as [Hw _].
    apply app_inj_tail in Hw as [-> _]. reflexivity.
Qed.

(* ...AND THE READING THE ROUND TAKES: the input's last line IS the
   pipeline line of the loop's own word list. *)
Lemma pline_at_of_lp (I : list (bv 8)) (wsf ws : list (list (bv 8))) :
  wsf = last_ws I ->
  FileDisc.fline_ok (UkSh.ush_lastbody I) ->
  wsf = ws ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat] ->
  PipeDisc.pline_ok (PipeDisc.LPipe ws) ->
  PipeLinksLine.pline_at I = PipeDisc.LPipe ws.
Proof using.
  intros Hwsf Hfb Hcut Hpok.
  assert (Hlast : last_ws I = wl_words (UkSh.ush_lastbody I))
    by (rewrite /UkSh.ush_lastbody; exact (last_ws_lastbody I)).
  assert (Hw : wl_words (UkSh.ush_lastbody I)
               = ws ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat])
    by (rewrite -Hlast -Hwsf; exact Hcut).
  pose proof (fline_ok_pipe_words (UkSh.ush_lastbody I) ws Hfb
                (proj1 Hpok) Hw) as Hbody.
  rewrite /PipeLinksLine.pline_at -/(UkSh.ush_lastbody I) Hbody.
  rewrite (PipeUline.line_body_of_pline (PipeDisc.LPipe ws)).
  exact (PipeDisc.pline_of_body (PipeDisc.LPipe ws) Hpok).
Qed.

(* ===================================================================== *)
(*  S2  THE ROUND'S RESOURCES, AND THE FOUR PAYLOAD CONVERSIONS           *)
(* ===================================================================== *)
Section UShPipeLaw.
  (* [UShPipeRound.v]'s binder list VERBATIM (the file whose law this
     discharges), PLUS [pipeProtoG] for the protocol's own ghosts -- which
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
  (*  S2b  THE INPUT'S LOWER BOUND, off the credential the fork lends     *)
  (*                                                                     *)
  (*  [UInitPipe]'s [pwc_blk_inp] (a [Local Lemma] one file ABOVE this    *)
  (*  one, so it cannot be named), at the ONE index the round needs:      *)
  (*  [PipeBoth.pwc_lpr2 g k v I 3] IS [pwc_blk g k v I 0 0].  What it    *)
  (*  buys is [EchoOut.inp_lb v I], which [UShPipeAssembly.               *)
  (*  pipe_fork_panic_law] needs to build design SS4.3h's terminal        *)
  (*  payload ([UkShPipeFork.pterm_shape]'s second conjunct) -- and the   *)
  (*  TAINT arm is the credential's own, not an artefact of this reading. *)
  (* =================================================================== *)
  Local Lemma pwc_blk_inp (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) :
    PipeLinksLine.pwc_blk g k v I a i -∗
    PipeLinksLine.pwc_blk g k v I a i ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite /PipeLinksLine.pwc_blk. iIntros "[Hl | #HT]"; last first.
    { iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Ht & #Hps & #Hcs & #HE)".
    iSplitL "Ht".
    - iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE". by iPureIntro.
    - iLeft. iExact "HE".
  Qed.

  Lemma pipe_wcl3_inp (I : list (bv 8)) :
    ⊢ pipe_Wcl_at g I 3%nat -∗
      pipe_Wcl_at g I 3%nat
      ∗ ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I) ∨ T).
  Proof using .
    rewrite /pipe_Wcl_at (pipe_inst_lcred g (S gen_id) I 3%nat).
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    cbn [PipeBoth.pwc_lpr2] in *.
    iDestruct (pwc_blk_inp (S gen_id) v I 0%nat 0%nat with "Hc") as "[Hc Hi]".
    iSplitL "Hc"; [ iExists v; iFrame "Hpin Hc" | ].
    iDestruct "Hi" as "[HE | HT]";
      [ iLeft; iExists v; iFrame "Hpin HE" | iRight; iExact "HT" ].
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
    cbn [PipeBoth.pwc_lpr2] in *.
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

  Definition pl_RcR (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) (γp : pipe_names) : iProp Σ :=
    (PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM
       (pl_XL pn) (pl_YR pn L)
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
    { iFrame "Hinv Hr HsR HgR HgM". }
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
    PipeLinksLine.pline_at I = PipeDisc.LPipe ws ->
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
    PipeLinksLine.pline_at I = PipeDisc.LPipe ws ->
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
    iIntros "!> [(#Hinv & _ & _ & HgR & HgM) _]".
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

End UShPipeLaw.


(* =================================================================== *)
(*  S2d  THE LEFT CHILD'S ARGV BYTES                                    *)
(*                                                                     *)
(*  [UkShEcho.wp_kshr_exec_echo_at]'s one reading of the node sh built, *)
(*  and it is NOT the echo era's ([UkShEcho.                            *)
(*  echo_argv_bytes_of_line_holds], stated at [UConsLine.ush_line_is ws *)
(*  f 0 len] -- a line whose bytes ARE [wl_line ws]).  A pipeline       *)
(*  round's line has [" | cat"] glued on and its cut has ONE MORE       *)
(*  [ushp_nulfold] layer (the right command's token), so neither the    *)
(*  premise nor the function is the mould's.  What makes it the same    *)
(*  proof anyway is that every index the predicate looks at is inside   *)
(*  the line's BODY, where the two lines agree byte for byte, and the   *)
(*  outer fold's ONLY nul is at [ge] -- above every word's end.         *)
(* =================================================================== *)
Lemma pl_echo_argv_bytes (ws : list (list (bv 8))) (f : nat -> bv 8)
    (len ge : nat) :
  UkShPipeRound.ushq_line_at ws f 0%nat len ->
  (length (wl_body ws) < ge)%nat ->
  UkShEcho.echo_argv_bytes ws
    (UkShPipeRound.ushq_cut (wl_toks ws) len f ge).
Proof using .
  intros (Hok & Hlen & Hby) Hge.
  assert (Hblen : (length (wl_body ws) < len)%nat).
  { rewrite Hlen /PipeDisc.line_bytes /PipeDisc.line_body !length_app.
    cbn [length]. lia. }
  (* below the bar the pipeline line's bytes ARE the echo line's *)
  assert (Hlo : forall j : nat, (j < length (wl_body ws))%nat ->
                  f j = wl_line ws !!! j).
  { intros j Hj.
    pose proof (Hby j ltac:(lia)) as Hfj.
    rewrite Nat.add_0_l in Hfj. rewrite Hfj.
    rewrite /PipeDisc.line_bytes /PipeDisc.line_body -app_assoc.
    rewrite (wl_lta_app_l (wl_body ws) _ j Hj).
    rewrite /wl_line (wl_lta_app_l (wl_body ws) [wl_nl] j Hj).
    reflexivity. }
  split.
  - intros i j Hi Hj.
    destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
    assert (Hwi : ws !!! i = w)
      by (rewrite list_lookup_total_alt Hw; reflexivity).
    rewrite /UkShEcho.echo_alen Hwi in Hj.
    rewrite /UkShEcho.echo_off.
    pose proof (wl_off_le_body ws 0%nat i w (length w) Hw
                  ltac:(lia)) as Hle.
    assert (Hlt : (wl_off 0%nat ws i + j < length (wl_body ws))%nat)
      by lia.
    rewrite (UkShPipeRound.ushq_cut_off (wl_toks ws) len f ge
               (wl_off 0%nat ws i + j)%nat ltac:(lia)).
    rewrite (wl_cut_in ws f len i w j Hw Hj ltac:(lia)).
    exact (Hlo _ Hlt).
  - intros i Hi.
    destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
    assert (Hwi : ws !!! i = w)
      by (rewrite list_lookup_total_alt Hw; reflexivity).
    rewrite /UkShEcho.echo_off /UkShEcho.echo_alen Hwi.
    pose proof (wl_off_le_body ws 0%nat i w (length w) Hw
                  ltac:(lia)) as Hle.
    rewrite (UkShPipeRound.ushq_cut_off (wl_toks ws) len f ge
               (wl_off 0%nat ws i + length w)%nat ltac:(lia)).
    exact (wl_cut_end ws f len i w Hw).
Qed.

(* ...and the two one-liners every lemma of the round also asks for *)
Lemma pboth_line_of_at (I : list (bv 8)) (ws : list (list (bv 8))) :
  PipeLinksLine.pline_at I = PipeDisc.LPipe ws -> pboth_line I.
Proof using . intro H. by exists ws. Qed.

Lemma pl_L_pos (ws : list (list (bv 8))) :
  (0 < length (wl_line (drop 1 ws)))%nat.
Proof using . rewrite /wl_line length_app. cbn [length]. lia. Qed.

(* ===================================================================== *)
(*  S3  THE VACUITY CHECK THE ASSEMBLY RAN INTO (lane SH-PIPE-ROUND-12).  *)
(*                                                                       *)
(*  [UShPipeChild.wp_kshm_child_pipe_paid_line_at] -- and the free twin   *)
(*  [UkShPipeRound.wp_kshm_child_pipe] it is built on -- asks for         *)
(*  [usz γs szv] AND for [UM0] at the SAME time, with [UM0] the           *)
(*  allocator state the parse's three [malloc]s are funded from.  Every   *)
(*  allocator state in the tree ([UkShMalloc.ushm_fresh],                 *)
(*  [UkShMalloc.ushm_one]) CARRIES [usz γs _], and so does [urun]         *)
(*  ([UserHeap.uheap]'s [ghost_var γs (1/2) sz]).  Three halves of one    *)
(*  [ghost_var] is [False], so the premise list cannot be met at any real *)
(*  allocator state -- which is why the [usz] must come OUT of the        *)
(*  parse's own leftover [UM3] and not be held beside [UM0].              *)
(* ===================================================================== *)
Section PipeChildSzScratch.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Lemma usz_three_absurd (γs : gname) (a b c : Z) :
    usz γs a -∗ usz γs b -∗ usz γs c -∗ False.
  Proof using .
    rewrite /usz. iIntros "H1 H2 H3".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[_ <-].
    iCombine "H1 H2" as "H".
    iDestruct (ghost_var_valid_2 with "H H3") as %[Hv _].
    iPureIntro. by apply (Qp.not_add_le_l _ _ Hv).
  Qed.

  Lemma pipe_paid_entry_absurd (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (sz szv : Z) :
    UkShMalloc.ushm_fresh N sz -∗ usz (ukn_s N) szv -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h m pc avail -∗ False.
  Proof using .
    iIntros "HM Hsz Hrun".
    rewrite /UkShMalloc.ushm_fresh. iDestruct "HM" as "(_ & _ & Hsz0)".
    rewrite /urun.
    iDestruct "Hrun" as (xi C pt Rfd Rut sz' M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hheap & _)".
    rewrite /uheap.
    iDestruct "Hheap" as (Mt Md Mslack)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & Hg & _)".
    iApply (usz_three_absurd (ukn_s N) sz szv sz' with "Hsz0 Hsz Hg").
  Qed.

End PipeChildSzScratch.
