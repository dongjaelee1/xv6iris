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

(* ===================================================================== *)
(*  S2d'  ...AND THE RIGHT COMMAND'S (lane SH-PIPE-ROUND-12).             *)
(*                                                                       *)
(*  [pl_echo_argv_bytes]'s twin at the ` | cat' tail, which                *)
(*  [UkShCat.wp_kshr_exec_cat_at_holds] takes and which NOTHING in the     *)
(*  tree proved: [UkShPipeLex.ushq_cat] is the WORD and                    *)
(*  [UkShPipeRound.ushq_cut_ok_right] is about the NODE.  Every index it   *)
(*  looks at sits ABOVE every token of [wl_toks ws] (so the parser's       *)
(*  nul-fold misses it) and BELOW the cut's own nul (so the outer fold     *)
(*  misses it too), which makes the cut the LINE there -- and the line's   *)
(*  bytes at those three indices are [PipeDisc.suf_pipecat]'s last three.  *)
(* ===================================================================== *)
Lemma pl_cat_argv_bytes (ws : list (list (bv 8))) (f : nat -> bv 8)
    (len : nat) :
  UkShPipeRound.ushq_line_at ws f 0%nat len ->
  UkShCat.cat_argv_bytes (length (wl_body ws) + 3)%nat
    (length (wl_body ws) + 3 + 3)%nat
    (UkShPipeRound.ushq_cut (wl_toks ws) len f
       (length (wl_body ws) + 3 + 3)%nat).
Proof using .
  intros Hline.
  pose proof Hline as (Hok & Hlen & Hby).
  pose proof (UkShPipeRound.ushq_line_is_of_at ws f 0%nat len Hline) as Hli.
  destruct (UkShPipeLex.ush_line_toks_holds_pipe ws UkShPipeLex.ushq_cat f
              0%nat len Hli) as (Hq & Ht & _ & _ & _).
  assert (Ef : (fun j : nat => f (0 + j)%nat) = f) by reflexivity.
  rewrite Ef in Hq, Ht.
  rewrite UkShPipeLex.ushq_cat_len in Hq.
  assert (Hlenv : len = (length (wl_body ws) + 7)%nat).
  { rewrite Hlen /PipeDisc.line_bytes /PipeDisc.line_body -app_assoc
            !length_app PipeDisc.suf_pipecat_len. cbn [length]. lia. }
  split_and!.
  - rewrite UkShCat.cmd_cat_len. reflexivity.
  - intros j Hj. rewrite UkShCat.cmd_cat_len in Hj.
    rewrite (UkShPipeRound.ushq_cut_off (wl_toks ws) len f
               (length (wl_body ws) + 3 + 3)%nat
               (length (wl_body ws) + 3 + j)%nat ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss (wl_toks ws)
               (UkShParseCmd.ushp_ext len f)
               (length (wl_body ws) + 3 + j)%nat
               ltac:(intros q t Hqt;
                     destruct (UkShPipeRound.ushq_args_below len f
                                 (length (wl_body ws) + 1)%nat
                                 (length (wl_body ws) + 3 + 3)%nat
                                 (wl_toks ws) Hq Ht q t Hqt) as [_ Hhi];
                     lia)).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((length (wl_body ws) + 3 + j) < len)%nat
         ltac:(lia)).
    pose proof (Hby (length (wl_body ws) + 3 + j)%nat ltac:(lia)) as Hfj.
    rewrite Nat.add_0_l in Hfj. rewrite Hfj.
    rewrite /PipeDisc.line_bytes /PipeDisc.line_body -app_assoc.
    rewrite !list_lookup_total_alt.
    rewrite (lookup_app_r (wl_body ws) (PipeDisc.suf_pipecat ++ [wl_nl])
               (length (wl_body ws) + 3 + j)%nat ltac:(lia)).
    replace (length (wl_body ws) + 3 + j - length (wl_body ws))%nat
      with (3 + j)%nat by lia.
    rewrite (lookup_app_l PipeDisc.suf_pipecat [wl_nl] (3 + j)%nat
               ltac:(rewrite PipeDisc.suf_pipecat_len; lia)).
    rewrite /UkShCat.cmd_cat.
    destruct j as [| [| [| j]]];
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | exfalso; lia ].
  - rewrite /UkShPipeRound.ushq_cut.
    cbn [UkShParseCmd.ushp_nulfold snd].
    rewrite /UkShParseCmd.ushp_setb Nat.eqb_refl. reflexivity.
Qed.

(* ...and the two one-liners every lemma of the round also asks for *)
Lemma pboth_line_of_at (I : list (bv 8)) (ws : list (list (bv 8))) :
  PipeLinksLine.pline_at I = PipeDisc.LPipe ws -> pboth_line I.
Proof using . intro H. by exists ws. Qed.

Lemma pl_L_pos (ws : list (list (bv 8))) :
  (0 < length (wl_line (drop 1 ws)))%nat.
Proof using . rewrite /wl_line length_app. cbn [length]. lia. Qed.

(* ...AND THE LEDGER FACT THE REGISTRAR ASKS FOR (lane SH-PIPE-ROUND-14).
   [pl_pipe_call]'s [fd_lowest_closed l = None] is not among the child
   law's premises and it does not have to be: [UserFd.ustd] carries
   [length l = NSTD] and the law's three rows are rows 0, 1 and 2, so the
   whole of the tracked ledger is open. *)
Lemma pl_fd_lowest_none (l : list fdstate) :
  length l = NSTD ->
  UkSh.ush_fd0c l -> UkSh.ush_fd1p l -> UkSh.ush_fd2p l ->
  fd_lowest_closed l = None.
Proof using.
  intros Hlen [wr0 H0] [rb1 H1] [rb2 H2].
  destruct l as [| a [| b [| c [| d tl]]]];
    try (exfalso; cbn in Hlen; unfold NSTD in Hlen; lia).
  cbn in H0, H1, H2.
  injection H0 as ->. injection H1 as ->. injection H2 as ->.
  reflexivity.
Qed.


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
    rewrite pwc_blk_view. iIntros "[Hl | #HT]"; last first.
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
    cbn [gwc_lpr] in *.
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
  (*  S2b''''  THE REGISTRAR, AND THE PREMISE THE ROUND CANNOT PAY        *)
  (*                                                                     *)
  (*  ROUND-11's table row [R] is [UShPipeAssembly.pipe_reg_pay pn emp L] *)
  (*  and its supplier [ush_pipe_call_pipe_pay].  ROUND-12 found that it  *)
  (*  took ONE premise the table never counted -- [UkRun.udepw_law 21],   *)
  (*  the CLOSE law, which is what the answer's two [UkShPipe.ush_cldep]  *)
  (*  rows were built from -- and that at [uprogSG_free] the law has NO   *)
  (*  producer but the taint.  SS4.3aa's ROW-AWARE close deposit closes   *)
  (*  that gap at the source: [UkRun.udepw_cl]'s right arm now pins the   *)
  (*  table's argument-0 row, so the two rows are paid by the very        *)
  (*  registration the call hands back ([UShPipeCall.                     *)
  (*  ush_pipe_call_paid_reg]) and this lemma has NO antecedent left.     *)
  (* =================================================================== *)
  Lemma pl_pipe_call (N : uk_names Σ) `{!ukn_const N} (pn : pnames)
      (l : list fdstate) (L : list (bv 8)) :
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    fd_lowest_closed l = None ->
    UShPipeAssembly.pipe_pre pn -∗ wtok pn -∗ PipeProto.side_L pn -∗
    rtok pn -∗ PipeProto.side_R pn -∗
    UkShPipe.ush_pipe_call (SG := uexecSG_xv6) (PS := uprogSG_free) N l
      (UShPipeAssembly.pipe_reg_pay pn emp%I L).
  Proof using .
    intros Hpsok Hnone.
    iIntros "Hpre Hw HsL Hr HsR".
    iApply (UShPipeAssembly.ush_pipe_call_pipe_pay_reg (PS := uprogSG_free)
              Hpsok N pn emp%I l L Hnone
              with "Hpre Hw HsL Hr HsR []").
    done.
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
  Lemma pl_kcat_dg (N' : uk_names Σ) :
    □ (ukn_pay N' (-1)) -∗ UkSh.sh_deps (PS := uprogSG_free) -∗
    UkCatCat.kcat_dg_cr (PS := uprogSG_free) N'
    ∗ UkCatCat.kcat_dg_cw (PS := uprogSG_free) N'.
  Proof using .
    iIntros "#HC #Hwr". rewrite /UkSh.sh_deps.
    rewrite /UkCatCat.kcat_dg_cr /UkCatCat.kcat_dg_cw.
    iSplitL.
    - iApply (UkCat.kcat_pay_seq_of_law (PS := uprogSG_free) N'
                _ _ 16%nat (ukn_pay N' (-1)) 0%nat with "HC Hwr").
    - iApply (UkCat.kcat_pay_seq_of_law (PS := uprogSG_free) N'
                _ _ 17%nat (ukn_pay N' (-1)) 0%nat with "HC Hwr").
  Qed.

  (* =================================================================== *)
  (*  ...AND THE ROUND ITSELF, which is what the right child's EXEC       *)
  (*  SUPPLY pays with ([UShCatPay.sh_exec_sup_cat_wq_holds_at]'s         *)
  (*  [Hround], quantified over the EXEC'D image's own record [N'']).     *)
  (*                                                                     *)
  (*  THE SIDE TOKEN MUST NOT RIDE IN THE CURSOR FAMILY.  [Hw] and        *)
  (*  [Hend] are both BOXED, but the third component of the answer -- the *)
  (*  wand [Cend -* ukn_pay N'' (-1)] -- is LINEAR and is built inside    *)
  (*  [Cr]'s own scope, so [PipeProto.side_R pn] is captured THERE        *)
  (*  ([pl_qc_of_cend]) and the family stays the bare cursor              *)
  (*  ([UShPipeCatRound.pcat_ch]).  Putting it in [Ch] needs a            *)
  (*  [UkCat.kcat_wr_mono] at every turn and is strictly worse.           *)
  (* =================================================================== *)
  Lemma pl_cat_kround (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (pn : pnames) (gL gR gM : gname)
      (gp : pipe_names) :
    PipeLinksLine.pline_at I = PipeDisc.LPipe ws ->
    L = wl_line (drop 1 ws) ->
    line_ok ws ->
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    PipeLinks.pipe_links g -∗
    era_pin γ (S gen_id) v -∗
    □ (∀ (N'' : uk_names Σ) (l : list fdstate),
         ⌜ukn_pay N''
          = (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)⌝ -∗
         ⌜pl_cat_fd0 gp l⌝ -∗
         UserFd.ustd (ukn_fd N'') l -∗
         pl_RcR v I L pn gL gR gM gp -∗
         ∃ Ir Cend : iProp Σ,
           UkCatCat.kcat_round (PS := uprogSG_free) N''
             (mword_of_int 0) Ir Cend
           ∗ Ir ∗ (Cend -∗ ukn_pay N'' (-1))).
  Proof using Hcons Hkill.
    intros Hpl HL Hok.
    assert (HLne : L <> []).
    { rewrite HL. intro Hq. pose proof (pl_L_pos ws) as Hp.
      rewrite Hq in Hp. cbn [length] in Hp. lia. }
    (* the line's bytes carry no '$' -- the right chain's own premise *)
    assert (Hwf1 : wl_wf (drop 1 ws)).
    { pose proof (line_ok_wf ws Hok) as Hwf.
      rewrite /wl_wf in Hwf |- *.
      apply Forall_lookup. intros i x Hx.
      rewrite lookup_drop in Hx.
      exact (Forall_lookup_1 _ _ _ _ Hwf Hx). }
    assert (Hnd : Forall LineBytes.nodollar L).
    { rewrite HL.
      exact (proj1 (PipeDisc.pd_wl_line_shape (drop 1 ws) Hwf1)). }
    (* the family's two witness obligations, [pipe_execR_law]'s verbatim *)
    assert (Hwit2 : forall sel : list bool,
               sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel)
      by (intros sel Hs; exact (PipeBoth.pblk2_wit_both I ws sel Hpl Hs)).
    assert (Hwit1 : forall sel : list bool,
               count_true sel = 0%nat -> (length sel <= length L)%nat ->
               pblk2_wit I L sel).
    { rewrite HL. intros sel Hc Hlen.
      exact (UShPipeAssembly.pblk2_wit_ran_at I ws sel Hpl Hc Hlen). }
    (* [UCatPipe.pcat_line] and [PipeLinksLine.pline_at] ARE the same term *)
    assert (Hout : UCatPipe.pcat_out I = L).
    { rewrite /UCatPipe.pcat_out.
      assert (Hcl : UCatPipe.pcat_line I = PipeDisc.LPipe ws) by exact Hpl.
      rewrite Hcl. cbn [PipeDisc.pline_ws]. by rewrite HL. }
    iIntros "#Hdps #Hlk #Hpin".
    iDestruct (PipeLinks.pipe_links_taint g with "Hlk") as "#Ht".
    iIntros "!>" (N'' l) "%Hpeq %Hfd0 Hstd Hcr".
    destruct Hfd0 as [[wb Hl0] [rb Hl1]].
    rewrite /pl_RcR.
    iDestruct "Hcr" as "(#Hinv & #Hpi & Hrt & HsR & HgR & HgM)".
    iDestruct (PipeProto.pipe_excl_wtok_lb_pipeN pn gp L HLne with "Hpi")
      as "#Hex".
    iAssert (UkCatCat.kcat_round (PS := uprogSG_free) N'' (mword_of_int 0)
               (UCatPipe.pcat_round_inv_g g N'' pn l
                  (UShPipeCatRound.pcat_ch g gR gM))
               (pl_Cend pn L gR gM))%I as "#Hround".
    { iApply (UCatPipe.pcat_round_at_g (PS := uprogSG_free) g Hcons Hkill
                N'' pn gp L l wb I
                (UShPipeCatRound.pcat_ch g gR gM) (pl_Cend pn L gR gM)
                Hout Hl0 with "Hpi [] [] [] []").
      - (* [Hdg]: cat's `read error' tail, off the taint *)
        iIntros "!> #HT".
        iAssert (□ (ukn_pay N'' (-1)))%I as "#HC".
        { iModIntro. rewrite Hpeq.
          iApply (pl_qc_of_taint pn L gL gR gM).
          rewrite Hkill. iExact "HT". }
        iPoseProof ("Hdps" with "HT") as "#Hwr".
        (* NAME the conjunct, do not FRAME it (lane SH-PIPE-ROUND-14): an
           [iDestruct ... as "[$ _]"] here sends the proofmode's [Frame]
           search into [UkCat.kcat_pay_seq], a sixteen-deep fixpoint, and
           it does NOT come back -- measured, [Set Default Timeout 300]
           fires on exactly this command and on nothing else in the file. *)
        iDestruct (pl_kcat_dg N'' with "HC Hwr") as "[Hcr _]".
        iExact "Hcr".
      - (* [Hdgw]: cat's `write error' tail AND the free write law *)
        iIntros "!> #HT".
        iAssert (□ (ukn_pay N'' (-1)))%I as "#HC".
        { iModIntro. rewrite Hpeq.
          iApply (pl_qc_of_taint pn L gL gR gM).
          rewrite Hkill. iExact "HT". }
        iPoseProof ("Hdps" with "HT") as "#Hwr".
        iDestruct (pl_kcat_dg N'' with "HC Hwr") as "[_ Hcw]".
        iSplitL "Hcw"; [ iExact "Hcw" | ].
        rewrite /UkSh.sh_deps. iExact "Hwr".
      - (* [Hw]: the turn's write, at the family's RIGHT chain, mode 1 *)
        iIntros "!>" (c nb rv fbb) "%Hrv %Hbytes Hjust Hstd2 Hc".
        destruct Hbytes as [Hcap Hlkp].
        iApply (UShPipeCatRound.pipe_cat_w (PS := uprogSG_free) g Hcons
                  N'' v I L gL gR gM (pl_XL pn) (pl_YR pn L) l rb
                  c nb rv fbb Hnd Hwit2 Hwit1 Hl1 Hrv Hcap
                  with "Hex Ht Hpin Hinv [Hjust] [] Hstd2 Hc").
        + (* the reader's bound, or the taint, or the EMPTY turn *)
          destruct (decide (Z.to_nat (bv_unsigned rv) = 0%nat))
            as [Hz | Hz].
          { iRight. iRight. by iPureIntro. }
          iDestruct "Hjust" as "[#Hlb | #HT]"; [ | iRight; by iLeft ].
          iLeft. rewrite /pl_YR.
          assert (E1 : take 1%nat L
                       = take 1%nat
                           (take (c + Z.to_nat (bv_unsigned rv))%nat L)).
          { rewrite take_take. f_equal.
            rewrite Nat.min_l; [ reflexivity | lia ]. }
          iApply (PipeProto.pws_lb_weaken pn
                    (take (c + Z.to_nat (bv_unsigned rv))%nat L)
                    (take 1%nat L)
                    ltac:(rewrite E1; eexists; symmetry; apply take_drop)
                    with "Hlb").
        + iLeft. iPureIntro. exact (conj Hcap Hlkp).
      - (* [Hend]: end of file, and what the round hands back *)
        iIntros "!>" (c) "Heof Hhold Hc".
        rewrite /pl_Cend /UCatPipe.pcat_hold.
        iDestruct "Hhold" as "[_ Hrc]".
        iExists c. iFrame "Heof Hrc Hc". }
    iExists (UCatPipe.pcat_round_inv_g g N'' pn l
               (UShPipeCatRound.pcat_ch g gR gM)),
            (pl_Cend pn L gR gM).
    iFrame "Hround".
    iSplitL "Hstd Hrt HgR HgM".
    - (* the round's invariant AT CURSOR 0 *)
      rewrite /UCatPipe.pcat_round_inv_g. iExists 0%nat.
      rewrite /UCatPipe.pcat_hold /UShPipeCatRound.pcat_ch.
      iFrame "Hstd".
      iSplitL "Hrt"; [ iLeft; iExact "Hrt" | ].
      iLeft. iFrame "HgR HgM".
    - (* ...AND THE EXIT, where the SIDE TOKEN is captured *)
      rewrite Hpeq. iIntros "Hce".
      iApply (pl_qc_of_cend pn L gL gR gM). iFrame "Hce HsR".
  Qed.

  (* =================================================================== *)
  (*  S2d3  THE RIGHT CHILD (ROUND-11's table, the `right child' row)     *)
  (*                                                                     *)
  (*  [pl_left_child]'s twin one command over: sh's SECOND [fork1] child  *)
  (*  runs [runcmd] on the pipeline line's RIGHT command (`cat') with fd  *)
  (*  0 the pipe's read end.  [UShCatPay.wp_kshr_exec_cat_paid] is the    *)
  (*  arm and its supply composed; [pl_cat_kround] is the entry's         *)
  (*  payment, [UShPipeAssembly.pipe_execR_law] at [F := side_R pn] read  *)
  (*  off [pl_RcR] through [exf_law_acc] is the exec-failed diagnostic,   *)
  (*  and [pl_cat_argv_bytes] its argv.                                   *)
  (* =================================================================== *)
  Lemma pl_right_child (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (pn : pnames) (gL gR gM : gname)
      (gp : pipe_names) (s0 szv : Z) (len : nat) (f : nat -> bv 8)
      (ld : list fdstate) (n : nat)
      (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (q : Z) :
    UkShPipeRound.ushq_line_at ws f 0%nat len ->
    L = wl_line (drop 1 ws) ->
    PipeLinksLine.pline_at I = PipeDisc.LPipe ws ->
    pl_cat_fd0 gp ld ->
    UkSh.ush_fd2p ld ->
    ukn_pay N' = (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM) ->
    m' !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int q : mword 64) ->
    UShCatPay.sh_cat_slot T -∗
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    era_pin γ (S gen_id) v -∗
    PipeLinks.pipe_links g -∗
    UCodeShK.shk_code (ukn_t N') -∗
    UkSh.ush_jtab (ukn_t N') -∗
    UkShRun.ush_cmd (ukn_d N') q
      (UkShRun.UExec (UkShMain.ush_args s0
         (UkShPipeRound.ushq_cut (wl_toks ws) len f
            (length (wl_body ws) + 3 + 3)%nat)
         [((length (wl_body ws) + 3)%nat,
           (length (wl_body ws) + 3 + 3)%nat)])) -∗
    usz (ukn_s N') szv -∗
    UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
    pl_RcR v I L pn gL gR gM gp -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m'
      (mword_of_int ShSyms.runcmd) (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hcons Hkill uartGhostG0.
    intros Hline HL Hpl Hfd0 Hfd2 Hpeq Ha0.
    assert (Hok : line_ok ws) by exact (proj1 (proj1 Hline)).
    assert (HLne : L <> []).
    { rewrite HL. intro Hq. pose proof (pl_L_pos ws) as Hp.
      rewrite Hq in Hp. cbn [length] in Hp. lia. }
    iIntros "#Hcat #Hdps #Hpin #Hlk #Hcode #Hjt #Htree Hsz Hstd Hcwd Hch
             Hcr Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iDestruct (PipeLinks.pipe_links_taint g with "Hlk") as "#Ht".
    (* ---- THE ENTRY'S PAYMENT: cat's round at fd 0 ---- *)
    iPoseProof (pl_cat_kround v I L ws pn gL gR gM gp Hpl HL Hok
                  with "Hdps Hlk Hpin") as "#Hround".
    (* ---- ...AND THE ARM.  The exec-failed law is a GOAL of this
       application and not an [iAssert]: it is stated at a
       [UkShDiag.ush_execfail_law_at] and an [iAssert ... as "#"] on one
       does not return in this cone (see [pl_exf_at_pers0]). ---- *)
    iApply (UShCatPay.wp_kshr_exec_cat_paid (PS := uprogSG_free)
              (pl_cat_fd0 gp)
              (length (wl_body ws) + 3)%nat
              (length (wl_body ws) + 3 + 3)%nat T
              (UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)
              (pl_RcR v I L pn gL gR gM gp)
              (PipeBoth.wcur gR (1/2) 16%nat ∗ PipeBoth.wcur gM (1/2) 2%nat
               ∗ PipeProto.side_R pn)%I
              N' Hc h' m' q szv s0
              (UkShPipeRound.ushq_cut (wl_toks ws) len f
                 (length (wl_body ws) + 3 + 3)%nat)
              ld n
              Hpeq Ha0 (pl_cat_argv_bytes ws f len Hline) Hfd0 Hfd2
              with "[] Hround Hcat [] Hcode [] [] Hjt Htree Hsz Hstd Hcwd
                    [Hch] Hcr Hrun").
    - iIntros "!> Ht2". iApply (pl_qc_of_taint pn L gL gR gM with "Ht2").
    - iApply (UexecExecMint.udep_free).
    - (* THE EXEC-FAILED LAW, read off the credential *)
      iApply (UShPipeAssembly.exf_law_acc (PS := uprogSG_free)
                PipeDisc.alt_execR 16%nat
                (pl_RcR v I L pn gL gR gM gp)
                (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat
                 ∗ PipeProto.side_R pn)%I
                (PipeBoth.wcur gR (1/2) 16%nat
                 ∗ PipeBoth.wcur gM (1/2) 2%nat
                 ∗ PipeProto.side_R pn)%I).
      rewrite /pl_RcR.
      iIntros "!> (#Hinv & #Hpi & _ & HsR & HgR & HgM)".
      iSplitR "HgR HgM HsR"; [ | iFrame "HgR HgM HsR" ].
      iApply (UShPipeAssembly.pipe_execR_law (PS := uprogSG_free)
                g Hcons v I L ws gL gR gM (pl_XL pn) (pl_YR pn L)
                (PipeProto.side_R pn)
                (pl_XL_timeless pn) (pl_YR_timeless pn L) Hpl HL
                with "[] Ht Hpin Hinv").
      iApply (PipeProto.pipe_excl_wtok_lb_pipeN pn gp L HLne with "Hpi").
    - iIntros "!> Hc2". iApply (pl_qc_of_cdR pn L gL gR gM with "Hc2").
    - iApply (UserChildren.uch_any_of (ukn_ch N') ∅ with "Hch").
  Qed.

  (* =================================================================== *)
  (*  S2e  THE LEFT CHILD (ROUND-11's table, the `left child' row)        *)
  (*                                                                     *)
  (*  The walk's LEFT continuation, discharged: sh's first [fork1] child  *)
  (*  runs [runcmd] on the pipeline line's LEFT command with fd 1 the     *)
  (*  pipe's write end.  [UkShEcho.wp_kshr_exec_echo_at_holds] is the     *)
  (*  arm, [UShEchoPipePay.sh_exec_sup_echo_pipe_at] its (W)/(E) supply   *)
  (*  and [UShPipeAssembly.pipe_execL_law] at [F := side_L pn] the        *)
  (*  exec-failed diagnostic -- the frame is there because the child's    *)
  (*  exit payload is [pipe_Qc_at]'s SIDE-TAGGED arm while the arm's own  *)
  (*  [box (Cd -* Q (-1))] is BOXED and cannot capture a linear token.    *)
  (*  The law is read off [pl_RcL] through [exf_law_acc], and the         *)
  (*  exclusion witness the family's steps need comes off the protocol's  *)
  (*  own handle, which rides inside [UEchoPipe.ep_pay].                  *)
  (* =================================================================== *)
  Lemma pl_left_child (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (pn : pnames) (gL gR gM : gname)
      (γp : pipe_names) (s0 szv : Z) (len ge : nat) (f : nat -> bv 8)
      (ld : list fdstate) (n : nat)
      (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (q : Z) :
    UkShPipeRound.ushq_line_at ws f 0%nat len ->
    (length (wl_body ws) < ge)%nat ->
    L = wl_line (drop 1 ws) ->
    PipeLinksLine.pline_at I = PipeDisc.LPipe ws ->
    UShEchoPipePay.ush_fd1pipe γp ld ->
    UkSh.ush_fd2p ld ->
    ukn_pay N' = (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM) ->
    m' !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int q : mword 64) ->
    UShEcho.sh_echo_slot T -∗
    era_pin γ (S gen_id) v -∗
    PipeLinks.pipe_links g -∗
    UCodeShK.shk_code (ukn_t N') -∗
    UkSh.ush_jtab (ukn_t N') -∗
    UkShRun.ush_cmd (ukn_d N') q
      (UkShRun.UExec (UkShMain.ush_args s0
         (UkShPipeRound.ushq_cut (wl_toks ws) len f ge) (wl_toks ws))) -∗
    usz (ukn_s N') szv -∗
    UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
    pl_RcL v I L pn gL gR gM γp -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N' h' m'
      (mword_of_int ShSyms.runcmd) (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hcons Hkill.
    intros Hline Hge HL Hpl Hfd1 Hfd2 Hpeq Ha0.
    assert (HLne : L <> []).
    { rewrite HL. intro Hq. pose proof (pl_L_pos ws) as Hp.
      rewrite Hq in Hp. cbn [length] in Hp. lia. }
    iIntros "#Hslot #Hpin #Hlk #Hcode #Hjt #Htree Hsz Hstd Hcwd Hch Hcr Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    (* ---- THE EXEC SUPPLY ---- *)
    iPoseProof (UShEchoPipePay.sh_exec_sup_echo_pipe_at
                  (PipeBoth.wcur gL (1/2) 0%nat) ws
                  (UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)
                  (pl_RcL v I L pn gL gR gM γp) T pn γp
                  (proj1 (proj1 Hline))
                  with "[] [] [] [] Hslot") as "#Hsup".
    { iIntros "!> [_ Hp]". rewrite -HL. iExact "Hp". }
    { rewrite -HL. iIntros "!> He".
      iApply (pl_qc_of_ep_exit pn L gL gR gM with "He"). }
    { iIntros "!> Ht". iApply (pl_qc_of_taint pn L gL gR gM with "Ht"). }
    { iApply (UexecExecMint.udep_free). }
    (* ---- THE EXEC-FAILED LAW, off the credential ---- *)
    iAssert (UkShDiag.ush_execfail_law (PS := uprogSG_free)
               (pl_RcL v I L pn gL gR gM γp)
               (PipeBoth.wcur gL (1/2) 17%nat ∗ PipeProto.side_L pn))%I
      as "#Hxl".
    { rewrite /UkShDiag.ush_execfail_law.
      iApply (UShPipeAssembly.exf_law_acc (PS := uprogSG_free)
                EchoDisc.alt_execfail 17%nat
                (pl_RcL v I L pn gL gR gM γp)
                (PipeBoth.wcur gL (1/2) 0%nat ∗ pl_XL pn
                 ∗ PipeProto.side_L pn)%I
                (PipeBoth.wcur gL (1/2) 17%nat ∗ PipeProto.side_L pn)%I).
      rewrite /pl_RcL /UEchoPipe.ep_pay /UEchoPipe.ep_frame.
      iIntros "!> (#Hinv & (#Hpi & [HsL HgL] & Hxl & _))".
      iSplitR "HgL Hxl HsL"; [ | rewrite /pl_XL; iFrame "HgL Hxl HsL" ].
      iDestruct (PipeLinks.pipe_links_taint g with "Hlk") as "#Ht".
      iApply (UShPipeAssembly.pipe_execL_law (PS := uprogSG_free)
                g Hcons v I L ws gL gR gM (pl_XL pn) (pl_YR pn L)
                (PipeProto.side_L pn)
                (pl_XL_timeless pn) (pl_YR_timeless pn L)
                Hpl with "[] Ht Hpin Hinv").
      iApply (PipeProto.pipe_excl_wtok_lb_pipeN pn γp L HLne with "Hpi"). }
    (* ---- ...AND THE ARM ---- *)
    iApply (UkShEcho.wp_kshr_exec_echo_at_holds (PS := uprogSG_free)
              (SG := uexecSG_xv6) (UShEchoPipePay.ush_fd1pipe γp) ws
              (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)
              (pl_RcL v I L pn gL gR gM γp)
              (PipeBoth.wcur gL (1/2) 17%nat ∗ PipeProto.side_L pn)%I
              N' Hc h' m' q szv s0
              (UkShPipeRound.ushq_cut (wl_toks ws) len f ge) ld n
              (proj1 (proj1 Hline)) Hpeq Ha0
              (pl_echo_argv_bytes ws f len ge Hline Hge)
              Hfd1 Hfd2
              with "Hcode Hsup Hxl [] Hjt Htree Hsz Hstd Hcwd [Hch] Hcr Hrun").
    { iIntros "!> Hc". iApply (pl_qc_of_cdL pn L gL gR gM with "Hc"). }
    { iApply (UserChildren.uch_any_of (ukn_ch N') ∅ with "Hch"). }
  Qed.

  (* =================================================================== *)
  (*  S2f  THE PARENT (ROUND-11's table, the `parent' row)                *)
  (*                                                                     *)
  (*  [UShPipeAssembly.pipe_round_parent] at the round's own resources.   *)
  (*  [Wq] is the child's exit payload [UkShFork.ushf_wq (pterm_wc g) I]  *)
  (*  and the two credential wands are this lane's                        *)
  (*  [pipe_lend_exit_pay] / [pipe_panic_exit_pay];                       *)
  (*  [S1 <> S2] is SS4.3y's relay read off the SECOND fork's answer      *)
  (*  ([ush_fork_ans_grows]) -- and it is read through an [iSplit] on a   *)
  (*  CONJUNCTION, because the landed [ush_fork_ans_sets_differ] consumes *)
  (*  the answer it reads and the parent needs it afterwards.             *)
  (* =================================================================== *)
  Lemma pl_parent (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (pn : pnames) (gL gR gM : gname)
      (γp : pipe_names) (N : uk_names Σ) `{!ukn_const N}
      (h' : CpuId) (m' : regfile) (av : nat)
      (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname) :
    PipeLinksLine.pline_at I = PipeDisc.LPipe ws ->
    L = wl_line (drop 1 ws) ->
    ukn_pay N = (fun _ : Z => UkShFork.ushf_wq (UkShPipeFork.pterm_wc g) I) ->
    r1 <> (mword_of_int (-1) : mword 64) ->
    r2 <> (mword_of_int (-1) : mword 64) ->
    era_pin γ (S gen_id) v -∗
    PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM
      (pl_XL pn) (pl_YR pn L) -∗
    shk_code (ukn_t N) -∗
    UkShPipe.ush_fork_ans (∅ : gset gname) S1
      (pl_RcL v I L pn gL gR gM γp)
      (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM) r1 -∗
    UkShPipe.ush_fork_ans S1 S2 (pl_RcR v I L pn gL gR gM γp)
      (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM) r2 -∗
    UkShPipe.ush_wait_pid_ans rw1 S2 S3 -∗
    UkShPipe.ush_wait_pid_ans rw2 S3 S4 -∗
    PipeProto.pipe_inv pn γp L -∗
    urun (SG := uexecSG_xv6) (PS := uprogSG_free) N h' m'
      (mword_of_int 0xea) av -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hpl HL Hpeq Hn1 Hn2.
    assert (HLne : L <> []).
    { rewrite HL. intro Hq. pose proof (pl_L_pos ws) as Hp.
      rewrite Hq in Hp. cbn [length] in Hp. lia. }
    assert (HLpos : (0 < length L)%nat)
      by (rewrite HL; exact (pl_L_pos ws)).
    iIntros "#Hpin #Hbinv #Hcode Hf1 Hf2 Hw1 Hw2 #Hpi Hrun".
    (* ---- SS4.3y's relay, WITHOUT consuming the answer ---- *)
    iAssert (⌜ S1 <> S2 ⌝
             ∧ UkShPipe.ush_fork_ans S1 S2 (pl_RcR v I L pn gL gR gM γp)
                 (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)
                 r2)%I with "[Hf2]" as "Hf2'".
    { iSplit; [ | iExact "Hf2" ].
      iApply (UShPipeAssembly.ush_fork_ans_grows
                (pl_RcR v I L pn gL gR gM γp)
                (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)
                r2 S1 S2 Hn2 with "Hf2"). }
    iDestruct "Hf2'" as "[%HS12 Hf2]".
    (* ---- the two wait answers' pure rows ---- *)
    iDestruct "Hw1" as (pidv) "(%Hpv & %Hm1 & Hw1)".
    iDestruct "Hw2" as (pidw) "(%Hpw & %Hm2 & Hw2)".
    iApply (UShPipeAssembly.pipe_round_parent (PS := uprogSG_free)
              g N pn γp I L ws v gL gR gM (pl_XL pn) (pl_YR pn L)
              (UkShFork.ushf_wq (UkShPipeFork.pterm_wc g) I)
              (pl_RcL v I L pn gL gR gM γp)
              (pl_RcR v I L pn gL gR gM γp)
              h' m' av r1 r2 rw1 rw2 S1 S2 S3 S4 pidv pidw
              (pl_XL_timeless pn) (pl_YR_timeless pn L)
              Hpl HL HLpos Hpeq Hpv Hpw Hn1 Hn2 HS12 Hm1 Hm2
              with "[] [] Hpi Hpin Hbinv [] [] Hcode Hf1 Hf2 Hw1 Hw2 Hrun").
    - iApply (PipeProto.pipe_excl_wtok_lb_pipeN pn γp L HLne with "Hpi").
    - iApply (PipeProto.pipe_no_short_of_inv pn γp L with "Hpi").
    - iIntros "Hc".
      iApply (UShPipeAssembly.pipe_lend_exit_pay g I).
      iApply (UkShPipeFork.pterm_wc_of g I 3%nat with "Hc").
    - iIntros "Hc".
      iApply (UShPipeAssembly.pipe_panic_exit_pay g I with "Hc").
  Qed.

  (* =================================================================== *)
  (*  S2g  THE CHILD LAW, DISCHARGED (lane SH-PIPE-ROUND-14)              *)
  (*                                                                     *)
  (*  [UShPipeRound.sh_pipe_child_law g] at its five antecedents, which   *)
  (*  is ROUND-11's instantiation table applied once.  Everything it      *)
  (*  names is landed: [pl_round_alloc] mints the protocol's names and    *)
  (*  the family's three cursors BEFORE the walk (the payload names all   *)
  (*  four), [pl_pipe_call] is the registrar, [pl_split_k] the four-way   *)
  (*  split, [pl_panic_pipe_law] / [pl_fork_panic_law] the two            *)
  (*  diagnostics, [pl_left_child] / [pl_right_child] / [pl_parent] the   *)
  (*  three continuations, and the walk is                                *)
  (*  [UShPipeChild.wp_kshm_child_pipe_paid_line_at_sz] at [Usz := emp]   *)
  (*  -- the break read off the parse's own leftover, SH-PIPE-ROUND-12's  *)
  (*  [usz] vacuity.                                                     *)
  (* =================================================================== *)
  Local Lemma pl_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* THE PARENT'S ROW OF THE SPLIT.  [pl_split]'s landed third slot is the
     protocol handle alone and [UShPipeAssembly.pipe_round_parent] also
     reads the FAMILY; [PipeBoth.blk2_inv] is an [inv] and so persistent,
     so the split may hand a copy to the parent as well.  [pl_split] is
     untouched. *)
  Definition pl_Rk (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) (gp : pipe_names) : iProp Σ :=
    (PipeProto.pipe_inv pn gp L
     ∗ PipeBoth.blk2_inv g blk2N (S gen_id) v I L gL gR gM
         (pl_XL pn) (pl_YR pn L))%I.

  Lemma pl_split_k (v : era_pins) (I L : list (bv 8)) (pn : pnames)
      (gL gR gM : gname) (gp : pipe_names) :
    pl_Cr v I L pn gL gR gM -∗
    UShPipeAssembly.pipe_reg_pay pn emp%I L gp -∗
    pl_RcL v I L pn gL gR gM gp
    ∗ (pl_RcR v I L pn gL gR gM gp
       ∗ (pl_Rk v I L pn gL gR gM gp ∗ emp)).
  Proof using .
    rewrite /pl_Cr /UShPipeAssembly.pipe_reg_pay /pl_RcL /pl_RcR /pl_Rk
            /UEchoPipe.ep_pay /UEchoPipe.ep_frame.
    iIntros "(#Hinv & HgL & HgR & HgM) (Hr & HsR & (#Hpi & [HsL _] & Hw & Hlb))".
    iSplitL "HgL HsL Hw Hlb".
    { iFrame "Hinv Hpi HsL HgL Hw Hlb". }
    iSplitL "HgR HgM Hr HsR".
    { iFrame "Hinv Hpi Hr HsR HgR HgM". }
    iSplitR; [ iFrame "Hpi Hinv" | done ].
  Qed.

  (* THE PARSE'S THREE mallocs, chained at ONE capability bound (168) --
     [UkShMalloc]'s own [ushm_malloc_le_exec] / [_le_one].  The pipe line's
     parse calls [malloc] three times ([execcmd], [pipecmd], [execcmd]),
     twelve units each out of the 4096 the first [morecore] inserts. *)
  Local Lemma pl_malloc23 (N' : uk_names Σ) (szf : Z) :
    UkShParse.ushp_malloc_ty_le (PS := uprogSG_free) N' 168
      (UkShMalloc.ushm_one_ge N' szf 4072)
      (UkShMalloc.ushm_one_ge N' szf 4060).
  Proof using .
    assert (E : (4072 - ((168 + 15) / 16 + 1))%Z = 4060%Z)
      by (vm_compute; reflexivity).
    rewrite <- E.
    exact (UkShMalloc.ushm_malloc_le_one (PS := uprogSG_free) N' 168 szf 4072
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
  Qed.

  (* ...AND THE BREAK, off what the parse LEFT (SH-PIPE-ROUND-12's repair:
     the walk's [usz] may not be held beside the allocator state). *)
  Local Lemma pl_usz_of_one (N' : uk_names Σ) (szf : Z) :
    ⊢ UkShMalloc.ushm_one_ge N' szf 4060 -∗ emp -∗ usz (ukn_s N') szf.
  Proof using .
    iIntros "H _".
    rewrite /UkShMalloc.ushm_one_ge. iDestruct "H" as (R) "[_ H]".
    rewrite /UkShMalloc.ushm_one. iDestruct "H" as (c) "(_ & _ & _ & _ & _ & $)".
  Qed.

  Lemma pl_child_law : ⊢ UShPipeRound.sh_pipe_child_law g.
  Proof using Hcons Hkill uartGhostG0 pipeProtoG0.
    rewrite /UShPipeRound.sh_pipe_child_law.
    iIntros "!> #Hlk #Hcat #Hslot #Hpin0 #Hdps".
    iDestruct "Hpin0" as (v) "#Hpin".
    iDestruct (PipeLinks.pipe_links_taint g with "Hlk") as "#Ht".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv s0 len wsf gf sz ld n I)
      "%Hpeq %Hs1 %Hlp %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
       Hcp Hrun".
    destruct Hlp as (ws & Hwsf & Hline).
    destruct Hrows as (Hfd0c & Hfd1p & Hfd2p).
    pose proof (pline_at_of_lp I wsf ws Hlws Hfbk Hwsf (proj1 Hline)) as Hpl.
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hcst.
    (* ---- the ledger: its three rows, and that nothing in it is shut ---- *)
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen3.
    pose proof (pl_fd_lowest_none ld Hlen3 Hfd0c Hfd1p Hfd2p) as Hnone.
    assert (H1lt : (1 < length ld)%nat)
      by (rewrite Hlen3; unfold NSTD; lia).
    assert (H0lt : (0 < length ld)%nat)
      by (rewrite Hlen3; unfold NSTD; lia).
    destruct Hfd0c as [wr0 Hl0]. destruct Hfd1p as [rb1 Hl1].
    (* ---- the family's names and the round's lend ---- *)
    iApply pl_fupd_mwp.
    iMod (pl_round_alloc v I (wl_line (drop 1 ws))
            (pboth_line_of_at I ws Hpl) with "Hpin")
      as (pn gL gR gM) "(Hpre & Hw & Hr & HsL & HsR & Halloc)".
    iModIntro.
    (* ---- the taint's reading of the lend, for the fork-panic law ---- *)
    iDestruct (UkShPipeFork.pterm_wc_3 g I with "Hcp") as "Hcp".
    iDestruct (pipe_wcl3_inp I with "Hcp") as "[Hcp #Hinp]".
    iDestruct (UkShPipeFork.pterm_wc_of g I 3%nat with "Hcp") as "Hcp".
    iAssert (inp_lb v I ∨ T)%I as "#Hlb".
    { iDestruct "Hinp" as "[Hx | #HT]"; [ | by iRight ].
      iDestruct "Hx" as (v0) "[#Hp0 #He0]".
      iDestruct (era_pin_agree with "Hp0 Hpin") as %->.
      iLeft. iExact "He0". }
    (* ---- the registrar ---- *)
    iPoseProof (pl_pipe_call N' pn ld (wl_line (drop 1 ws))
                  (fun k H => H) Hnone with "Hpre Hw HsL Hr HsR")
      as "Hpipe".
    (* ---- the fork-panic law ([pl_panic_pipe_law] is a GOAL below, for
       [pl_exf_at_pers0]'s reason) ---- *)
    iAssert (□ (∀ gp : pipe_names,
                UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
                  EchoDisc.alt_panic 5%nat
                  (pl_RcR v I (wl_line (drop 1 ws)) pn gL gR gM gp ∗ emp)
                  (UkShPipeFork.pterm_shape g I 5%nat ∨ T)))%I as "#Hlawf".
    { iIntros "!>" (gp).
      iApply (pl_fork_panic_law v I (wl_line (drop 1 ws)) ws pn gL gR gM gp
                Hpl with "Hdps Hlk Hpin Hlb"). }
    (* ---- ...AND THE WALK ---- *)
    iApply (UShPipeChild.wp_kshm_child_pipe_paid_line_at_sz
              (SG := uexecSG_xv6) (PS := uprogSG_free)
              N' (fun k H => H)
              (UkShMalloc.ushm_fresh N' sz)
              (UkShMalloc.ushm_one_ge N' (sz + 65536) 4084)
              (UkShMalloc.ushm_one_ge N' (sz + 65536) 4072)
              (UkShMalloc.ushm_one_ge N' (sz + 65536) 4060)
              (UkShMalloc.ushm_malloc_le_next (PS := uprogSG_free) N'
                 (sz + 65536))
              h m dw dv s0 (sz + 65536) FsImg.ROOTINO len gf ws ld
              (FdOpen true wr0 (FdDevice ConsoleInv.CONSOLE))
              (FdOpen rb1 true (FdDevice ConsoleInv.CONSOLE))
              (∅ : gset gname) n
              (UShPipeAssembly.pipe_reg_pay pn emp%I
                 (wl_line (drop 1 ws)))
              (pl_RcL v I (wl_line (drop 1 ws)) pn gL gR gM)
              (pl_RcR v I (wl_line (drop 1 ws)) pn gL gR gM)
              (pl_Rk v I (wl_line (drop 1 ws)) pn gL gR gM)
              (fun _ : pipe_names => emp%I)
              (fun _ : pipe_names =>
                 (UkShPipeFork.pterm_shape g I 5%nat ∨ T)%I)
              (fun _ : Z =>
                 UShPipeAssembly.pipe_Qc_at g pn
                   (wl_line (drop 1 ws)) gL gR gM)
              (UkShPipeFork.pterm_wc g I 3%nat)
              (pl_Cr v I (wl_line (drop 1 ws)) pn gL gR gM)
              (pipe_Wcl_at g I 0%nat)
              emp%I (UkSh.ush_pid N') UkShPipe.ush_wait_pid_ans
              (UkShMalloc.ushm_malloc_le_exec (PS := uprogSG_free) N'
                 (fun k H => H) sz ltac:(lia) Hszal Hszok)
              (pl_malloc23 N' (sz + 65536))
              (pl_usz_of_one N' (sz + 65536))
              Hs1 Hline Hs0 Hs64 Hs38 (fun x y => eq_refl) Hl0 Hl1
              ltac:(discriminate) ltac:(discriminate)
              ltac:(intros rb wb gn Hq; discriminate Hq)
              ltac:(intros rb wb gn Hq; discriminate Hq)
              Hfd2p
              with "Hcode Hjt Hpcode Hpro Hstr Hws Hsy [] Hstd Hcwd Hch HM
                    Hcp [] [] Halloc [] Hpipe Hpid [] [] [] Hlawf []
                    Hrun [] [] []").
    - (* [Usz := emp] *) done.
    - (* the payload's taint arm *)
      iIntros "!> Ht2".
      iApply (pl_qc_of_taint pn (wl_line (drop 1 ws)) gL gR gM with "Ht2").
    - (* the lend pays the exit *)
      iIntros "!> Hc". rewrite Hpeq.
      iApply (UShPipeAssembly.pipe_lend_exit_pay g I with "Hc").
    - (* the four-way split *)
      iIntros (gp) "Hcr Hrg".
      iApply (pl_split_k v I (wl_line (drop 1 ws)) pn gL gR gM gp
                with "Hcr Hrg").
    - (* the two [wait(0)]s' law, at the caller's own pid *)
      iApply (UkShPipe.ush_wait0_law_pid (PS := uprogSG_free)
                (fun k H => H) N').
    - (* the [pipe(2)]-failed tail's own diagnostic law *)
      iApply (pl_panic_pipe_law v I (wl_line (drop 1 ws)) ws pn gL gR gM
                Hpl with "Hlk Hpin").
    - (* the [pipe(2)]-failed tail pays the exit *)
      iIntros "!> _ Hb". rewrite Hpeq.
      iApply (UShPipeAssembly.pipe_panic_exit_pay g I with "Hb").
    - (* ...and the two [panic("fork")] tails *)
      iIntros "!>" (gp) "_ Hb". rewrite Hpeq.
      iApply (UShPipeAssembly.pipe_fork_exit_pay g v I with "Hpin Hb").
    - (* ---- THE LEFT CHILD ---- *)
      iIntros (N2 h2 m2 g2 gp q)
        "%Hpeq2 %Ha02 _ #Hcode2 #Hjt2 #Htree2 Hsz2 Hstd2 Hcwd2 Hch2 _ _
         HcL Hrun2".
      replace (2 + (UkShDiag.ush_Dg + (68 + n)))%nat
        with (6 + (2 + (UkShDiag.ush_Dg + (62 + n))))%nat by lia.
      iApply (pl_left_child v I (wl_line (drop 1 ws)) ws pn gL gR gM gp
                s0 (sz + 65536) len (length (wl_body ws) + 3 + 3)%nat gf
                (<[1%nat := FdOpen false true (FdPipe gp)]> ld) (62 + n)%nat
                N2 h2 m2 q Hline ltac:(lia) eq_refl Hpl
                ltac:(exists false;
                      exact (list_lookup_insert ld 1%nat
                               (FdOpen false true (FdPipe gp)) H1lt))
                ltac:(destruct Hfd2p as [rb2 H2]; exists rb2;
                      rewrite list_lookup_insert_ne; [ exact H2 | lia ])
                Hpeq2 Ha02
                with "Hslot Hpin Hlk Hcode2 Hjt2 Htree2 Hsz2 Hstd2 Hcwd2
                      Hch2 HcL Hrun2").
    - (* ---- THE RIGHT CHILD ---- *)
      iIntros (N2 h2 m2 g2 gp q)
        "%Hpeq2 %Ha02 _ #Hcode2 #Hjt2 #Htree2 Hsz2 Hstd2 Hcwd2 Hch2 _ _
         HcR Hrun2".
      replace (2 + (UkShDiag.ush_Dg + (68 + n)))%nat
        with (6 + (2 + (UkShDiag.ush_Dg + (62 + n))))%nat by lia.
      iApply (pl_right_child v I (wl_line (drop 1 ws)) ws pn gL gR gM gp
                s0 (sz + 65536) len gf
                (<[0%nat := FdOpen true false (FdPipe gp)]> ld) (62 + n)%nat
                N2 h2 m2 q Hline eq_refl Hpl
                ltac:(split;
                      [ exists false;
                        exact (list_lookup_insert ld 0%nat
                                 (FdOpen true false (FdPipe gp)) H0lt)
                      | exists rb1; rewrite list_lookup_insert_ne;
                        [ exact Hl1 | lia ] ])
                ltac:(destruct Hfd2p as [rb2 H2]; exists rb2;
                      rewrite list_lookup_insert_ne; [ exact H2 | lia ])
                Hpeq2 Ha02
                with "Hcat Hdps Hpin Hlk Hcode2 Hjt2 Htree2 Hsz2 Hstd2
                      Hcwd2 Hch2 HcR Hrun2").
    - (* ---- THE PARENT, at 0xea ---- *)
      iIntros (h2 m2 gp r1 r2 rw1 rw2 S1 S2 S3 S4)
        "%Hn1 %Hn2 Hf1 Hf2 Hw1 Hw2 Hch2 #Hjt2 Hsz2 Hstd2 Hcwd2 Hrk _ Hpid2
         Hrun2".
      iDestruct "Hrk" as "[#Hpi #Hbinv]".
      iApply (pl_parent v I (wl_line (drop 1 ws)) ws pn gL gR gM gp
                N' h2 m2 (2 + (UkShDiag.ush_Dg + (68 + n)))%nat
                r1 r2 rw1 rw2 S1 S2 S3 S4 Hpl eq_refl Hpeq Hn1 Hn2
                with "Hpin Hbinv Hcode Hf1 Hf2 Hw1 Hw2 Hpi Hrun2").
  Qed.

End UShPipeLaw.



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
