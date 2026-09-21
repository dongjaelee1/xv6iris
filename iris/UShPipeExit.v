(* ===================================================================== *)
(*  UShPipeExit.v -- THE ROUND'S EXIT, AND WHY IT DOES NOT REACH THE     *)
(*  SHELL'S BOUNDARY CREDENTIAL (lane SH-PIPE-ROUND-3, STOP 1).          *)
(*                                                                       *)
(*  This file MECHANISES the shape mismatch the lane stopped at.         *)
(*  Nothing in it is a step towards the round: it is the refutation the  *)
(*  brief's first STOP rule asks for -- report both shapes, stop at the  *)
(*  exit, let the coordinator reconcile.                                 *)
(*                                                                       *)
(*  THE TWO SHAPES.                                                      *)
(*                                                                       *)
(*   (a) WHAT THE FAMILY'S EXIT PRODUCES.  [PipeBoth.pblk2_exit] spends  *)
(*       the PROMPT'S FIRST BYTE -- the claim step under it,             *)
(*       [PipeOut.pecl_blk2_file], is stated at [b = u_prompt !!! 0] and *)
(*       at no other byte, and it is the ONLY step that appends the      *)
(*       round's code to [cs] -- and it leaves                           *)
(*       [PipeLinksLine.pwc_sp_t], which through                         *)
(*       [PipeLinkInst.pipe_inst_lcred] is [Wcf I 1].                 *)
(*                                                                       *)
(*   (b) WHAT THE SHELL WANTS.  sh's runcmd child hands its parent       *)
(*       [UkShFork.ushf_wq I = Wcf I 3 \/ Wcf I 0], and the fork arm     *)
(*       converts both to [Wcf I 0] before the loop re-enters            *)
(*       ([UkShFork.wp_kshf_fork_at], the re-entry's [iApply (Hwbl np    *)
(*       with ...)]).  [Wcf I 0] is [PipeLinksLine.pwc_line], i.e.       *)
(*       [pwc_pro k v I] or [pwc_post k v I a] at an alternative the     *)
(*       round may pick -- and [pwc_post] at any block longer than the   *)
(*       prompt carries [cs_lb v (cs ++ [a])]: THE CODE IS ALREADY       *)
(*       FILED.  The prompt itself is written by sh's MAIN LOOP, one     *)
(*       process later, out of that credential.                          *)
(*                                                                       *)
(*  SO THE ROUND WOULD HAVE TO HAND BACK A FILED BLOCK, and it cannot.   *)
(*  While the round is open -- i.e. while ANYONE holds the writer's half *)
(*  of the era's current-round ghost [PipeOut.pe_cur] at this round --   *)
(*  the claim's own choice list is ONE SHORT of it                       *)
(*  ([PipeOut.pblk_open]'s [pblk2_at]: [length cs = nlines I - 1]),      *)
(*  while both arms of [pwc_line] want it at least [nlines I] long.      *)
(*  That is [pipe_open_not_post] / [pipe_open_not_line] below, and the   *)
(*  taint is the only state in which the two coexist.  The family        *)
(*  carries that half whenever its selector is non-empty, so the         *)
(*  corollary [pipe_blk2_not_line] is the same fact at the round's own   *)
(*  end state, at exactly the premises [pblk2_exit] takes.               *)
(*                                                                       *)
(*  THE LEMMAS ARE STATED WITHOUT THE FAMILY ON PURPOSE.  Holding the    *)
(*  family AND a block credential at once is refuted by the turn alone   *)
(*  ([UShPipeRound.pipe_turn_one_writer]: [EchoOut.turn] is half an      *)
(*  authority), so a lemma that needs both proves only that the exit     *)
(*  must be a TRADE.  What is refuted here is the trade's RESULT: the    *)
(*  post-block credential cannot exist while the round is open, whether  *)
(*  or not the family still does.                                        *)
(*                                                                       *)
(*  WHY THE CODE CANNOT BE FILED EARLIER (the reason the design put the  *)
(*  filing at the prompt, and it survives this finding): nobody knows    *)
(*  which byte is the block's LAST.  The final selector is decided by    *)
(*  two separate processes whose sources are fixed but whose             *)
(*  PARTICIPATION is not -- at [PExecL] the right child writes nothing,  *)
(*  at [PRan] the left one does -- so a writer standing at the end of    *)
(*  its own source cannot tell whether the other will write, and the     *)
(*  block's length is settled only by the `$' of the NEXT prompt.        *)
(*                                                                       *)
(*  WHAT WOULD RECONCILE IT is in the lane report, not here (it moves    *)
(*  landed statements this lane may not move): [pwc_line] needs a THIRD  *)
(*  arm carrying the complete unfiled block, so that                     *)
(*  [PipeLinksLine.pprompt_dollar_line] -- the ONE consumer of           *)
(*  [pwc_line], which already writes exactly the byte [pblk2_exit]       *)
(*  wants -- can file the round's code there; the family has to be       *)
(*  RECOVERABLE at the end of the round, which a plain [inv]             *)
(*  ([PipeBoth.blk2_inv]) never is; and cat's round has to be generic in *)
(*  its cursor ([UCatPipe.pcat_round_at] files [pcat_alt] at cat's first *)
(*  byte through [pcch], which is the one thing a two-writer block may   *)
(*  not do).                                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map
        invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import LogEntryDefs.
Require Import PipeOutPure.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinksLine.
Require Import PipeBoth.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section pipe_exit.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).

  (* =================================================================== *)
  (*  S1  WHAT AN OPEN ROUND SAYS ABOUT THE CLAIM'S CHOICE LIST           *)
  (*                                                                     *)
  (*  The writer's half of [pe_cur] at round [r] forces the claim into    *)
  (*  its OPEN arm ([cur_half_excl] kills the between-rounds one, where   *)
  (*  the claim holds the whole ghost), and there [pblk_open]'s           *)
  (*  [pblk2_at] pins the length of [o_cs] at [r].                        *)
  (* =================================================================== *)
  Lemma pecl_open_cs_len (k r : nat) (w : pipe_era) (gb : gname)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    pera_pin g k w -∗ cur_half w (1/2) r gb -∗ pecl g k ho H -∗
    (PT ∨ ∃ v : era_pins, era_pin γ k v
           ∗ (∃ cs : list nat, ⌜length cs = r⌝ ∗ cs_auth v cs)).
  Proof using .
    iIntros "#Hpera Hcw Hcl".
    rewrite /pecl. iDestruct "Hcl" as "[#HT | Hc]"; [by iLeft |].
    iDestruct "Hc"
      as (v2 w2 so r2 gb2 pre opn)
         "(#Hpin2 & #Hpera2 & Hblk & Hcur & Hrb & Hta & Hcsa & Hpsa & HEa
           & Hdl & Hdll & %Hall)".
    iDestruct (pera_pin_agree with "Hpera Hpera2") as %->.
    destruct Hall as [(Hfls & _) | (Htrue & Hopen)].
    { rewrite Hfls. cbn [cur_frac].
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    rewrite Htrue. cbn [cur_frac].
    iDestruct (cur_half_agree with "Hcw Hcur") as %[Hr _].
    iRight. iExists v2. iFrame "Hpin2". iExists (o_cs so). iFrame "Hcsa".
    iPureIntro.
    destruct Hopen as (_ & Hop & _).
    destruct Hop as (Hreq & _ & _ & (a' & Hat & _)).
    destruct Hat as (_ & _ & Hcslen & _).
    rewrite Hcslen -Hreq Hr. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S1b  THE ENTRY, WHICH IS FINE -- the other half of the STOP rule    *)
  (*                                                                     *)
  (*  [lk_lcred]'s owed arm at an [LPipe] line IS the family at the empty *)
  (*  selector.  [PipeLinkInst.pipe_inst_lcred] reads [Wcf I 3] as     *)
  (*  [exists v, era_pin * pwc_lpr g k v I 3] and [pwc_lpr _ _ _ 3] is    *)
  (*  [pwc_blk k v I 0 0] by [lk_lpr_S3]'s [eq_refl]; the two steps below *)
  (*  are landed ([pwc_lend_of_blk0], [pwc_blk2_of_lend]).  The ONE thing *)
  (*  the child law does not hand over literally is [pboth_line I] -- the *)
  (*  last body parses to [LPipe] -- which is a pure consequence of the   *)
  (*  line facts it does hand over ([UShPipeRound.ushq_lp] and            *)
  (*  [FileDisc.fline_ok (ush_lastbody I)]), through [PipeUline].         *)
  (* =================================================================== *)
  Lemma pipe_blk2_of_lpr3 (k : nat) (v : era_pins) (I R : list (bv 8)) :
    pboth_line I ->
    pwc_lpr g k v I 3%nat -∗ pwc_blk2 g k v I R [] 0%nat 0%nat.
  Proof using .
    intros Hl. iIntros "Hc".
    iApply (pwc_blk2_of_lend g k v I R Hl).
    iApply (pwc_lend_of_blk0 g k v I 0%nat with "Hc").
  Qed.

  (* =================================================================== *)
  (*  S2  THE REFUTATION, at the shell's two boundary shapes              *)
  (* =================================================================== *)

  (* (b) [pwc_post]: the block written up to its prompt, WITH THE CODE
         FILED.  This is the arm sh's fork re-entry lands on when the
         child's exit paid a block ([lk_lcred_of_post_a]). *)
  Lemma pipe_open_not_post (k : nat) (v : era_pins) (w : pipe_era)
      (gb : gname) (I : list (bv 8)) (a : nat)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    (* the block owes more than the prompt's own two bytes -- which at the
       round's code is exactly [sel <> []] ([PipeBoth.pblk2_code_len]) *)
    (2 < length (pab I a))%nat ->
    era_pin γ k v -∗ pera_pin g k w -∗
    cur_half w (1/2) (nlines I - 1)%nat gb -∗
    pwc_post g k v I a -∗ pecl g k ho H -∗ PT.
  Proof using .
    intros Hlen. iIntros "#Hpin #Hpera Hcw Hpost Hcl".
    iDestruct (pecl_open_cs_len with "Hpera Hcw Hcl") as "[#HT | Hc]";
      [iExact "HT" |].
    iDestruct "Hc" as (v2) "[#Hpin2 Hc]".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct "Hc" as (cs0) "[%Hcs0 Hcsa]".
    rewrite /pwc_post /pwc_blk.
    iDestruct "Hpost" as "[Hp | #HT]"; [| iExact "HT"].
    iDestruct "Hp" as (ps' cs' P') "(%Hw' & Htn' & #Hps' & #Hcs' & #HE')".
    iDestruct (cs_lb_prefix with "Hcsa Hcs'") as %Hpre.
    iExFalso. iPureIntro.
    (* the credential's index is positive, so its choice list is the
       claim's with the round's code ALREADY APPENDED *)
    assert (Hbc : blkcs_p cs' a (length (pab I a) - 2)%nat = cs' ++ [a]).
    { destruct (length (pab I a) - 2)%nat as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc in Hpre.
    destruct Hw' as ((_ & _ & Hn' & _) & _).
    pose proof (prefix_length _ _ Hpre) as Hle.
    rewrite length_app in Hle. cbn [length] in Hle.
    (* [Hn']: [nlines I = S (length cs')], so the credential wants
       [nlines I] entries; [Hcs0]: the open round leaves [nlines I - 1]. *)
    lia.
  Qed.

  (* (a) [pwc_pro]: the prologue owed -- the other arm of [pwc_line], and
         the one a PANICKING round leaves.  Refuted the same way: it wants
         a choice list as long as the input has lines. *)
  Lemma pipe_open_not_pro (k : nat) (v : era_pins) (w : pipe_era)
      (gb : gname) (I : list (bv 8))
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    I <> [] ->
    rest_of I = [] ->
    era_pin γ k v -∗ pera_pin g k w -∗
    cur_half w (1/2) (nlines I - 1)%nat gb -∗
    pwc_pro g k v I -∗ pecl g k ho H -∗ PT.
  Proof using .
    intros Hne Hrest. iIntros "#Hpin #Hpera Hcw Hpro Hcl".
    iDestruct (pecl_open_cs_len with "Hpera Hcw Hcl") as "[#HT | Hc]";
      [iExact "HT" |].
    iDestruct "Hc" as (v2) "[#Hpin2 Hc]".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct "Hc" as (cs0) "[%Hcs0 Hcsa]".
    rewrite /pwc_pro.
    iDestruct "Hpro" as "[Hp | #HT]"; [| iExact "HT"].
    iDestruct "Hp" as (ps' cs' P') "(%Hw' & Htn' & #Hps' & #Hcs' & #HE')".
    iDestruct (cs_lb_prefix with "Hcsa Hcs'") as %Hpre.
    iExFalso. iPureIntro.
    destruct Hw' as (_ & _ & Hn' & _).
    pose proof (prefix_length _ _ Hpre) as Hle.
    pose proof (nlines_pos_of_rest_nil I Hne Hrest) as Hpos.
    lia.
  Qed.

  (* ...AND THE TWO TOGETHER ARE [pwc_line], i.e. [Wcf I 0] -- what the
     shell's loop re-enters at.  The [pwc_post] arm is read at the round's
     OWN code: a boundary credential filed at a different alternative is
     refuted on the wire by [PipeDisc.pcont_pair_det], which is the
     design's own uniqueness argument and is not repeated here. *)
  Lemma pipe_open_not_line (k : nat) (v : era_pins) (w : pipe_era)
      (gb : gname) (I : list (bv 8)) (a : nat)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    I <> [] ->
    rest_of I = [] ->
    (2 < length (pab I a))%nat ->
    era_pin γ k v -∗ pera_pin g k w -∗
    cur_half w (1/2) (nlines I - 1)%nat gb -∗
    (pwc_pro g k v I ∨ pwc_post g k v I a) -∗ pecl g k ho H -∗ PT.
  Proof using .
    intros Hne Hrest Hlen. iIntros "#Hpin #Hpera Hcw [Hpro | Hpost] Hcl".
    - iApply (pipe_open_not_pro k v w gb I ho H Hne Hrest
                with "Hpin Hpera Hcw Hpro Hcl").
    - iApply (pipe_open_not_post k v w gb I a ho H Hlen
                with "Hpin Hpera Hcw Hpost Hcl").
  Qed.

  (* =================================================================== *)
  (*  S2b  THE DEGENERATE ALTERNATIVE, which S2 does not cover             *)
  (*                                                                     *)
  (*  [pwc_line] DOES have one unfiled state: the NO-OUTPUT alternative   *)
  (*  ([PipeLinksLine.pwc_line_of_blk0] at [pnoc_of], whose whole block   *)
  (*  is the prompt, so [pwc_post]'s index is 0 and [blkcs_p cs a 0 =     *)
  (*  cs]).  S2's premise [2 < length (pab I a)] excludes it, and what    *)
  (*  excludes it in fact is the TURN and not the choice list: that state *)
  (*  stands at the block's START, and a round that has written [c1 + c2] *)
  (*  bytes has moved the turn by that much.  Below is the resource half  *)
  (*  of it -- three halves of one [mono_nat] authority, the claim's      *)
  (*  included ([UShPipeRound.pipe_turn_one_writer]'s idiom) -- which     *)
  (*  covers EVERY alternative but only in the hold-both form.            *)
  (*                                                                     *)
  (*  The trade form of the degenerate case is not a theorem here, and    *)
  (*  the reason it needs none: a trade cannot move the turn (the other   *)
  (*  half is the claim's), so it would have to DROP the round's          *)
  (*  [cur_half] -- and then the claim is stuck in its open arm for ever, *)
  (*  where the ONLY step that can put the prompt's `$' on the wire is    *)
  (*  [PipeOut.pecl_blk2_file], which asks for the very half that was     *)
  (*  dropped.                                                           *)
  (* =================================================================== *)
  (* [UShPipeRound.pipe_turn_one_writer] restated here (that file is the
     round's, far above this one): [EchoOut.turn] is HALF a [mono_nat]
     authority, so two writers beside the claim are three halves. *)
  Lemma pipe_turn_three (v : era_pins) (P1 P2 P3 : nat) :
    turn v P1 -∗ turn v P2 -∗ turn_auth v P3 -∗ False.
  Proof using .
    rewrite /turn /turn_auth. iIntros "H1 H2 H3".
    iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[_ <-].
    (* the two halves are COMBINED, not split out of a rewritten [1]:
       [iEval (rewrite -Qp.half_half)] + [iSplitL] is the landed idiom
       ([EchoOut.turn_update]) and it does not fire in this file's
       scopes. *)
    iCombine "H1 H2" as "H".
    iDestruct (mono_nat_auth_own_agree with "H H3") as %[Hq _].
    iPureIntro. rewrite ?Qp.half_half in Hq.
    exact (Qp.not_add_le_l 1%Qp (1/2)%Qp Hq).
  Qed.

  Lemma pipe_blk2_not_blk0 (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 a i : nat)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    era_pin γ k v -∗
    pwc_blk2 g k v I R sel c1 c2 -∗ pwc_blk g k v I a i -∗
    pecl g k ho H -∗ PT.
  Proof using .
    iIntros "#Hpin Hfam Hblk Hcl".
    rewrite /pecl. iDestruct "Hcl" as "[#HT | Hc]"; [iExact "HT" |].
    rewrite /pwc_blk2. iDestruct "Hfam" as "[Hf | #HT]"; [| iExact "HT"].
    rewrite /pwc_blk. iDestruct "Hblk" as "[Hb | #HT]"; [| iExact "HT"].
    iDestruct "Hf" as (ps cs P) "(_ & _ & Htn1 & _)".
    iDestruct "Hb" as (ps' cs' P') "(_ & Htn2 & _)".
    iDestruct "Hc"
      as (v2 w so r gb pre opn)
         "(#Hpin2 & _ & _ & _ & _ & Hta & _)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iExFalso.
    iApply (pipe_turn_three v (P + c1 + c2)%nat (P' + i)%nat
              (pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so))
              with "Htn1 Htn2 Hta").
  Qed.

  (* =================================================================== *)
  (*  S3  ...AT THE ROUND'S OWN END STATE                                 *)
  (*                                                                     *)
  (*  The family carries the writer's half of [pe_cur] whenever its       *)
  (*  selector is non-empty ([PipeBoth.pblk_led]), and its code's length  *)
  (*  is [S (S (c1 + c2))] ([pblk2_code_len]) -- so the premises of S2    *)
  (*  are exactly the premises [PipeBoth.pblk2_exit] takes.               *)
  (* =================================================================== *)
  Lemma pipe_blk2_not_line (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 a : nat)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    sel <> [] ->
    pblk2_code I R sel a ->
    era_pin γ k v -∗
    pwc_blk2 g k v I R sel c1 c2 -∗
    (pwc_pro g k v I ∨ pwc_post g k v I a) -∗
    pecl g k ho H -∗
    PT.
  Proof using .
    intros Hsel Hcode. iIntros "#Hpin Hfam Hline Hcl".
    rewrite /pwc_blk2. iDestruct "Hfam" as "[Hf | #HT]"; [| iExact "HT"].
    iDestruct "Hf"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    rewrite /pblk_led. iDestruct "Hled" as "[%Hnil | Hled]"; [done |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcw & #Hrlb)".
    (* the round's own block is longer than the prompt *)
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hw as (Hne & Hrest & _ & _ & _ & _ & Hlen & _).
    pose proof (pblk2_code_len I R sel a c1 c2 Hwf Hlen Hcode) as Hab.
    assert (Hpos : (0 < c1 + c2)%nat).
    { destruct sel as [| b s]; [done |]. cbn [length] in Hlen. lia. }
    iApply (pipe_open_not_line k v w gb I a ho H Hne Hrest
              ltac:(rewrite Hab; lia) with "Hpin Hpera Hcw Hline Hcl").
  Qed.

End pipe_exit.
