(* ===================================================================== *)
(*  UShPipeRound2.v -- THE PIPELINE ROUND, ASSEMBLED AS FAR AS THE       *)
(*  LANDED INTERFACES ALLOW, AND THE LEAF AT WHICH IT STOPS              *)
(*  (lane SH-PIPE-ROUND-5; design claude-notes/design/app-pipe.md        *)
(*  SS4.3f-SS4.3i).                                                      *)
(*                                                                       *)
(*  WHAT IS HERE.                                                        *)
(*                                                                       *)
(*   S1  the round's NAMESPACE, and the two mask side conditions the     *)
(*       family's byte steps ask for, discharged once and for all at it: *)
(*       PIPE-EXEC-ECHO's exclusion is at [Eex := pipeN]                 *)
(*       ([XL := PipeProto.wcur pn 0], [YR := pws_lb pn (take 1 L)]),    *)
(*       so the round's own namespace has to miss BOTH the port's and    *)
(*       the protocol's.                                                  *)
(*   S2  the round's ENTRY: sh's fork lends [Wcf I 3] and that IS the    *)
(*       family at the empty selector, with the three cursor halves the  *)
(*       round keeps.                                                    *)
(*   S3  the round's CODE, pure: the four (c1, R, c2) combinations the   *)
(*       protocol admits, each at its own landed [pblk2_code_*].         *)
(*   S4  the round's EXIT on the GOOD path: the family closed at the     *)
(*       two cursors IS the loop's boundary credential [Wcf I 0].        *)
(*   S5  the entry payment's SPLIT: [UEchoPipe.ep_pay]'s frame is        *)
(*       separable, which is what lets the [pipe(2)] registrar be run    *)
(*       at [Wq := emp] and the left cursor half be joined to it at the  *)
(*       arm's own split -- see the lane report, finding (2).            *)
(*   S6  THE STOP: at a round whose second [fork1] failed, the runcmd    *)
(*       child's exit payload CANNOT be [UkShFork.ushf_wq], and the      *)
(*       refutation is a theorem and not an impression.                  *)
(*   S7  ...and the CONTRAST: with both cursors at zero the family IS    *)
(*       the lend again, which is what makes the FIRST panic tail        *)
(*       (panic("pipe"), no child alive) payable.                        *)
(*                                                                       *)
(*  WHAT IS NOT HERE, and why: the WALK.  [UShPipeChild.                 *)
(*  wp_kshm_child_pipe_paid_line] is applied at the payloads S2-S4       *)
(*  build, but its LAST tail -- the second [fork1]'s panic -- is paid    *)
(*  into [ukn_pay N (-1)], and [UShPipeRound.sh_pipe_child_law] fixes    *)
(*  that at [UkShFork.ushf_wq I]; S6 is the proof that no round can      *)
(*  meet it.  Design SS4.3i's repair (the pipe line's child exit payload *)
(*  is [ushf_wq I \/ pwc_fork_exit ... 5]) is a change to                 *)
(*  [UShPipeRound.sh_pipe_child_law]'s DEFINITION, which this lane may   *)
(*  not make.                                                            *)
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
Require Import PipeDisc.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinksLine.
Require Import PipeBoth.
Require Import PipeLinkInst.
Require Import Xv6G.            (* [xv6G] -- the backtick Context trap: a
                                   generalisation over a name that is NOT
                                   in scope BINDS it (durable-notes) *)
Require Import PipeNames.
Require Import PipeProto.
Require Import UEchoPipe.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S3 (pure)  THE ROUND'S CODE                                          *)
(*                                                                       *)
(*  At the end of the round the two cursors are known and the family's   *)
(*  selector is pinned by them ([wr_blk2_p]: [count_true sel = c1] and   *)
(*  [length sel = c1 + c2]).  The four combinations a pipeline round can *)
(*  end in -- and the mixed one, which the children's exclusion refutes  *)
(*  before it gets here -- are exactly the four landed codes.            *)
(* ===================================================================== *)
Definition pround_case (L R : list (bv 8)) (c1 c2 : nat) : Prop :=
  (c1 = 0%nat /\ R = L /\ c2 = length L)                       (* PRan   *)
  \/ (c1 = length dg_execL /\ c2 = 0%nat)                      (* PExecL *)
  \/ (c1 = 0%nat /\ R = dg_execR /\ c2 = length dg_execR)      (* PExecR *)
  \/ (c1 = length dg_execL /\ R = dg_execR
      /\ c2 = length dg_execR).                                (* PBoth  *)

Lemma pround_code (I : list (bv 8)) (ws : list (list (bv 8)))
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) :
  pline_at I = LPipe ws ->
  count_true sel = c1 -> length sel = (c1 + c2)%nat ->
  pround_case (wl_line (drop 1 ws)) R c1 c2 ->
  exists a : nat, pblk2_code I R sel a.
Proof using.
  intros Hl Hc Hlen Hcase.
  destruct Hcase as [(H1 & H2 & H3) | [(H1 & H2) | [(H1 & H2 & H3)
                                                   | (H1 & H2 & H3)]]].
  - exists (palt_code PRan). rewrite H2.
    apply (pblk2_code_ran I ws sel Hl); [ rewrite Hc; exact H1 | ].
    rewrite Hlen H1 H3. lia.
  - exists (palt_code PExecL).
    apply (pblk2_code_execL I ws R sel Hl); [ rewrite Hc; exact H1 | ].
    rewrite Hlen H1 H2. lia.
  - exists (palt_code PExecR). rewrite H2.
    apply (pblk2_code_execR I ws sel Hl); [ rewrite Hc; exact H1 | ].
    rewrite Hlen H1 H3. lia.
  - exists (palt_code (PBoth sel)). rewrite H2.
    apply (pblk2_code_both I ws sel Hl); [ rewrite Hc; exact H1 | ].
    rewrite Hlen H1 H3. lia.
Qed.

Section UShPipeRound2.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Notation PT := (echo_taint γ).

  (* =================================================================== *)
  (*  S1  THE ROUND'S NAMESPACE, AND THE TWO CHILDREN'S EXCLUSION         *)
  (*                                                                     *)
  (*  [PipeBoth.pblk2_cstep_L] / [_cstep_R] ask for                       *)
  (*  [Eex ⊆ ⊤ ∖ ↑uartN Uart0 ∖ ↑N] and [↑N ## ↑uartN Uart0]; the         *)
  (*  exclusion PIPE-EXEC-ECHO landed is at [Eex := ↑pipeN], so the       *)
  (*  round's own namespace has to miss BOTH the port's and the           *)
  (*  protocol's.  [blk2N] is that namespace and the two side conditions  *)
  (*  are closed facts about it.                                          *)
  (* =================================================================== *)
  Definition blk2N : namespace := nroot .@ "pipeblk2".

  Lemma blk2N_uart : (↑blk2N : coPset) ## (↑uartN Uart0 : coPset).
  Proof using . rewrite /blk2N /uartN. solve_ndisj. Qed.

  Lemma blk2N_pipeN : (↑pipeN : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑blk2N : coPset).
  Proof using . rewrite /blk2N /uartN /pipeN. solve_ndisj. Qed.


  (* =================================================================== *)
  (*  S2  THE ROUND'S ENTRY                                               *)
  (*                                                                     *)
  (*  What sh's fork lends the runcmd child is [Wcf I 3], which at the    *)
  (*  pipeline instance is [pwc_lpr2 _ _ _ 3 = pwc_blk _ _ _ 0 0]         *)
  (*  ([PipeLinkInst.pipe_inst_lcred] + [lk_lpr_S3]'s [eq_refl]); through *)
  (*  [pwc_lend_of_blk0] that IS the family at the empty selector         *)
  (*  ([PipeBoth.blk2_inv_alloc]).  The round keeps the three halves and  *)
  (*  the invariant is persistent, so every later party reads it.         *)
  (* =================================================================== *)
  Lemma pipe_round_entry (E : coPset) (I L : list (bv 8))
      (XL YR : iProp Σ) :
    pboth_line I ->
    pipe_Wcl_at g I 3%nat ={E}=∗
    ∃ (v : era_pins) (gL gR gM : gname),
      era_pin γ (S gen_id) v
      ∗ blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR
      ∗ PipeBoth.wcur gL (1/2) 0%nat
      ∗ PipeBoth.wcur gR (1/2) 0%nat
      ∗ PipeBoth.wcur gM (1/2) 0%nat.
  Proof using .
    intros Hline. rewrite /pipe_Wcl_at (pipe_inst_lcred g (S gen_id) I 3%nat).
    iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [pwc_lpr2] in *.
    iMod (blk2_inv_alloc g E blk2N (S gen_id) v I L XL YR Hline
            with "[Hc]") as (gL gR gM) "(#Hinv & HL & HR & HM)".
    { iApply (pwc_lend_of_blk0 g (S gen_id) v I 0%nat with "Hc"). }
    iModIntro. iExists v, gL, gR, gM. by iFrame "Hpin Hinv HL HR HM".
  Qed.

  (* =================================================================== *)
  (*  S4  THE ROUND'S EXIT, ON THE GOOD PATH                              *)
  (*                                                                     *)
  (*  The two waits have returned both cursor halves, so the family is    *)
  (*  recoverable ([blk2_inv_close], the DONE arm), and the block it      *)
  (*  leaves is COMPLETE and UNFILED -- which is exactly what             *)
  (*  [pwc_line2]'s third arm is for.  The caller supplies the round's    *)
  (*  code, which is a fact about the two cursors alone (S3) once the     *)
  (*  protocol reading has ruled out the mixed selector.                  *)
  (* =================================================================== *)
  Lemma pipe_round_exit (E : coPset) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ) (v : era_pins) (c1 c2 : nat) :
    Timeless XL -> Timeless YR ->
    (↑blk2N : coPset) ⊆ E ->
    (0 < c1 + c2)%nat ->
    (forall (R : list (bv 8)) (sel : list bool),
       R = L \/ R = dg_execR \/ R = alt_forkc ->
       count_true sel = c1 -> length sel = (c1 + c2)%nat ->
       exists a : nat, pblk2_code I R sel a) ->
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    PipeBoth.wcur gL (1/2) c1 -∗ PipeBoth.wcur gR (1/2) c2 ={E}=∗
    pipe_Wcl_at g I 0%nat.
  Proof using .
    intros HX HY HN Hpos Hcode. iIntros "#Hpin #Hinv HcL HcR".
    iMod (blk2_inv_close g E blk2N (S gen_id) v I L gL gR gM XL YR c1 c2
            HX HY HN with "Hinv HcL HcR") as (R sel) "[Hf %Hsrc]".
    iModIntro.
    rewrite /pipe_Wcl_at (pipe_inst_lcred g (S gen_id) I 0%nat).
    iExists v. iFrame "Hpin". cbn [pwc_lpr2].
    rewrite {1}/pwc_blk2.
    iDestruct "Hf" as "[Hf | #HT]";
      [| iApply (pwc_line2_taint g (S gen_id) v I with "HT")].
    iDestruct "Hf"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (_ & _ & _ & _ & _ & _ & Hlen & Hcnt & _ & _).
    destruct (Hcode R sel Hsrc Hcnt Hlen) as (a & Ha).
    assert (Hne : sel <> []).
    { intro Hn. rewrite Hn in Hlen. cbn [length] in Hlen. lia. }
    iApply (pwc_line2_of_blk2 g (S gen_id) v I R sel c1 c2 a Ha Hne).
    rewrite /pwc_blk2. iLeft. iExists ps, cs, P.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    by iFrame "Htn Hps Hcs Hled HE".
  Qed.

  (* =================================================================== *)
  (*  S6  THE STOP: THE TERMINAL ROUND'S EXIT PAYLOAD                     *)
  (*                                                                     *)
  (*  [UShPipeRound.sh_pipe_child_law] is                                 *)
  (*  [UkShFork.ushf_child_law_at Wcf ushq_lp 68], whose FIRST premise is *)
  (*  [ukn_pay N' = (fun _ => UkShFork.ushf_wq I)] -- so the runcmd       *)
  (*  child's exit, on EVERY arm, pays [Wcf I 3 \/ Wcf I 0].  At a round  *)
  (*  whose second [fork1] failed what the child holds is                 *)
  (*  [PipeBoth.pwc_fork_exit ... 5] (lane PIPE-STAGE-3), and the two     *)
  (*  cannot coexist: the family inside the invariant carries the         *)
  (*  writer's [turn] at the round's own position, the boundary           *)
  (*  credential carries one too, and the claim holds the authority --    *)
  (*  three halves of one [mono_nat].  So the exit payload has to be      *)
  (*  WIDENED (design SS4.3i), which moves a landed definition this lane   *)
  (*  may not move.                                                       *)
  (* =================================================================== *)

  (* [UShPipeExit.pipe_turn_three] restated (that file is not in this     *)
  (* file's cone): [EchoOut.turn] is HALF a [mono_nat] authority.         *)
  Lemma pround_turn_three (v : era_pins) (P1 P2 P3 : nat) :
    turn v P1 -∗ turn v P2 -∗ turn_auth v P3 -∗ False.
  Proof using .
    rewrite /turn /turn_auth. iIntros "H1 H2 H3".
    iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[_ <-].
    iCombine "H1 H2" as "H".
    iDestruct (mono_nat_auth_own_agree with "H H3") as %[Hq _].
    iPureIntro. rewrite ?Qp.half_half in Hq.
    exact (Qp.not_add_le_l 1%Qp (1/2)%Qp Hq).
  Qed.

  (* EVERY arm of the loop's four boundary families is a [turn] or the
     taint -- including [pwc_line2]'s new third one. *)
  Lemma pwc_lpr2_turn (k : nat) (v : era_pins) (I : list (bv 8))
      (p : nat) :
    pwc_lpr2 g k v I p -∗ (∃ P : nat, turn v P) ∨ PT.
  Proof using .
    iIntros "H". destruct p as [| [| [| p]]]; cbn [pwc_lpr2].
    - rewrite /pwc_line2. iDestruct "H" as "[H | [H | H]]".
      + rewrite /pwc_pro. iDestruct "H" as "[H | #HT]";
          [| iRight; iExact "HT"].
        iDestruct "H" as (ps cs P) "(_ & Ht & _)".
        iLeft. iExists P. iExact "Ht".
      + iDestruct "H" as (a) "[_ H]". rewrite /pwc_post /pwc_blk.
        iDestruct "H" as "[H | #HT]"; [| iRight; iExact "HT"].
        iDestruct "H" as (ps cs P) "(_ & Ht & _)".
        iLeft. iExists (P + (length (pab I a) - 2))%nat. iExact "Ht".
      + iDestruct "H" as (R sel c1 c2 a) "(_ & _ & H)".
        rewrite /pwc_blk2. iDestruct "H" as "[H | #HT]";
          [| iRight; iExact "HT"].
        iDestruct "H" as (ps cs P) "(_ & _ & Ht & _)".
        iLeft. iExists (P + c1 + c2)%nat. iExact "Ht".
    - rewrite /pwc_sp_t. iDestruct "H" as "[H | #HT]";
        [| iRight; iExact "HT"].
      iDestruct "H" as (ps cs P) "(_ & Ht & _)".
      iLeft. iExists P. iExact "Ht".
    - rewrite /pwc_open_t. iDestruct "H" as "[H | #HT]";
        [| iRight; iExact "HT"].
      iDestruct "H" as (ps cs P) "(_ & Ht & _)".
      iLeft. iExists P. iExact "Ht".
    - rewrite /pwc_blk. iDestruct "H" as "[H | #HT]";
        [| iRight; iExact "HT"].
      iDestruct "H" as (ps cs P) "(_ & Ht & _)".
      iLeft. iExists (P + 0)%nat. iExact "Ht".
  Qed.

  (* THE SHARP FORM, and the one that covers a TRADE: while ANY party
     still holds a cursor half -- the STRAY does, for ever, at a
     terminal round -- the loop's boundary credential is unreachable
     beside the family's invariant, whatever the holder gives up for it.
     [blk2_inv] is an [inv] and therefore PERSISTENT, so a process that
     ever had it has it still; the only way out is the DONE arm, and the
     outstanding half refutes that. *)
  Lemma pipe_half_not_lpr (E : coPset) (N : namespace)
      (k : nat) (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c1 p : nat)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    era_pin γ k v -∗
    blk2_inv g N k v I L gL gR gM XL YR -∗
    PipeBoth.wcur gL (1/2) c1 -∗
    pwc_lpr2 g k v I p -∗
    pecl g k ho H ={E}=∗ PT.
  Proof using .
    intros HX HY HN. iIntros "#Hpin #Hinv HcL Hlpr Hcl".
    rewrite {1}/pecl. iDestruct "Hcl" as "[#HT | Hc]";
      [by iModIntro; iExact "HT" |].
    iDestruct "Hc"
      as (v2 w so r gb pre opn)
         "(#Hpin2 & _ & _ & _ & _ & Hta & _)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (pwc_lpr2_turn k v I p with "Hlpr") as "[Hb | #HT]";
      [| by iModIntro; iExact "HT"].
    iDestruct "Hb" as (Pb) "Htb".
    iMod (inv_acc E N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_L gL gR c1 with "HcL Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1' c2') "(Hf & HgL & HgR & Hxl & Hrm)".
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hf | #HT]"; last first.
    { iMod ("Hclose" with "[HgL HgR Hxl Hrm]") as "_".
      { iNext. rewrite /blk2_body. iLeft.
        iExists R, sel, c1', c2'. iFrame "HgL HgR Hxl Hrm".
        iApply (pwc_blk2_taint g k v I R sel c1' c2' with "HT"). }
      iModIntro. iExact "HT". }
    iDestruct "Hf" as (ps cs P) "(_ & _ & Htn & _)".
    iDestruct (pround_turn_three v (P + c1' + c2')%nat Pb _
                 with "Htn Htb Hta") as %[].
  Qed.

  (* THE REFUTATION.  [p] is arbitrary: no index of the loop's boundary
     family can be handed back while the terminal round's family is
     alive, so neither arm of [ushf_wq] can. *)
  Lemma pipe_fork_exit_not_lpr (E : coPset) (N : namespace)
      (k : nat) (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c2 p : nat)
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    era_pin γ k v -∗
    pwc_fork_exit g N k v I L gL gR gM XL YR c2 -∗
    pwc_lpr2 g k v I p -∗
    pecl g k ho H ={E}=∗ PT.
  Proof using .
    intros HX HY HN. iIntros "#Hpin (#Hinv & HcR & HcM) Hlpr Hcl".
    (* the claim's authority *)
    rewrite {1}/pecl. iDestruct "Hcl" as "[#HT | Hc]";
      [by iModIntro; iExact "HT" |].
    iDestruct "Hc"
      as (v2 w so r gb pre opn)
         "(#Hpin2 & _ & _ & _ & _ & Hta & _)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    (* the boundary credential's own writer *)
    iDestruct (pwc_lpr2_turn k v I p with "Hlpr") as "[Hb | #HT]";
      [| by iModIntro; iExact "HT"].
    iDestruct "Hb" as (Pb) "Htb".
    (* ...and the family's, from inside the invariant *)
    iMod (inv_acc E N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_R gL gR c2 with "HcR Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1 c2') "(Hf & HgL & HgR & Hxl & Hrm)".
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hf | #HT]"; last first.
    { iMod ("Hclose" with "[HgL HgR Hxl Hrm]") as "_".
      { iNext. rewrite /blk2_body. iLeft.
        iExists R, sel, c1, c2'. iFrame "HgL HgR Hxl Hrm".
        iApply (pwc_blk2_taint g k v I R sel c1 c2' with "HT"). }
      iModIntro. iExact "HT". }
    iDestruct "Hf" as (ps cs P) "(_ & _ & Htn & _)".
    iDestruct (pround_turn_three v (P + c1 + c2')%nat Pb _
                 with "Htn Htb Hta") as %[].
  Qed.

  (* =================================================================== *)
  (*  S7  ...AND BACK: the round's lend RETURNED when nothing was written *)
  (*                                                                     *)
  (*  The [pipe(2)]-failed tail is paid from the SAME [Cr] the split      *)
  (*  would have turned into the family, so the family has to be          *)
  (*  reversible at the empty block: with both cursors at zero the        *)
  (*  family IS the lend again.  This is what makes the FIRST of the      *)
  (*  three panic tails payable -- and the contrast with S6 is the        *)
  (*  lane's finding: the first tail is fine because no child exists,     *)
  (*  the third is not because the stray does.                            *)
  (* =================================================================== *)
  Lemma pwc_blk2_zero_to_blk (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (a : nat) :
    pwc_blk2 g k v I R sel 0%nat 0%nat -∗ pwc_blk g k v I a 0%nat.
  Proof using .
    rewrite /pwc_blk2 /pwc_blk. iIntros "[Hf | #HT]"; last by iRight.
    iDestruct "Hf"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & _ & #HE)".
    assert (Hz : (P + 0 + 0)%nat = (P + 0)%nat) by lia.
    rewrite Hz. iLeft. iExists ps, cs, P. cbn [blkcs_p].
    iSplitR.
    { iPureIntro. split;
        [ exact (wr_blk2_p_blk ps cs I P R sel 0%nat 0%nat Hw)
        | exact Htl ]. }
    by iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pipe_round_unwind (E : coPset) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ) (v : era_pins) :
    Timeless XL -> Timeless YR ->
    (↑blk2N : coPset) ⊆ E ->
    era_pin γ (S gen_id) v -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    PipeBoth.wcur gL (1/2) 0%nat -∗ PipeBoth.wcur gR (1/2) 0%nat ={E}=∗
    pipe_Wcl_at g I 3%nat.
  Proof using .
    intros HX HY HN. iIntros "#Hpin #Hinv HcL HcR".
    iMod (blk2_inv_close g E blk2N (S gen_id) v I L gL gR gM XL YR
            0%nat 0%nat HX HY HN with "Hinv HcL HcR") as (R sel) "[Hf _]".
    iModIntro.
    rewrite /pipe_Wcl_at (pipe_inst_lcred g (S gen_id) I 3%nat).
    iExists v. iFrame "Hpin". cbn [pwc_lpr2].
    iApply (pwc_blk2_zero_to_blk (S gen_id) v I R sel 0%nat with "Hf").
  Qed.

End UShPipeRound2.

(* ===================================================================== *)
(*  S5  THE ENTRY PAYMENT'S FRAME IS SEPARABLE                           *)
(*                                                                       *)
(*  [UEchoPipe.ep_pay Wq pn gp L] is [pipe_inv * (side_L pn * Wq) *       *)
(*  wcur pn 0 * pws_lb pn []] -- the era's console credential [Wq] sits   *)
(*  BESIDE the protocol's handle and nothing reads it.  So the           *)
(*  [pipe(2)] registrar may be run at [Wq := emp] and the left cursor    *)
(*  half joined to its result at the arm's own split, which is the only  *)
(*  order in which BOTH the [pipe(2)]-failed tail and echo's exec are    *)
(*  payable: [UkShPipe.ush_pipe_ans]'s -1 arm returns NOTHING of the     *)
(*  registrar, so a [Wq] that carried [wcur gL (1/2) 0] would be lost at *)
(*  a [pipe(2)] failure and S7's unwind could not run.                   *)
(* ===================================================================== *)
Section UShPipeRound2Pay.
  Context {Σ : gFunctors}.
  Context `{!riscvGS Σ, !xv6G Σ, !pipeProtoG Σ}.

  Lemma ep_pay_frame (Wq : iProp Σ) (pn : pnames) (gp : pipe_names)
      (L : list (bv 8)) :
    (UEchoPipe.ep_pay emp%I pn gp L ∗ Wq) ⊣⊢ UEchoPipe.ep_pay Wq pn gp L.
  Proof using .
    rewrite /UEchoPipe.ep_pay /UEchoPipe.ep_frame.
    iSplit.
    - iIntros "((#Hinv & [HL _] & Hw & Hlb) & HQ)".
      iFrame "Hinv HL HQ Hw Hlb".
    - iIntros "(#Hinv & [HL HQ] & Hw & Hlb)".
      iFrame "Hinv HL HQ Hw Hlb".
  Qed.

End UShPipeRound2Pay.

(* ===================================================================== *)
(*  S8  WHY ROUTE (γ) CANNOT BE TAKEN (lane SH-PIPE-ROUND-5 part 4;       *)
(*  design SS4.3l, and its own pre-authorised fallback condition).        *)
(*                                                                       *)
(*  SS4.3l would FREEZE the claim's resolution authority at the terminal   *)
(*  round ([PipeOut.cs_freeze], landed beside it: the mechanism works).   *)
(*  For [PipeOut.pecl] to CARRY the frozen authority, no landed claim     *)
(*  step that can still fire at a terminal round may GROW [cs].  Two do:  *)
(*  [PipeOut.pecl_step_write_blk] and [PipeOut.pecl_blk2_file].  Both are *)
(*  applicable at a terminal round's state, and the witness is            *)
(*  PIPE-MODEL-3's own ([PipeDisc.d4_ambiguous_bytes]): at                *)
(*  `echo fork | cat' the fork-failure round and the GOOD round print the *)
(*  same bytes, so the block the terminal round has written is also the   *)
(*  block a NON-TERMINAL alternative owes -- and [pecl_blk2_file]'s four  *)
(*  pure premises are then all met at that alternative.  A claim that had *)
(*  frozen [cs] could not answer it, so [pecl] must keep [cs_auth] at     *)
(*  fraction 1 at a terminal round and route (γ) fails.                   *)
(* ===================================================================== *)
Lemma pterm_gamma_witness (pre0 : list (bv 8)) :
  pcont (LPipe pd_ws3) (PForkS sel_forkc) = (pre0 ++ u_prompt)%list ->
  palt_ok (LPipe pd_ws3) PRan
  /\ palt_panic PRan = false
  /\ palt_isforkS PRan = false
  /\ pcont (LPipe pd_ws3) PRan = (pre0 ++ u_prompt)%list.
Proof using.
  intro Hc. split_and!.
  - apply palt_ok_LPipe_ran.
  - exact palt_panic_ran.
  - reflexivity.
  - rewrite d4_ambiguous_bytes. exact Hc.
Qed.
