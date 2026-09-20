(* ===================================================================== *)
(*  PipeForkGap.v -- THE MODEL HAS NO ALTERNATIVE FOR WHAT THE MACHINE   *)
(*  CAN PRINT WHEN sh's SECOND [fork1] PANICS WHILE THE FIRST CHILD'S    *)
(*  EXEC HAS FAILED (lane SH-PIPE-ROUND-4, finding H4).                  *)
(*                                                                       *)
(*  THE BEHAVIOUR.  [runcmd]'s PIPE arm forks twice.  If [fork1] #1       *)
(*  succeeds and [fork1] #2 fails, the runcmd child panics -- [panic]     *)
(*  prints "fork\n" on fd 2 and exits -- while child #1 is alive.  If     *)
(*  child #1's [exec] of /echo fails it prints "exec echo failed\n" on    *)
(*  fd 2, one byte per [write], CONCURRENTLY.  Both alternatives exist in *)
(*  the model ([PFork] and [PExecL]) and a round files exactly ONE code,  *)
(*  so the wire that carries bytes of BOTH has to be some admissible      *)
(*  alternative's continuation.                                          *)
(*                                                                       *)
(*  IT IS NOT.  The theorem below takes the SHORTEST witness -- the       *)
(*  interleaving whose first byte is the PANIC's and whose second is the  *)
(*  left child's -- and refutes it against EVERY alternative an           *)
(*  [LPipe] line admits, [PBoth] included (whose merge is of [dg_execL]   *)
(*  with [dg_execR] and never with [alt_panic]).                          *)
(*                                                                       *)
(*  AT ONE LINE, not at every line, and deliberately: at a line whose     *)
(*  own text begins with `ef' the [PRan] arm would carry those two bytes  *)
(*  and the refutation would be about the OTHER seven arms only.  The     *)
(*  finding is that the model admits a round the machine can contradict,  *)
(*  and one line is enough to have it.                                    *)
(*                                                                       *)
(*  WHAT IT DOES NOT SAY.  It does not say the pipeline theorem is false: *)
(*  that depends on whether a failing [exec] of /echo is reachable under  *)
(*  the claim's pin (the echo application treats it as reachable, which   *)
(*  is why [PExecL] exists at all).  The three ways out are in the lane   *)
(*  report; NOTHING in the tree imports this file.                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Local Open Scope list_scope.

(* the line: `echo hello | cat' *)
Definition gap_ws : list (list (bv 8)) := [cmd_echo; sb "hello"%string].

(* THE WITNESS: the panic's first byte, then the left child's first byte
   -- the interleaving in which the runcmd child's [panic("fork")] gets
   the port before child 1's [fprintf(2, "exec %s failed\n", ...)] does. *)
Definition gap_b0 : bv 8 := alt_panic !!! 0%nat.     (* `f' *)
Definition gap_b1 : bv 8 := dg_execL !!! 0%nat.      (* `e' *)

(* ---- the seven arms whose continuation is a CONSTANT list ---- *)
Lemma gap_not_echo3 :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) (PEcho 3%nat)).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_not_ran :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) PRan).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_not_execL :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) PExecL).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_not_execR :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) PExecR).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_not_pipe :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) PPipe).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_not_fork :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) PFork).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_not_silent :
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) PSilent).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- ...AND THE MERGE ARM, whose two sources BOTH begin `e' ---- *)
Lemma dgL_cons1 : exists dl : list (bv 8),
    dg_execL = dg_execL !!! 0%nat :: dl.
Proof using. exists (drop 1 dg_execL). vm_compute. reflexivity. Qed.

Lemma dgR_cons1 : exists dr : list (bv 8),
    dg_execR = dg_execL !!! 0%nat :: dr.
Proof using. exists (drop 1 dg_execR). vm_compute. reflexivity. Qed.

Lemma gap_b0_ne : gap_b0 <> dg_execL !!! 0%nat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_both_len : (1 <= length dg_execL + length dg_execR)%nat.
Proof using. vm_compute. lia. Qed.

Lemma gap_not_both (sel : list bool) :
  palt_ok (LPipe gap_ws) (PBoth sel) ->
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) (PBoth sel)).
Proof using.
  intros [Hlen Hcnt] Hpre.
  assert (Hge : (1 <= length sel)%nat)
    by (rewrite Hlen; exact gap_both_len).
  destruct dgL_cons1 as [dl HL]. destruct dgR_cons1 as [dr HR].
  destruct sel as [| u s]; [ cbn [length] in Hge; lia | ].
  cbn [pcont] in Hpre. rewrite HL in Hpre. rewrite HR in Hpre.
  destruct u;
    [ rewrite pmerge_true_cons in Hpre | rewrite pmerge_false_cons in Hpre ];
    cbn [app] in Hpre;
    exact (gap_b0_ne (prefix_cons_inv_1 _ _ _ _ Hpre)).
Qed.

(* ===================================================================== *)
(*  THE REFUTATION                                                        *)
(* ===================================================================== *)
Theorem pfork_execL_gap (a : palt) :
  palt_ok (LPipe gap_ws) a ->
  ~ ([gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) a).
Proof using.
  destruct a as [k | | | | sel | | | ].
  - intros Hk. cbn [palt_ok] in Hk. subst k. exact gap_not_echo3.
  - intros _. exact gap_not_ran.
  - intros _. exact gap_not_execL.
  - intros _. exact gap_not_execR.
  - exact (gap_not_both sel).
  - intros _. exact gap_not_pipe.
  - intros _. exact gap_not_fork.
  - intros _. exact gap_not_silent.
Qed.
