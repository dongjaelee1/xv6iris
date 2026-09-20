(* ===================================================================== *)
(*  PipeForkGap.v -- THE MODEL HAS NO ALTERNATIVE FOR WHAT THE MACHINE   *)
(*  CAN PRINT WHEN sh's SECOND [fork1] PANICS WHILE THE FIRST CHILD'S    *)
(*  EXEC HAS FAILED (lane SH-PIPE-ROUND-4, finding H4).                  *)
(*                                                                       *)
(*  THE BEHAVIOUR.  [runcmd]'s PIPE arm forks twice.  If [fork1] #1       *)
(*  succeeds and [fork1] #2 fails, the runcmd child panics -- [panic]     *)
(*  prints `fork\n' on fd 2 and exits -- while child #1 is alive.  If     *)
(*  child #1's [exec] of /echo fails it prints `exec echo failed\n' on    *)
(*  fd 2, one byte per [write], CONCURRENTLY.  Both alternatives exist in *)
(*  the model ([PFork] and [PExecL]) and a round files exactly ONE code,  *)
(*  so the wire that carries bytes of BOTH has to be some admissible      *)
(*  alternative's continuation.                                          *)
(*                                                                       *)
(*  IT WAS NOT, AND NOW IT IS (lane PIPE-MODEL-3, design section 4.3h).   *)
(*  [pfork_execL_gap] used to refute the SHORTEST witness -- the          *)
(*  interleaving whose first byte is the PANIC's and whose second is the  *)
(*  left child's -- against EVERY alternative an [LPipe] line admitted.   *)
(*  The model now HAS that alternative, [PForkS], so the old theorem is   *)
(*  FALSE BY DESIGN and is replaced by two: [pfork_execL_admitted] (the   *)
(*  two-byte wire IS a prefix of [pcont (LPipe gap_ws) (PForkS            *)
(*  [false; true])]) and [pfork_execL_only_forkS] (NO OTHER alternative   *)
(*  admits it -- the seven refutations below are kept verbatim and are    *)
(*  what says the new arm is not slack).  The selector is [false; true]   *)
(*  and not the design's [true; false]: [true] takes the STRAY's byte     *)
(*  ([dg_execL]) and [false] takes [alt_forkc]'s, the way the stage's     *)
(*  landed [PipeBothPure.pend2 R sel = pmerge sel dg_execL R] reads them, *)
(*  and the panic's byte is on the wire first.                            *)
(*                                                                       *)
(*  AT ONE LINE, not at every line, and deliberately: at a line whose     *)
(*  own text begins with `ef' the [PRan] arm would carry those two bytes  *)
(*  and the refutation would be about the OTHER seven arms only.  The     *)
(*  finding is that the model admits a round the machine can contradict,  *)
(*  and one line is enough to have it.                                    *)
(*                                                                       *)
(*  NOTHING IN THE TREE IMPORTS THIS FILE.                                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import PipeBothPure.
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
(* THE WITNESS, WHICH IS WHAT THE MODEL CHANGE IS FOR: the two-byte wire
   the machine can produce at that round IS a prefix of the terminal
   round's continuation -- one [false] (the runcmd child's `f') and one
   [true] (the stray's `e'). *)
Theorem pfork_execL_admitted :
  palt_ok (LPipe gap_ws) (PForkS [false; true])
  /\ [gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) (PForkS [false; true]).
Proof using.
  split.
  - cbn [palt_ok]. split_and!;
      [discriminate | vm_compute; lia | vm_compute; lia].
  - apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ...AND NOTHING ELSE ADMITS IT, which is the old [pfork_execL_gap]
   restated: the arm the model gained is exactly the arm the machine
   needs, and not one alternative more. *)
Theorem pfork_execL_only_forkS (a : palt) :
  palt_ok (LPipe gap_ws) a ->
  [gap_b0; gap_b1] `prefix_of` pcont (LPipe gap_ws) a ->
  palt_isforkS a = true.
Proof using.
  destruct a as [k | | | | sel | | sel | ].
  - intros Hk. cbn [palt_ok] in Hk. subst k.
    intro H. by destruct (gap_not_echo3 H).
  - intros _ H. by destruct (gap_not_ran H).
  - intros _ H. by destruct (gap_not_execL H).
  - intros _ H. by destruct (gap_not_execR H).
  - intros Hok H. by destruct (gap_not_both sel Hok H).
  - intros _ H. by destruct (gap_not_pipe H).
  - intros _ _. reflexivity.
  - intros _ H. by destruct (gap_not_silent H).
Qed.

(* ===================================================================== *)
(*  THE SECOND GAP, in the same file because it is the same shape:        *)
(*  DESIGN 4.3f (R2) OMITS THE TWO CHILDREN'S EXCLUSION.                  *)
(*                                                                       *)
(*  The witness every byte step of [PipeBoth]'s family spends is          *)
(*  [pblk2_wit I R sel] -- `some admissible, non-panicking alternative of *)
(*  the round's line has [pend2 R sel] as a prefix`.  The ruling makes    *)
(*  [R] EXISTENTIAL in [blk2_inv] and pins it by the right child's mode,  *)
(*  so at mode 1 ([R] = the LINE, cat printing what it read) the LEFT     *)
(*  child's step would have to spend the witness at a selector with a     *)
(*  [true] bit AND a [false] one.  It is FALSE there: the block would     *)
(*  begin with a byte of [dg_execL] and continue with a byte of the LINE, *)
(*  and no alternative of an [LPipe] line has that continuation.          *)
(*                                                                       *)
(*  Which is why [PipeBoth]'s [pblk2_cstep_L] / [pblk2_cstep_R] carry an  *)
(*  EXCLUSION premise the ruling does not mention.  The theorem below is  *)
(*  [pblk2_wit]'s body, spelled out (it names only [PipeDisc] and         *)
(*  [PipeBothPure], so this file stays out of the Iris cone).             *)
(* ===================================================================== *)
Definition gap_L : list (bv 8) := wl_line (drop 1 gap_ws).   (* `hello<nl>' *)

Lemma gap_pend2_mixed :
  pend2 gap_L [true; false] = [dg_execL !!! 0%nat; gap_L !!! 0%nat].
Proof using. vm_compute. reflexivity. Qed.

Notation mixp := ([dg_execL !!! 0%nat; gap_L !!! 0%nat]).

Lemma mix_not_ran : ~ (mixp `prefix_of` pcont (LPipe gap_ws) PRan).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma mix_not_execL : ~ (mixp `prefix_of` pcont (LPipe gap_ws) PExecL).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma mix_not_execR : ~ (mixp `prefix_of` pcont (LPipe gap_ws) PExecR).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma mix_not_pipe : ~ (mixp `prefix_of` pcont (LPipe gap_ws) PPipe).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma mix_not_forkc : ~ (mixp `prefix_of` alt_forkc).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma mix_not_silent : ~ (mixp `prefix_of` pcont (LPipe gap_ws) PSilent).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dgL_cons2 : exists dl : list (bv 8),
    dg_execL = dg_execL !!! 0%nat :: dg_execL !!! 1%nat :: dl.
Proof using. exists (drop 2 dg_execL). vm_compute. reflexivity. Qed.

Lemma dgR_cons2 : exists dr : list (bv 8),
    dg_execR = dg_execL !!! 0%nat :: dg_execL !!! 1%nat :: dr.
Proof using. exists (drop 2 dg_execR). vm_compute. reflexivity. Qed.

Lemma gapL0_ne_0 : gap_L !!! 0%nat <> dg_execL !!! 0%nat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma gapL0_ne_1 : gap_L !!! 0%nat <> dg_execL !!! 1%nat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma gap_both_len2 : (2 <= length dg_execL + length dg_execR)%nat.
Proof using. vm_compute. lia. Qed.

Lemma fc_cons2 : exists dz : list (bv 8),
    alt_forkc = alt_forkc !!! 0%nat :: alt_forkc !!! 1%nat :: dz.
Proof using. exists (drop 2 alt_forkc). vm_compute. reflexivity. Qed.

Lemma gapL0_ne_f0 : gap_L !!! 0%nat <> alt_forkc !!! 0%nat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.
Lemma gapL0_ne_f1 : gap_L !!! 0%nat <> alt_forkc !!! 1%nat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* the terminal round's arm: its two sources are [dg_execL] and
   [alt_forkc], so the LINE's first byte is never its second one *)
Lemma mix_not_forkS (sel : list bool) :
  palt_ok (LPipe gap_ws) (PForkS sel) ->
  ~ (mixp `prefix_of` pcont (LPipe gap_ws) (PForkS sel)).
Proof using.
  intros (Hne & H1 & H2) Hpre.
  destruct dgL_cons2 as [dl HL]. destruct fc_cons2 as [dz HF].
  destruct sel as [| u [| w s]].
  - by destruct (Hne eq_refl).
  - exfalso. apply prefix_length in Hpre.
    rewrite /pcont (pmerge_length [u] dg_execL alt_forkc H1 H2) in Hpre.
    cbn [length] in Hpre. lia.
  - cbn [pcont] in Hpre. rewrite HL in Hpre. rewrite HF in Hpre.
    destruct u; destruct w;
      rewrite ?pmerge_true_cons, ?pmerge_false_cons in Hpre;
      cbn [app] in Hpre;
      apply prefix_cons_inv_2 in Hpre;
      apply prefix_cons_inv_1 in Hpre;
      first [ exact (gapL0_ne_0 Hpre) | exact (gapL0_ne_1 Hpre)
            | exact (gapL0_ne_f0 Hpre) | exact (gapL0_ne_f1 Hpre) ].
Qed.

Lemma mix_not_both (sel : list bool) :
  palt_ok (LPipe gap_ws) (PBoth sel) ->
  ~ (mixp `prefix_of` pcont (LPipe gap_ws) (PBoth sel)).
Proof using.
  intros [Hlen Hcnt] Hpre.
  assert (Hge : (2 <= length sel)%nat)
    by (rewrite Hlen; exact gap_both_len2).
  destruct dgL_cons2 as [dl HL]. destruct dgR_cons2 as [dr HR].
  destruct sel as [| u [| w s]];
    [ cbn [length] in Hge; lia | cbn [length] in Hge; lia | ].
  cbn [pcont] in Hpre. rewrite HL in Hpre. rewrite HR in Hpre.
  destruct u; destruct w;
    rewrite ?pmerge_true_cons, ?pmerge_false_cons in Hpre;
    cbn [app] in Hpre;
    apply prefix_cons_inv_2 in Hpre;
    apply prefix_cons_inv_1 in Hpre;
    first [ exact (gapL0_ne_0 Hpre) | exact (gapL0_ne_1 Hpre) ].
Qed.

(* [pblk2_wit I gap_L [true; false]] at an [I] whose last body is this
   line, spelled out: FALSE. *)
Theorem gap_mixed_no_wit :
  ~ (exists a : nat,
       palt_ok (LPipe gap_ws) (palt_of a)
       /\ palt_panic (palt_of a) = false
       /\ pend2 gap_L [true; false]
            `prefix_of` pcont (LPipe gap_ws) (palt_of a)).
Proof using.
  intros [a (Hok & Hpan & Hpre)].
  rewrite gap_pend2_mixed in Hpre.
  revert Hok Hpan Hpre. generalize (palt_of a). intros al Hok Hpan Hpre.
  destruct al as [k | | | | sel | | sel | ].
  - cbn [palt_ok] in Hok. subst k. vm_compute in Hpan. discriminate Hpan.
  - exact (mix_not_ran Hpre).
  - exact (mix_not_execL Hpre).
  - exact (mix_not_execR Hpre).
  - exact (mix_not_both sel Hok Hpre).
  - exact (mix_not_pipe Hpre).
  - exact (mix_not_forkS sel Hok Hpre).
  - exact (mix_not_silent Hpre).
Qed.
