(* ===================================================================== *)
(*  UkShPipeFork.v -- THE PIPE ERA'S FORK RE-ENTRY: the child law's      *)
(*  TERMINAL PAYLOAD, and the reduction of design SS4.3i's re-entry to   *)
(*  ONE obligation (lane SH-PIPE-ROUND-5 part 2; design SS4.3i/SS4.3j).  *)
(*                                                                       *)
(*  WHAT SS4.3j ASKS FOR is a pipe-specific twin of                      *)
(*  [UkShFork.wp_kshm_body_at] / [wp_kshf_fork_at] whose child payload   *)
(*  carries the terminal round and whose re-entry, at that arm, writes    *)
(*  the prompt with [PipeBoth.pprompt_dollar_fork] /                      *)
(*  [pprompt_space_fork] and then enters [getcmd]'s read.                 *)
(*                                                                       *)
(*  WHAT THIS FILE MEASURES, and it is the lane's finding: THAT RE-ENTRY  *)
(*  NEEDS NO NEW LOOP WALK.  [UkSh]'s command loop is GENERIC in the      *)
(*  era's write credential [Wc] -- the whole of it reads [Wc] through     *)
(*  exactly four section hypotheses ([ush_wb_wc], [ush_wc_blk_line],      *)
(*  [ush_wc_read]) and one resource ([ush_prompt_law]) -- so the terminal *)
(*  arm is the SAME walk at a WIDENED credential                          *)
(*                                                                       *)
(*     pterm_wc I p := Wcf I p \/ (p < 3 /\ the terminal round at 5 + p)  *)
(*                                                                       *)
(*  which is EQUAL to [Wcf] at index 3 -- the only index the body of the  *)
(*  loop ever sees ([UkSh.ush_posw] is stated at [ush_wcp _ _ _ _ 3]).    *)
(*  So the body, the fork arm and the child law transfer for free (S2),   *)
(*  the three pure [Wc] laws transfer for free (S1), and TWO obligations  *)
(*  remain:                                                              *)
(*                                                                       *)
(*   (A) [pterm_prompt_arm]: the prompt's two bytes at the terminal arm,  *)
(*       which is exactly [pprompt_dollar_fork] then [pprompt_space_fork] *)
(*       (positions 5 and 6 of [alt_forkc]) packaged as [UkSh.ksh_w];     *)
(*       PIPE-STAGE-3 landed both steps and what is left is the [ksh_w]   *)
(*       plumbing [UShPanic]'s prompt law already does at the other arm.  *)
(*                                                                       *)
(*   (B) [pterm_read_law] -- THE LEAF, and the STOP rule's:               *)
(*                                                                       *)
(*         forall I l, wl_nl `notin` l ->                                 *)
(*           Pm (I ++ l ++ [wl_nl]) -* pterm_shape I 7 -*                 *)
(*           Pm (I ++ l ++ [wl_nl]) * echo_taint (pgn_cl g)               *)
(*                                                                       *)
(*       `if a line is EVER read after a terminal round, the era is       *)
(*       tainted` -- design SS4.3i's dirty credential, which is D4 read   *)
(*       at the resource level (a fork-failure round is the last round of *)
(*       the covered session, so the next line's bytes cannot be          *)
(*       disciplined).  With it, [ush_wc_read] at [pterm_wc] is one line  *)
(*       ([PipeLinkInst.pipe_Hcltaint]) and the terminal re-entry is two  *)
(*       instructions, [UkSh.wp_ksh_getcmd] at [pterm_wc], and the LANDED *)
(*       body at [Wcf] -- because after the read the credential is        *)
(*       [Wcf I' 3] again.  Without it the re-entry has no continuation.  *)
(*       S3 states it and reduces [ush_wc_read] to it.                    *)
(*                                                                       *)
(*  (B) IS DISCHARGED (lane PIPE-STAGE-4, design SS4.3m as amended):      *)
(*  [pterm_shape] carries the round's FROZEN resolution, which is the one *)
(*  non-monotone reading a read site can hold, and the read residue       *)
(*  inside [Pm] carries a LONGER lower bound of the same list.            *)
(*  [pterm_read_law_of] below is that, at one premise about [Pm] -- the   *)
(*  era's own [UShLine.ush_mid_at] hands out [PipeLinksLine.pwc_rres].    *)
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
Require Import PipeDisc.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeBoth.
Require Import PipeLinkInst.
Require Import UShPipeRound2.     (* [blk2N] and its two mask facts *)
Require Import FdSlots UserFd.
Require Import UkRun.
Require Import UkSh.
Require Import UkShFork.
Require Import Xv6G.         (* the backtick-[Context] trap: name the class *)
Require Import IrefSlots ProcAvail FileInvDefs.
Require Import ConsoleInv.   (* [CONSOLE] *)
Require Import UCodeShK.     (* [shk_rodata] *)
Require Import UShPanic.     (* [prompt_step] / [ksh_w_of_link_prompt_fam] *)
Require Import RiscvPtsto.
Require Import WpUart.
Require Import UexecExecInst.  (* [uprogSG_free] -- the era's ARM instance; the
                                 two-instances wedge, durable-notes *)
Require Import CtxIdDefs.
Local Open Scope list_scope.

Section UkShPipeFork.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  (* [UkSh.ush_posb]'s position ghost ([Xv6Cameras.uartGhostG]); the name
     IS in scope through [UkSh], so the backtick generalisation binds the
     class and does not invent one (durable-notes' [Context] trap). *)
  Context `{!uartGhostG Σ}.

  Local Notation T := (echo_taint γ).
  Local Notation Wcf := (pipe_Wcl_at g).
  Local Notation Wbf := (pipe_Wbl_at g).

  (* =================================================================== *)
  (*  S1  THE TERMINAL SHAPE, THE CHILD LAW'S PAYLOAD, AND THE WIDENED    *)
  (*      CREDENTIAL                                                      *)
  (* =================================================================== *)

  (* PIPE-STAGE-3's second shape, with everything the round chose bound
     existentially and the two [Timeless] side conditions riding inside
     (design SS4.3j: `the existential's exact shape is the lane's').  The
     namespace is NOT existential: it is this campaign's [blk2N], whose
     two mask facts are closed ([blk2N_uart], [blk2N_pipeN]), and an
     existential one would put a [coPset] disjointness under the binder
     at every use. *)
  (* ...AND THE THIRD PURE CONJUNCT (lane SH-PIPE-ROUND-6, obligation
     (A)): the round's line IS a pipeline line.  The two terminal prompt
     steps ([PipeBoth.pprompt_dollar_fork] / [pprompt_space_fork]) ask
     for [forall sel, sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc
     sel], which is FREE at an [LPipe] line ([PipeBoth.pblk2_wit_t_forkc])
     and at no other; the shape has to carry it because [UkSh.
     ush_prompt_law] quantifies over EVERY input [I] and the loop knows
     nothing about the round's line. *)
  (* ...AND THE ERA'S DELIVERED INPUT AT THE BOUNDARY (lane
     SH-PIPE-ROUND-7 part 2; design SS4.3p (a)).  [inp_lb v I] is
     PERSISTENT and the round has it -- it forks on a line it has just
     read -- and without it the widened credential cannot discharge
     [UShLine.ush_wc_inp], which is a PURE entailment and so cannot open
     [blk2_inv] to find the input fact inside.  That law is the ONE of
     [UInitSh.cons_cred_holds_at]'s ten that does not transfer for free
     when [UInitPipe.pipe_cc]'s [cc_wc] becomes [pterm_wc]; this conjunct
     is what pays it ([pterm_wc_inp_of] below). *)
  Definition pterm_shape (I : list (bv 8)) (c2 : nat) : iProp Σ :=
    (∃ (v : era_pins) (L : list (bv 8)) (gL gR gM : gname)
       (XL YR : iProp Σ),
       ⌜Timeless XL /\ Timeless YR /\ pboth_line I⌝
       ∗ era_pin γ (S gen_id) v
       ∗ inp_lb v I
       ∗ pwc_fork_exit g blk2N (S gen_id) v I L gL gR gM XL YR c2)%I.

  (* ...AND THE PIPE LINE'S CHILD EXIT PAYLOAD (design SS4.3j (1)).  The
     runcmd child exits either as upstream's child does -- the block owed
     or the boundary ([UkShFork.ushf_wq]) -- or at a round whose second
     [fork1] failed, holding the family, the right cursor at 5 (the five
     bytes of `fork\n' it wrote itself) and the mode half at 3. *)
  Definition pterm_pay (I : list (bv 8)) : iProp Σ :=
    (UkShFork.ushf_wq Wcf I ∨ pterm_shape I 5%nat)%I.

  Lemma pterm_pay_of_wq (I : list (bv 8)) :
    UkShFork.ushf_wq Wcf I -∗ pterm_pay I.
  Proof using . iIntros "H". rewrite /pterm_pay. by iLeft. Qed.

  Lemma pterm_pay_of_shape (I : list (bv 8)) :
    pterm_shape I 5%nat -∗ pterm_pay I.
  Proof using . iIntros "H". rewrite /pterm_pay. by iRight. Qed.

  (* the pin is PERSISTENT and the shape carries it, which is what the
     taint arm of the read law below reads off it *)
  Lemma pterm_shape_pin (I : list (bv 8)) (c2 : nat) :
    pterm_shape I c2 -∗
    (∃ v : era_pins, era_pin γ (S gen_id) v) ∗ pterm_shape I c2.
  Proof using .
    rewrite /pterm_shape. iIntros "H".
    iDestruct "H" as (v L gL gR gM XL YR) "(%Htl & #Hpin & #Hlb & Hfe)".
    iSplitR; [ by iExists v; iFrame "Hpin" | ].
    iExists v, L, gL, gR, gM, XL, YR. iSplitR; [ by iPureIntro | ].
    by iFrame "Hpin Hlb Hfe".
  Qed.

  (* a KILLED child pays the payload with the taint, exactly as
     [UkShFork.ushf_kill_law] asks -- at the era's pin, as
     [UShPipeRound.pipe_kill_law] takes it *)
  Lemma pterm_pay_taint (v : era_pins) (I : list (bv 8)) :
    era_pin γ (S gen_id) v -∗ T -∗ pterm_pay I.
  Proof using .
    iIntros "#Hpin #HT". iApply pterm_pay_of_wq.
    rewrite /UkShFork.ushf_wq. iRight.
    iApply (pipe_Hcltaint g I 0%nat v with "Hpin HT").
  Qed.

  (* THE WIDENED CREDENTIAL.  [p] is how many PROMPT bytes are out, and
     the terminal round's right cursor stands at [5 + p]: 5 is the
     runcmd child's `fork\n', 6 is the main loop's `$' and 7 its space
     ([PipeBoth.alt_forkc_dollar] / [alt_forkc_space]).  The guard
     [p < 3] is what makes the widening INVISIBLE to the loop's body. *)
  Definition pterm_wc (I : list (bv 8)) (p : nat) : iProp Σ :=
    (Wcf I p ∨ (⌜(p < 3)%nat⌝ ∗ pterm_shape I (5 + p)%nat))%I.

  Lemma pterm_wc_of (I : list (bv 8)) (p : nat) : Wcf I p -∗ pterm_wc I p.
  Proof using . iIntros "H". rewrite /pterm_wc. by iLeft. Qed.

  (* ---- AT INDEX 3 THE WIDENING COLLAPSES, and that is the whole
          reason the body transfers ---- *)
  Lemma pterm_wc_3 (I : list (bv 8)) : pterm_wc I 3%nat -∗ Wcf I 3%nat.
  Proof using .
    rewrite /pterm_wc. iIntros "[H | [%Hlt _]]"; [ iExact "H" | lia ].
  Qed.

  (* ---- ...AND THE CHILD LAW'S PAYLOAD AT THE WIDENED CREDENTIAL IS
          EXACTLY [pterm_pay], so SS4.3j (1)'s REDEFINITION NEEDS NO NEW
          DEFINITION: [UkShFork.ushf_child_law_at] AT [pterm_wc] already
          IS the twin the ruling asks for (lane SH-PIPE-ROUND-6).  What
          it also needs -- and what this lane REFUTES -- is
          [UkShFork]'s [HWct], i.e. [Timeless (pterm_wc I p)]; see S5. ---- *)
  Lemma pterm_wq_pay (I : list (bv 8)) :
    UkShFork.ushf_wq pterm_wc I ⊣⊢ pterm_pay I.
  Proof using .
    rewrite /pterm_pay /UkShFork.ushf_wq /pterm_wc. iSplit.
    - iIntros "[[H | [%Hlt _]] | [H | [_ H]]]".
      + iLeft. by iLeft.
      + exfalso. lia.
      + iLeft. by iRight.
      + iRight. rewrite Nat.add_0_r. iExact "H".
    - iIntros "[[H | H] | H]".
      + iLeft. by iLeft.
      + iRight. by iLeft.
      + iRight. iRight. iSplitR; [ iPureIntro; lia | ].
        rewrite Nat.add_0_r. iExact "H".
  Qed.

  (* ---- [UkSh]'s three pure [Wc] laws, at the widened credential ---- *)
  Lemma pterm_wb_wc (I : list (bv 8)) : ⊢ Wbf I -∗ pterm_wc I 0%nat.
  Proof using .
    iIntros "H". iApply pterm_wc_of. iApply (pipe_Hwbwc g I with "H").
  Qed.

  Lemma pterm_wc_blk_line (I : list (bv 8)) :
    ⊢ pterm_wc I 3%nat -∗ pterm_wc I 0%nat.
  Proof using .
    iIntros "H". iApply pterm_wc_of.
    iApply (pipe_Hwbl g I with "[H]"). iApply (pterm_wc_3 I with "H").
  Qed.

  (* =================================================================== *)
  (*  S2  THE LOOP'S STATE TRANSFERS, BOTH WAYS                           *)
  (*                                                                     *)
  (*  [UkSh.ush_wcp] is the only place the loop reads [Wc], and           *)
  (*  [ush_posw] -- the BODY's state -- names it at index 3 ALONE.  So    *)
  (*  the body's state transfers from the widened credential to the       *)
  (*  landed one, and the HEAD's state (index 0) transfers the other way. *)
  (* =================================================================== *)
  Lemma pterm_wcp_3 (l : list fdstate) (I : list (bv 8)) :
    UkSh.ush_wcp pterm_wc Wbf l I 3%nat -∗ UkSh.ush_wcp Wcf Wbf l I 3%nat.
  Proof using .
    rewrite /UkSh.ush_wcp. iIntros "[[%Hrow Hc] | [%Hcl Hb]]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iApply (pterm_wc_3 I with "Hc").
    - exfalso. destruct Hcl as [_ Hlt]. lia.
  Qed.

  Lemma pterm_wcp_of (l : list fdstate) (I : list (bv 8)) (p : nat) :
    UkSh.ush_wcp Wcf Wbf l I p -∗ UkSh.ush_wcp pterm_wc Wbf l I p.
  Proof using .
    rewrite /UkSh.ush_wcp. iIntros "[[%Hrow Hc] | [%Hcl Hb]]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iApply (pterm_wc_of I p with "Hc").
    - iRight. iFrame "Hb". by iPureIntro.
  Qed.

  (* =================================================================== *)
  (*  S2b  THE ERA-LEVEL READING OF THE WIDENED CREDENTIAL, AND THE ONE    *)
  (*       CONJUNCT THE TERMINAL SHAPE STILL OWES IT (lane                 *)
  (*       SH-PIPE-ROUND-7, finding (3)).                                  *)
  (*                                                                       *)
  (*  The lane's finding is that the terminal round can only ever reach    *)
  (*  the prompt inside the LOOP'S OWN credential -- the parent's only     *)
  (*  continuation at 0x938 is [UkShLoop.ushl_head], and [getcmd] is out   *)
  (*  of reach of a body law ([UkSh.wp_ksh_getcmd] spends                  *)
  (*  [UkSh.ush_read_leaf], which needs the era's [ukn_pay N =             *)
  (*  ucons_pay ...] equation, and [UkSh.ush_rest_l_at] carries only       *)
  (*  [ukn_const N]).  So the era's own credential -- [UInitPipe.pipe_cc]'s*)
  (*  [cc_wc] field -- has to BE [pterm_wc], and the ten laws of           *)
  (*  [UInitSh.cons_cred_holds_at] have to hold at it.  Measured: five of  *)
  (*  them mention [Wc] and FOUR are landed above ([pterm_wb_wc] (6),      *)
  (*  [pterm_wc_blk_line] (7), [pterm_wc_read_of] (5), [pterm_wc_of] with  *)
  (*  [UInitPipe.pipe_wp_line] (10), and (9) is                            *)
  (*  [UShLine.ush_posb_of_lend_at] AT [pterm_wc], which is generic in     *)
  (*  [Wc]).  The ONE that does not transfer for free is                   *)
  (*  [UShLine.ush_wc_inp] -- the credential carries the era's delivered   *)
  (*  input -- because it is a PURE entailment and the terminal shape's    *)
  (*  only input fact sits inside [blk2_inv].  This is that law, at the    *)
  (*  landed one plus exactly the reading the terminal shape owes; the     *)
  (*  round (which mints the shape at a boundary whose line it has just    *)
  (*  read) can supply it as one more persistent conjunct of               *)
  (*  [pterm_shape].                                                       *)
  (* =================================================================== *)
  (* ...and the shape's own reading of it, which is why the conjunct is
     there *)
  Lemma pterm_shape_inp (I : list (bv 8)) (c2 : nat) :
    pterm_shape I c2 -∗
    pterm_shape I c2 ∗ (∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I).
  Proof using .
    rewrite /pterm_shape. iIntros "H".
    iDestruct "H" as (v L gL gR gM XL YR) "(%Htl & #Hpin & #Hlb & Hfe)".
    iSplitR "".
    - iExists v, L, gL, gR, gM, XL, YR. iSplitR; [ by iPureIntro | ].
      by iFrame "Hpin Hlb Hfe".
    - iExists v. by iFrame "Hpin Hlb".
  Qed.

  Lemma pterm_wc_inp_of
      (Hwcf : forall (I : list (bv 8)) (p : nat),
         ⊢ Wcf I p -∗ Wcf I p
           ∗ ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I) ∨ T))
      (I : list (bv 8)) (p : nat) :
    ⊢ pterm_wc I p -∗ pterm_wc I p
      ∗ ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I) ∨ T).
  Proof using .
    rewrite {1}/pterm_wc. iIntros "[Hc | [%Hlt Hsh]]".
    - iDestruct (Hwcf I p with "Hc") as "[Hc $]".
      iApply (pterm_wc_of I p with "Hc").
    - iDestruct (pterm_shape_inp I (5 + p)%nat with "Hsh") as "[Hsh Hi]".
      iSplitR "Hi"; [ | by iLeft ].
      rewrite /pterm_wc. iRight. iSplitR; [ by iPureIntro | ]. iExact "Hsh".
  Qed.

  Context (N : uk_names Σ).
  Context (γp : gname).
  Context (Pm : list (bv 8) -> iProp Σ).

  (* the BODY's state comes back to the landed credential *)
  Lemma pterm_posw_3 (l : list fdstate) (ws : list (list (bv 8))) :
    UkSh.ush_posw N γp T pterm_wc Wbf Pm l ws -∗
    UkSh.ush_posw N γp T Wcf Wbf Pm l ws.
  Proof using .
    rewrite /UkSh.ush_posw. iIntros "[H | H]"; [| iRight; iExact "H" ].
    iDestruct "H" as (I) "(%Hpure & Hpm & Hc)". iLeft. iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    iApply (pterm_wcp_3 l I with "Hc").
  Qed.

  (* ...and the HEAD's state goes out to the widened one *)
  Lemma pterm_posb_of (l : list fdstate) (p : nat) :
    UkSh.ush_posb N γp T Wcf Wbf Pm l p -∗
    UkSh.ush_posb N γp T pterm_wc Wbf Pm l p.
  Proof using .
    rewrite /UkSh.ush_posb. iIntros "[H | H]"; [| iRight; iExact "H" ].
    iDestruct "H" as (I) "(%Hr & Hpm & Hc)". iLeft. iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    iApply (pterm_wcp_of l I p with "Hc").
  Qed.

  (* ...AND THE TERMINAL ARM ITSELF IS A HEAD STATE: this is what the
     fork twin's re-entry hands [UkSh.wp_ksh_getcmd] at the third arm. *)
  Lemma pterm_posb_of_shape (l : list fdstate) (I : list (bv 8)) :
    UkSh.ush_fd0c l /\ UkSh.ush_fd1p l /\ UkSh.ush_fd2p l ->
    rest_of I = [] ->
    Pm I -∗ pterm_shape I 5%nat -∗
    UkSh.ush_posb N γp T pterm_wc Wbf Pm l 0%nat.
  Proof using .
    intros Hrow Hrest. iIntros "Hpm Hsh". rewrite /UkSh.ush_posb.
    iLeft. iExists I. iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
    rewrite /pterm_wc. iRight. iSplitR; [ iPureIntro; lia | ].
    rewrite Nat.add_0_r. iExact "Hsh".
  Qed.

  (* =================================================================== *)
  (*  S3  THE TWO OBLIGATIONS THAT REMAIN, AND THE REDUCTION              *)
  (* =================================================================== *)

  (* (B) THE LEAF (design SS4.3i's dirty credential).  D4 at the resource
     level: a round whose [fork1] failed is the LAST round of the covered
     session, so a line read after it cannot be disciplined and the era's
     claim is dirty.  The cursor is 7 because the main loop has written
     both prompt bytes by the time the read completes a line. *)
  Definition pterm_read_law : Prop :=
    forall I l : list (bv 8),
      wl_nl ∉ l ->
      ⊢ Pm (I ++ l ++ [wl_nl])%list -∗ pterm_shape I 7%nat ={⊤}=∗
        Pm (I ++ l ++ [wl_nl])%list ∗ T.

  (* ...AND WITH IT, [UkSh]'s FOURTH AND LAST [Wc] HYPOTHESIS IS ONE
     LINE.  This is the reduction: everything else the terminal re-entry
     needs is landed. *)
  (* ...AND ITS DISCHARGE (lane PIPE-STAGE-4).  What refutes `a line was
     delivered after a fork-failure round' is neither pure nor monotone:
     the terminal round FREEZES the claim's resolution at [nlines I - 1]
     ([PipeOut.cs_frozen_at], carried by [pwc_fork_exit]), while the read
     residue of the delivered line forces [length cs0 >= nlines I].
     [PipeBoth.pterm_read_absurd] is the contradiction; the fancy update
     is spent only to read [1 <= nlines I] back out of the family's
     invariant ([pwc_fork_exit_nlines]).  The ONE premise is the era's
     reading of [Pm], which is [UShLine.ush_mid_at]'s fourth conjunct. *)
  Lemma pterm_read_law_of :
    (forall I' : list (bv 8),
       ⊢ Pm I' -∗ Pm I'
         ∗ (∃ v : era_pins, era_pin γ (S gen_id) v ∗ pwc_rres v I')) ->
    pterm_read_law.
  Proof using .
    intros Hpm I l Hnl. iIntros "Hpm Hsh".
    iDestruct (Hpm (I ++ l ++ [wl_nl])%list with "Hpm") as "[Hpm Hv]".
    iDestruct "Hv" as (v') "[#Hpin' #Hres]".
    rewrite /pterm_shape.
    iDestruct "Hsh" as (v L gL gR gM XL YR) "(%Htl & #Hpin & #Hlb & Hfe)".
    destruct Htl as (HTX & HTY & _).
    iDestruct (era_pin_agree with "Hpin' Hpin") as %->.
    iMod (pterm_fork_exit_read_fupd g ⊤ blk2N (S gen_id) v I L l
            gL gR gM XL YR 7%nat HTX HTY ltac:(apply top_subseteq)
            with "Hfe Hres") as "[_ #HT]".
    iModIntro. by iFrame "Hpm HT".
  Qed.

  Lemma pterm_wc_read_of :
    pterm_read_law ->
    (forall I l : list (bv 8),
       wl_nl ∉ l ->
       ⊢ Pm (I ++ l ++ [wl_nl])%list -∗ Wcf I 2%nat ={⊤}=∗
         Pm (I ++ l ++ [wl_nl])%list ∗ Wcf (I ++ l ++ [wl_nl])%list 3%nat) ->
    forall I l : list (bv 8),
      wl_nl ∉ l ->
      ⊢ Pm (I ++ l ++ [wl_nl])%list -∗ pterm_wc I 2%nat ={⊤}=∗
        Pm (I ++ l ++ [wl_nl])%list ∗ pterm_wc (I ++ l ++ [wl_nl])%list 3%nat.
  Proof using .
    intros Hterm Hlanded I l Hnl. iIntros "Hpm Hc".
    rewrite {1}/pterm_wc. iDestruct "Hc" as "[Hc | [_ Hsh]]".
    - iMod (Hlanded I l Hnl with "Hpm Hc") as "[$ Hw]". iModIntro.
      iApply (pterm_wc_of _ 3%nat with "Hw").
    - iDestruct (pterm_shape_pin I 7%nat with "Hsh") as "[Hpv Hsh]".
      iDestruct "Hpv" as (v) "#Hpin".
      iMod (Hterm I l Hnl with "Hpm Hsh") as "[$ #HT]". iModIntro.
      iApply (pterm_wc_of _ 3%nat).
      iApply (pipe_Hcltaint g (I ++ l ++ [wl_nl])%list 3%nat v
                with "Hpin HT").
  Qed.


End UkShPipeFork.

(* NAME THE LEAF, DO NOT UNFOLD IT (durable-notes, the instance-search
   wedge; [UInitPipe]'s own header has the measurement).  The terminal
   shape carries the family's [inv] and the widened credential is a
   disjunction over it, so ANY [Persistent]/[Timeless]/[IntoWand] search
   that is allowed to unfold [pterm_wc] walks into the two-writer body and
   does not come back -- measured at [UInitPipe.v]'s prompt law, where the
   era's credential became [pterm_wc] (design SS4.3p): one [iApply] ran
   for 1h28m before this.  Every consumer either names its instance or
   rewrites the definition by hand. *)
#[global] Typeclasses Opaque PipeLinkInst.pipe_Wcl_at.
#[global] Typeclasses Opaque PipeLinkInst.pipe_Wbl_at.
#[global] Typeclasses Opaque pterm_shape.
#[global] Typeclasses Opaque pterm_pay.
#[global] Typeclasses Opaque pterm_wc.

Section UkShPipeForkPrompt.
  (* [UShPanic.v]'s binder list, which is what makes the call's classes
     resolve here as they resolve there, plus the pipeline era's two. *)
  Context {Σ : gFunctors}.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{!uartGhostG Σ}.

  Local Notation Wcf := (pipe_Wcl_at g).

  (* =================================================================== *)
  (*  S4  OBLIGATION (A): THE TWO PROMPT BYTES AT THE TERMINAL ARM,       *)
  (*      PACKAGED AS [UkSh.ksh_w] (lane SH-PIPE-ROUND-6, order A;        *)
  (*      design SS4.3m AS LANDED).                                       *)
  (*                                                                     *)
  (*  The loop's prompt is ONE [write(2, "$ ", 2)] and [UShPanic.        *)
  (*  ksh_w_of_link_prompt_fam] is that call at an ABSTRACT byte family   *)
  (*  [F] with a per-byte link step as its only premise.  So obligation   *)
  (*  (A) is exactly a [UShPanic.prompt_step] at                          *)
  (*  [F p := pterm_shape g I (5 + p)], whose two instances are             *)
  (*  PIPE-STAGE-3's landed steps ([PipeBoth.pprompt_dollar_fork] at      *)
  (*  position 5, [pprompt_space_fork] at 6 -- 5 is the runcmd child's    *)
  (*  own `fork\n').  Nothing else about the terminal arm is needed here: *)
  (*  the call is the SAME one the landed arm makes, at a different       *)
  (*  family.                                                            *)
  (*                                                                     *)
  (*  [Hcons] IS A HYPOTHESIS AND THAT IS A FINDING (see the lane's       *)
  (*  report): the terminal byte steps turn a CLAIM step into an          *)
  (*  [out_link], which every other era-level byte law reaches through    *)
  (*  the RESOURCE bundle [PipeLinks.pipe_links] instead                  *)
  (*  ([pipe_links_holds] is itself [Proof using Hcons]).  The pipeline's *)
  (*  record has no eighth leaf for the TERMINAL byte, so this lane       *)
  (*  carries the equation the way [PipeBoth] does.                       *)
  (* =================================================================== *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).

  Lemma pterm_prompt_step (I : list (bv 8)) :
    pipe_link_taint g -∗
    UShPanic.prompt_step (fun p : nat => pterm_shape g I (5 + p)%nat).
  Proof using Hcons.
    iIntros "#Ht". rewrite /UShPanic.prompt_step.
    iIntros "!>" (p b Φ) "%Hb %Hp Hsh HΦ".
    assert (Hbt : b = u_prompt !!! p)
      by (symmetry; exact (list_lookup_total_correct u_prompt p b Hb)).
    rewrite /pterm_shape.
    iDestruct "Hsh" as (v L gL gR gM XL YR) "(%Htl & #Hpin & #Hlb & Hfe)".
    destruct Htl as (HTX & HTY & Hbl).
    assert (Hwitt : forall sel : list bool,
              sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel).
    { destruct Hbl as (ws & Hws). intros sel Hs.
      exact (pblk2_wit_t_forkc I ws sel Hws Hs). }
    destruct p as [| [| p]]; [ | | exfalso; lia ].
    - (* the `$' at position 5 *)
      iApply (pprompt_dollar_fork g Hcons blk2N (S gen_id) v I L gL gR gM
                XL YR b Φ HTX HTY blk2N_uart Hbt Hwitt
                with "[] Ht Hpin Hfe [HΦ]").
      { iApply pblk2_ecl_R_t_holds. }
      iIntros "Hfe". iApply "HΦ".
      iExists v, L, gL, gR, gM, XL, YR. iSplitR; [ by iPureIntro | ].
      by iFrame "Hpin Hlb Hfe".
    - (* the space at position 6 *)
      iApply (pprompt_space_fork g Hcons blk2N (S gen_id) v I L gL gR gM
                XL YR b Φ HTX HTY blk2N_uart Hbt Hwitt
                with "[] Ht Hpin Hfe [HΦ]").
      { iApply pblk2_ecl_R_t_holds. }
      iIntros "Hfe". iApply "HΦ".
      iExists v, L, gL, gR, gM, XL, YR. iSplitR; [ by iPureIntro | ].
      by iFrame "Hpin Hlb Hfe".
  Qed.

  (* ...AND THE CALL ITSELF: obligation (A), verbatim. *)
  Lemma pterm_prompt_arm (Np : uk_names Σ) (I : list (bv 8))
      (l : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    pipe_link_taint g -∗ shk_rodata (ukn_t Np) -∗
    UkSh.ksh_w (PS := uprogSG_free) Np (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd Np) l ∗ pterm_shape g I 5%nat)
      (UserFd.ustd (ukn_fd Np) l ∗ pterm_shape g I 7%nat).
  Proof using Hcons.
    intros Hl2. iIntros "#Ht #Hro".
    iPoseProof (pterm_prompt_step I with "Ht") as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) Np
              (fun p : nat => pterm_shape g I (5 + p)%nat) l rb Hl2
              with "Hst Hro").
  Qed.

  (* ...AND THE LOOP'S PROMPT LAW AT THE WIDENED CREDENTIAL.  This is
     what [UkSh.wp_ksh_getcmd] spends at the terminal re-entry, and it is
     the LANDED law on the left arm and (A) on the right. *)
  Lemma pterm_prompt_law (Np : uk_names Σ) :
    pipe_link_taint g -∗ shk_rodata (ukn_t Np) -∗
    UkSh.ush_prompt_law (PS := uprogSG_free) Np Wcf -∗
    UkSh.ush_prompt_law (PS := uprogSG_free) Np (pterm_wc g).
  Proof using Hcons.
    iIntros "#Ht #Hro #Hlaw".
    rewrite {1}/UkSh.ush_prompt_law.
    iDestruct "Hlaw" as "[#Hplaw #Hclaw]".
    rewrite /UkSh.ush_prompt_law. iModIntro. iSplitR "".
    - iIntros (I l) "%Hfd2". destruct Hfd2 as [rb Hl2].
      iPoseProof (pterm_prompt_arm Np I l rb Hl2 with "Ht Hro") as "Hta".
      iIntros (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
      rewrite {1}/pterm_wc. iDestruct "Hc" as "[Hc | [_ Hsh]]".
      + iApply ("Hplaw" $! I l with "[%] [%] [%] [%] Hcode [$Hstd $Hc] Hrun
                 [Hcont]");
          [ by exists rb | exact Ha0 | exact Ha1 | exact Ha2 | ].
        iIntros (h' ret) "[Hstd Hw] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hw] Hrun").
        iApply (pterm_wc_of g I 2%nat with "Hw").
      + iApply ("Hta" $! h m avail with "[%] [%] [%] Hcode [$Hstd Hsh]
                 Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | | ].
        { rewrite Nat.add_0_r. iExact "Hsh". }
        iIntros (h' ret) "[Hstd Hsh'] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hsh'] Hrun").
        rewrite /pterm_wc. iRight. iSplitR; [ iPureIntro; lia | ].
        iExact "Hsh'".
    - iExact "Hclaw".
  Qed.

  (* =================================================================== *)
  (*  S5  THE TERMINAL ARM'S TIMELESS CORE, AND THE READ REFUTATION AT    *)
  (*      IT ALONE (lane SH-PIPE-ROUND-6)                                 *)
  (*                                                                     *)
  (*  WHY THIS IS HERE.  [UkShFork]'s fork arm redeems the child's exit   *)
  (*  payload with [ChildTok.gen_pay_timeless] -- the escrow's plain      *)
  (*  [gen_pay] costs a LATER, and the u-tier has no later-providing      *)
  (*  leaf at the two [c.mv]s the parent runs next, so the payload MUST   *)
  (*  be [Timeless] ([UkShFork]'s own [HWct] section variable, and the    *)
  (*  [Proof using] of [wp_kshf_fork_at] / [wp_kshm_body_at] names it).   *)
  (*  [pterm_shape] is NOT: it carries the family's [inv].  The check     *)
  (*  below is the two halves of that, one green and one red.            *)
  (*                                                                     *)
  (*  The RED one, compiled by hand and NOT committed, is                 *)
  (*                                                                     *)
  (*    Lemma chk_pterm_wc_timeless I p : Timeless (pterm_wc g I p).      *)
  (*    Proof. rewrite /pterm_wc /pterm_shape /pwc_fork_exit /blk2_inv.   *)
  (*           apply _. Qed.                                              *)
  (*                                                                     *)
  (*    Error: Cannot infer this placeholder of type: Timeless           *)
  (*      (Wcf I p \/ |(p < 3)%nat| * exists v L gL gR gM XL YR,          *)
  (*         |...| * era_pin gamma (S gen_id) v *                         *)
  (*         inv blk2N (blk2_body g (S gen_id) v I L gL gR gM XL YR) *    *)
  (*         wcur gR (1/2) (5 + p) * wcur gM (1/2) 3 *                    *)
  (*         (cs_frozen_at v (nlines I - 1) \/ echo_taint gamma))         *)
  (*                                                                     *)
  (*  -- i.e. PIPE-STAGE-3's obstruction verbatim, at the CHILD'S EXIT    *)
  (*  ESCROW instead of at a [LinkRec] boundary field.  Everything in     *)
  (*  the shape BUT the [inv] is timeless, which is the green half:       *)
  (* =================================================================== *)
  Lemma pterm_cursors_timeless (v : era_pins) (gR gM : gname) (c2 : nat)
      (I : list (bv 8)) :
    Timeless (PipeBoth.wcur gR (1/2) c2 ∗ PipeBoth.wcur gM (1/2) 3%nat
              ∗ (cs_frozen_at v (nlines I - 1)%nat ∨ echo_taint γ))%I.
  Proof using . apply _. Qed.

  (* THE TIMELESS, PERSISTENT CORE of the terminal arm: the era's pin, the
     round's FROZEN resolution and the two pure facts.  It is everything
     the READ site needs and nothing the PROMPT needs -- which is the
     whole of what a repair has to re-home (design SS4.3m AS LANDED SS7's
     era-fixed family: the [inv] moves to [pipe_links], the core stays
     in the credential). *)
  Definition pterm_tcore (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       ⌜pboth_line I⌝
       ∗ era_pin γ (S gen_id) v
       ∗ ((⌜(1 <= nlines I)%nat⌝ ∗ cs_frozen_at v (nlines I - 1)%nat)
          ∨ echo_taint γ))%I.

  Global Instance pterm_tcore_persistent I : Persistent (pterm_tcore I).
  Proof using . rewrite /pterm_tcore. apply _. Qed.
  Global Instance pterm_tcore_timeless I : Timeless (pterm_tcore I).
  Proof using . rewrite /pterm_tcore. apply _. Qed.

  (* ...AND THE READ AFTER THE TERMINAL PROMPT REFUTES A LATER LINE AT THE
     CORE ALONE: a PLAIN entailment, no family, no mask, no fancy update.
     This is strictly stronger than part 3's [pterm_read_law] (which
     spends a [={T}=*] only to read [1 <= nlines I] back out of the
     family's invariant) and it survives any re-homing of the family. *)
  Lemma pterm_tcore_read (v : era_pins) (I l : list (bv 8)) :
    era_pin γ (S gen_id) v -∗
    pterm_tcore I -∗ pwc_rres v (I ++ l ++ [wl_nl])%list -∗
    echo_taint γ.
  Proof using .
    iIntros "#Hpv Hc Hres".
    iDestruct "Hc" as (v') "(%Hbl & #Hpin & [[%Hpos #Hfz] | #HT])";
      [| iExact "HT" ].
    iDestruct (era_pin_agree with "Hpin Hpv") as %->.
    iExFalso.
    iApply (pterm_read_absurd v I l Hpos with "Hfz Hres").
  Qed.

  (* ...AND THE LANDED SHAPE YIELDS IT, at the one fancy update
     [PipeBoth.pwc_fork_exit_nlines] costs. *)
  Lemma pterm_shape_tcore (E : coPset) (I : list (bv 8)) (c2 : nat) :
    (↑blk2N : coPset) ⊆ E ->
    pterm_shape g I c2 ={E}=∗ pterm_shape g I c2 ∗ pterm_tcore I.
  Proof using .
    intros HN. rewrite {1}/pterm_shape.
    iIntros "H".
    iDestruct "H" as (v L gL gR gM XL YR) "(%Htl & #Hpin & #Hlb & Hfe)".
    destruct Htl as (HTX & HTY & Hbl).
    iMod (pwc_fork_exit_nlines g E blk2N (S gen_id) v I L gL gR gM XL YR c2
            HTX HTY HN with "Hfe") as "[Hfe #Hn]".
    iAssert (pterm_tcore I) as "#Hc".
    { rewrite /pterm_tcore. iExists v. iSplitR; [ by iPureIntro | ].
      iFrame "Hpin". iDestruct "Hn" as "[%Hpos | #HT]"; [| by iRight ].
      rewrite {1}/pwc_fork_exit. iDestruct "Hfe" as "(_ & _ & _ & #Hfz)".
      iDestruct "Hfz" as "[#Hfz | #HT]"; [| by iRight ].
      iLeft. iFrame "Hfz". by iPureIntro. }
    iModIntro. iFrame "Hc". rewrite /pterm_shape.
    iExists v, L, gL, gR, gM, XL, YR. iSplitR; [ by iPureIntro | ].
    by iFrame "Hpin Hlb Hfe".
  Qed.

End UkShPipeForkPrompt.
