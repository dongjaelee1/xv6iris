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
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeOutPure.
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
Require Import RiscvPtsto.
Require Import WpUart.
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
  Definition pterm_shape (I : list (bv 8)) (c2 : nat) : iProp Σ :=
    (∃ (v : era_pins) (L : list (bv 8)) (gL gR gM : gname)
       (XL YR : iProp Σ),
       ⌜Timeless XL /\ Timeless YR⌝
       ∗ era_pin γ (S gen_id) v
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
    iDestruct "H" as (v L gL gR gM XL YR) "(%Htl & #Hpin & Hfe)".
    iSplitR; [ by iExists v; iFrame "Hpin" | ].
    iExists v, L, gL, gR, gM, XL, YR. by iFrame "Hpin Hfe".
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
    iDestruct "Hsh" as (v L gL gR gM XL YR) "(%Htl & #Hpin & Hfe)".
    destruct Htl as [HTX HTY].
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
