(* PipeProto.v -- THE PER-PIPE PROTOCOL: one invariant that three processes
   share, so that the bytes a pipe carries are the application's own ghost
   state and the pipeline's round can be READ OFF the two children's exit
   payloads.

   Design of record: claude-notes/design/app-pipe.md SS3 ("The protocol: one
   invariant per pipe, three processes") and SS4.2 ("The round closes at sh,
   from the two exit payloads"), over claude-notes/design/pipe.md ("The byte
   queue").  Lane PIPE-PROTO.

   WHO HOLDS WHAT.  sh's runcmd child allocates the protocol right after
   pipe(2) ([pipe_proto_alloc]), keeps the two SIDE TOKENS and hands the
   WRITE PERMIT to the left child (echo) and the READ PERMIT to the right
   child (cat) through the exec channel.  Nobody ever holds the pipe's queue
   FRAGMENT again: it lives in the invariant, which is why a row on this
   pipe can be closed by anybody at any time ([pipe_reg_of_inv], the
   registration [PipeReg] asks for) and why a dup'd or forked copy of a row
   costs nothing.

   THE THREE PROPERTIES, at the body:

     (P1)  ps_ws s `prefix_of` L         -- only the line ever goes in
     (P2)  the write permit at 0 forces ps_ws s = []   (derived, see below)
     (P3)  after end-of-file the contents are FROZEN: the reader's one-shot
           snapshot [eof_shot pn w] says w = ps_ws s and ps_wo s = false

   (P3) is preserved by a write link only because the link carries
   [ps_wo s = true] (lane PQ-FLAG, design SS3.1): a write link cannot fire at
   a state whose write end is shut, and a snapshot is only taken at such a
   state.  That ONE premise is the whole of the freeze.

   TWO CORRECTIONS TO THE DESIGN, both forced at the STATEMENT and both
   recorded in claude-notes/projects/app-pipe.md:

   1. THE EXACTNESS OF A CURSOR IS AN EXCLUSIVE RESOURCE, not an arithmetic
      consequence of a lower bound.  Design SS3 hoped the chain's [Q j] could
      pin [ps_ws s = take j L] from "a [mono_list] lower bound of length j
      plus (P1)"; it cannot -- a lower bound and (P1) together give only
      [take j L `prefix_of` ps_ws s `prefix_of` L], i.e. [ps_ws s = take k L]
      for SOME k >= j, and the writer's node needs k = j to know which byte
      of L it is appending.  What pins it is that the writer is the ONLY
      writer, and the only way to say that in the logic is an exclusive
      permit that CARRIES the cursor.  So the protocol has a write cursor
      [wcur pn c] (half of a [ghost_var]; the body holds the other half at
      [length (ps_ws s)]) and, symmetrically, a read cursor [rcur pn c] at
      [ps_rp s].  They compose across echo's several [write]s and cat's
      several [read]s, which is exactly what the design asked the builders
      for.
   2. (P2) AND [wtok_spent] ARE THEN UNNECESSARY.  The design's (P2)
      (["ps_ws s = []"] or the persistent "the token went in") exists to let
      sh conclude "echo never wrote" from the start token; with the cursor
      that is [wcur pn 0] against the body's [wcur pn (length (ps_ws s))],
      one [ghost_var] agreement ([pipe_body_P2] below).  So [wtok pn] IS the
      write permit at 0, no one-shot is minted for it, and the body has one
      conjunct fewer.

   The reader's start permit ([rtok]) is the design's third omission: SS3
   lists only [wtok] among what [pipe_proto_alloc] hands out, and without a
   read permit cat's chain cannot pin [ps_rp s] either.

   NOTHING IN THE TREE IMPORTS THIS FILE, so no audit cone reaches it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list gmap bitvector.definitions.
From iris.algebra Require Import excl agree csum.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.       (* [riscvGS] *)
Require Import UserPtTree.       (* [uptd] -- the posts' entry table *)
Require Import Xv6G.             (* the ONE bundle; [pipeG] is reached through it *)
Require Import PipeNames.        (* [pipe_st] / [pst_*] / [pipe_names] / [pn_queue] *)
Require Import PipeQueue.        (* the links, the chains, the payments, the posts *)
Require Import PipeReg.          (* [pipe_reg] -- what a pipe row's close is paid with *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE PROTOCOL'S CAMERAS AND NAMES                                  *)
(* ===================================================================== *)

(* THE READER'S END-OF-FILE SNAPSHOT: a one-shot, [KptGhost.kptR]'s shape.
   [Cinl] is "no end-of-file has been observed" (exclusive, in the body);
   [Cinr] is the frozen contents (PERSISTENT, and that is the whole point --
   it rides cat's exit payload and is read by sh after both waits). *)
Definition pipe_eofR : cmra :=
  csumR (exclR unitO) (agreeR (leibnizO (list (bv 8)))).

(* THE WRITER'S "THE READ END WAS SEEN SHUT" ONE-SHOT (design SS3.1b, lane
   PIPE-PROTO-2).  Same shape, no payload: what it records is a fact about
   [ps_ro], which is MONOTONE -- only [pst_close false] moves it, and only
   one way -- so the shot needs to carry nothing but itself. *)
Definition pipe_roR : cmra := csumR (exclR unitO) (agreeR unitO).

Class pipeProtoG (Σ : gFunctors) := PipeProtoG {
  ppg_hist :: inG Σ (mono_listR (leibnizO (bv 8)));  (* [ps_ws]'s history *)
  ppg_eof  :: inG Σ pipe_eofR;                       (* the EOF snapshot *)
  ppg_ro   :: inG Σ pipe_roR;                        (* the read-end shot *)
  ppg_cur  :: ghost_varG Σ nat;                      (* the two cursors *)
  ppg_side :: inG Σ (exclR unitO);                   (* the two side tokens *)
}.

Definition pipeProtoΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO (bv 8))); GFunctor pipe_eofR;
     GFunctor pipe_roR; ghost_varΣ nat; GFunctor (exclR unitO) ].

Global Instance subG_pipeProtoΣ {Σ} : subG pipeProtoΣ Σ -> pipeProtoG Σ.
Proof. solve_inG. Qed.

(* ONE RECORD OF NAMES per pipe, as design SS3 asks ([pnames]).  It is plain
   data, so it crosses [exec] inside a program's entry payload the way
   [pipe_names] does. *)
Record pnames := MkPNames {
  pn_hist  : gname;   (* the [mono_list] of bytes written *)
  pn_eof   : gname;   (* the reader's one-shot snapshot *)
  pn_ro    : gname;   (* the writer's "the read end was seen shut" shot *)
  pn_wcur  : gname;   (* the write permit, a [ghost_var nat] in halves *)
  pn_rcur  : gname;   (* the read permit, likewise *)
  pn_sideL : gname;   (* sh's left-child token *)
  pn_sideR : gname;   (* sh's right-child token *)
}.

Global Instance pnames_eq_dec : EqDecision pnames.
Proof. solve_decision. Defined.
Global Instance pnames_inhabited : Inhabited pnames :=
  populate (MkPNames 1%positive 1%positive 1%positive 1%positive 1%positive
              1%positive 1%positive).

(* THE NAMESPACE, at top level and free of any context, as [KptGhost.kptN]
   is: a caller that has to state a mask premise must be able to name it. *)
Definition pipeN : namespace := nroot .@ "pipeproto".

(* the reader's observation node has to DECIDE whether the state it is fired
   at is an end-of-file, so that it can shoot the snapshot there and be
   vacuous everywhere else *)
Global Instance pst_eof_dec (s : pipe_st) : Decision (pst_eof s).
Proof. rewrite /pst_eof /pst_empty. apply and_dec; apply _. Defined.

Section PipeProto.
  (* THE CONTEXT IS [xv6G]'S PLUS THIS FILE'S OWN CLASS and nothing else
     ([PipeReg.v]'s header, [Xv6G.v]'s rule): a second [pipeG] beside the
     bundle would make [pipe_qfrag] here a different proposition from
     [PipeQueue]'s. *)
  Context `{!riscvGS Σ, !xv6G Σ, !pipeProtoG Σ}.

  (* ------------------------------------------------------------------- *)
  (*  1.  THE PIECES                                                      *)
  (* ------------------------------------------------------------------- *)

  (* the history of everything written, and a PERSISTENT lower bound of it
     -- "these bytes are in the pipe, and they are never coming out of the
     history".  [pws_lb pn L] is echo's exit payload: "the line is in". *)
  Definition pws_auth (pn : pnames) (l : list (bv 8)) : iProp Σ :=
    own (pn_hist pn) (●ML (l : list (leibnizO (bv 8)))).
  Definition pws_lb (pn : pnames) (l : list (bv 8)) : iProp Σ :=
    own (pn_hist pn) (◯ML (l : list (leibnizO (bv 8)))).

  (* the EOF snapshot's two states *)
  Definition eof_pending (pn : pnames) : iProp Σ :=
    own (pn_eof pn) (Cinl (Excl ()) : pipe_eofR).
  Definition eof_shot (pn : pnames) (w : list (bv 8)) : iProp Σ :=
    own (pn_eof pn) (Cinr (to_agree (w : leibnizO (list (bv 8)))) : pipe_eofR).

  (* THE READ-END SHOT'S TWO STATES (P4).  [ro_shot] is what a writer takes
     out of its OWN observation node when the node fires at a shut read end,
     and it is what makes a write payable after a SHORT write: a write link
     carries [⌜ps_ro s = true⌝] (lane PQ-FLAG-2) and (P4) says the shot
     forces [ps_ro s = false], so every link of a derailed chain is
     VACUOUS -- the exact mirror of (P3)'s refutation by [⌜ps_wo s = true⌝]. *)
  Definition ro_pending (pn : pnames) : iProp Σ :=
    own (pn_ro pn) (Cinl (Excl ()) : pipe_roR).
  Definition ro_shot (pn : pnames) : iProp Σ :=
    own (pn_ro pn) (Cinr (to_agree ()) : pipe_roR).

  (* THE TWO PERMITS.  Half of each [ghost_var] sits in the body at the
     state's own cursor, the other half is the process's exclusive right to
     move it -- and its exact knowledge of where it is. *)
  Definition wcur (pn : pnames) (c : nat) : iProp Σ :=
    ghost_var (pn_wcur pn) (1/2) c.
  Definition rcur (pn : pnames) (c : nat) : iProp Σ :=
    ghost_var (pn_rcur pn) (1/2) c.

  (* ...at the start.  [wtok] is design SS3's "writer's start token": it is
     the write permit at cursor 0, which is what makes (P2) a [ghost_var]
     agreement instead of a second one-shot. *)
  Definition wtok (pn : pnames) : iProp Σ := wcur pn 0.
  Definition rtok (pn : pnames) : iProp Σ := rcur pn 0.

  (* THE TWO SIDE TOKENS (design SS4.2 as amended by SH-PIPE's R-2): a
     [wait(0)] cannot tell sh's two children apart, so both children's exit
     payloads are ONE symmetric disjunction and the side is told by which
     exclusive token came back. *)
  Definition side_L (pn : pnames) : iProp Σ := own (pn_sideL pn) (Excl ()).
  Definition side_R (pn : pnames) : iProp Σ := own (pn_sideR pn) (Excl ()).

  Global Instance pws_lb_persistent pn l : Persistent (pws_lb pn l).
  Proof using . rewrite /pws_lb. apply _. Qed.
  Global Instance pws_lb_timeless pn l : Timeless (pws_lb pn l).
  Proof using . rewrite /pws_lb. apply _. Qed.
  Global Instance pws_auth_timeless pn l : Timeless (pws_auth pn l).
  Proof using . rewrite /pws_auth. apply _. Qed.
  Global Instance eof_pending_timeless pn : Timeless (eof_pending pn).
  Proof using . rewrite /eof_pending. apply _. Qed.
  Global Instance eof_shot_timeless pn w : Timeless (eof_shot pn w).
  Proof using . rewrite /eof_shot. apply _. Qed.
  Global Instance eof_shot_persistent pn w : Persistent (eof_shot pn w).
  Proof using .
    rewrite /eof_shot. apply own_core_persistent, Cinr_core_id, _.
  Qed.
  Global Instance ro_pending_timeless pn : Timeless (ro_pending pn).
  Proof using . rewrite /ro_pending. apply _. Qed.
  Global Instance ro_shot_timeless pn : Timeless (ro_shot pn).
  Proof using . rewrite /ro_shot. apply _. Qed.
  Global Instance ro_shot_persistent pn : Persistent (ro_shot pn).
  Proof using .
    rewrite /ro_shot. apply own_core_persistent, Cinr_core_id, _.
  Qed.
  Global Instance wcur_timeless pn c : Timeless (wcur pn c).
  Proof using . rewrite /wcur. apply _. Qed.
  Global Instance rcur_timeless pn c : Timeless (rcur pn c).
  Proof using . rewrite /rcur. apply _. Qed.
  Global Instance side_L_timeless pn : Timeless (side_L pn).
  Proof using . rewrite /side_L. apply _. Qed.
  Global Instance side_R_timeless pn : Timeless (side_R pn).
  Proof using . rewrite /side_R. apply _. Qed.

  (* ---- the history ---- *)

  Lemma pws_auth_lb (pn : pnames) (l : list (bv 8)) :
    pws_auth pn l -∗ pws_auth pn l ∗ pws_lb pn l.
  Proof using .
    rewrite /pws_auth /pws_lb -own_op -mono_list_auth_lb_op. iIntros "$".
  Qed.

  Lemma pws_lb_prefix (pn : pnames) (l l' : list (bv 8)) :
    pws_auth pn l -∗ pws_lb pn l' -∗ ⌜l' `prefix_of` l⌝.
  Proof using .
    rewrite /pws_auth /pws_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    by iPureIntro.
  Qed.

  (* a lower bound is DOWNWARD CLOSED: knowing a longer prefix is in the
     history is knowing every shorter one is *)
  Lemma pws_lb_weaken (pn : pnames) (l l' : list (bv 8)) :
    l' `prefix_of` l -> pws_lb pn l -∗ pws_lb pn l'.
  Proof using .
    intros Hp. rewrite /pws_lb. iIntros "H". iApply (own_mono with "H").
    apply mono_list_lb_mono. exact Hp.
  Qed.

  Lemma pws_auth_grow (pn : pnames) (l : list (bv 8)) (b : bv 8) :
    pws_auth pn l ==∗ pws_auth pn (l ++ [b]) ∗ pws_lb pn (l ++ [b]).
  Proof using .
    rewrite /pws_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((l ++ [b]) : list (leibnizO (bv 8))))
            with "Ha") as "Ha".
    { apply mono_list_update. by exists [b]. }
    iModIntro. iApply (pws_auth_lb with "Ha").
  Qed.

  (* ---- the one-shot ---- *)

  Lemma eof_pending_shot (pn : pnames) (w : list (bv 8)) :
    eof_pending pn -∗ eof_shot pn w -∗ False.
  Proof using .
    rewrite /eof_pending /eof_shot. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %Hv.
  Qed.

  Lemma eof_shot_agree (pn : pnames) (w w' : list (bv 8)) :
    eof_shot pn w -∗ eof_shot pn w' -∗ ⌜w = w'⌝.
  Proof using .
    rewrite /eof_shot. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Cinr_op Cinr_valid in Hv.
    iPureIntro. exact (to_agree_op_inv_L _ _ Hv).
  Qed.

  Lemma eof_shoot (pn : pnames) (w : list (bv 8)) :
    eof_pending pn ==∗ eof_shot pn w.
  Proof using .
    rewrite /eof_pending /eof_shot. iIntros "H".
    iApply (own_update with "H"). by apply cmra_update_exclusive.
  Qed.

  Lemma ro_pending_shot (pn : pnames) : ro_pending pn -∗ ro_shot pn -∗ False.
  Proof using .
    rewrite /ro_pending /ro_shot. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %Hv.
  Qed.

  Lemma ro_shoot (pn : pnames) : ro_pending pn ==∗ ro_shot pn.
  Proof using .
    rewrite /ro_pending /ro_shot. iIntros "H".
    iApply (own_update with "H"). by apply cmra_update_exclusive.
  Qed.

  (* ---- the permits ---- *)

  Lemma wcur_agree (pn : pnames) (c c' : nat) :
    wcur pn c -∗ wcur pn c' -∗ ⌜c = c'⌝.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %He. by iPureIntro.
  Qed.

  Lemma rcur_agree (pn : pnames) (c c' : nat) :
    rcur pn c -∗ rcur pn c' -∗ ⌜c = c'⌝.
  Proof using .
    rewrite /rcur. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %He. by iPureIntro.
  Qed.

  Lemma wcur_move (pn : pnames) (c c' d : nat) :
    wcur pn c -∗ wcur pn c' ==∗ wcur pn d ∗ wcur pn d.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    iApply (ghost_var_update_halves d with "H1 H2").
  Qed.

  Lemma rcur_move (pn : pnames) (c c' d : nat) :
    rcur pn c -∗ rcur pn c' ==∗ rcur pn d ∗ rcur pn d.
  Proof using .
    rewrite /rcur. iIntros "H1 H2".
    iApply (ghost_var_update_halves d with "H1 H2").
  Qed.

  (* ---- the side tokens: two answers cannot be the same side ---- *)

  Lemma side_L_excl (pn : pnames) : side_L pn -∗ side_L pn -∗ False.
  Proof using .
    rewrite /side_L. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    exact (exclusive_l _ _ Hv).
  Qed.

  Lemma side_R_excl (pn : pnames) : side_R pn -∗ side_R pn -∗ False.
  Proof using .
    rewrite /side_R. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    exact (exclusive_l _ _ Hv).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2.  THE BODY AND THE INVARIANT                                      *)
  (* ------------------------------------------------------------------- *)

  (* THE BODY, at the line [L] (design SS3; [L] is the bytes echo writes --
     [PipeDisc]'s good continuation minus the prompt, which is spelled
     inline there as [wl_line (drop 1 (pline_ws l))], see [PipeDisc.pcont]'s
     [PRan] row: there is no landed NAME for it, so the protocol takes it as
     a parameter).

     The pipe's exact queue FRAGMENT lives here and nowhere else.  Beside it:
     the history's authority (so a writer can hand out persistent lower
     bounds), and the BODY'S HALF of each of the two cursors, pinned to the
     state -- which is what makes a permit holder's knowledge exact. *)
  Definition pipe_body (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      : iProp Σ :=
    (∃ s : pipe_st,
       pipe_qfrag (pn_queue γp) s
       ∗ pws_auth pn (ps_ws s)
       ∗ wcur pn (length (ps_ws s))
       ∗ rcur pn (ps_rp s)
       (* (P1) only the line ever goes in *)
       ∗ ⌜ps_ws s `prefix_of` L⌝
       (* (P5) THE READER NEVER RUNS AHEAD OF THE WRITER -- the one fact
          that makes a READ CURSOR say something about the CONTENTS (see
          [pws_lb_of_rcur] below, and [pipe_body_needs_P5] for why nothing
          else in this body implies it).  It is preserved for free: a write
          grows [ps_ws] and leaves [ps_rp], a close moves neither, and a
          READ fires only at [pst_next s = Some b], i.e. at [ps_rp s <
          length (ps_ws s)]. *)
       ∗ ⌜(ps_rp s <= length (ps_ws s))%nat⌝
       (* (P3) after end-of-file the contents are frozen *)
       ∗ (eof_pending pn
          ∨ ∃ w : list (bv 8),
              eof_shot pn w ∗ ⌜w = ps_ws s /\ ps_wo s = false⌝)
       (* (P4) the read end, once seen shut, STAYS shut ([ps_ro] is
          monotone: only [pst_close false] moves it) *)
       ∗ (ro_pending pn ∨ (ro_shot pn ∗ ⌜ps_ro s = false⌝)))%I.

  (* TIMELESS, and it is load-bearing: every link's fupd runs at ⊤ with no
     WP step to strip a later off an opened invariant, so the body has to be
     strippable under a plain [iInv .. as ">"].  This is why (P3) is stated
     as the cell's two OWNED arms and not as the design's wand
     [∀ w, γeof ↦ Some w -∗ ⌜..⌝]: a wand is not timeless. *)
  Global Instance pipe_body_timeless pn γp L : Timeless (pipe_body pn γp L).
  Proof using . rewrite /pipe_body. apply _. Qed.

  Definition pipe_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      : iProp Σ := inv pipeN (pipe_body pn γp L).

  Global Instance pipe_inv_persistent pn γp L : Persistent (pipe_inv pn γp L).
  Proof using . rewrite /pipe_inv. apply _. Qed.

  (* ---- (P1)--(P3), each against the KERNEL'S authority (which is the
     shape every link reads them at: the body holds the fragment, the
     caller's link is handed the authority) ---- *)

  Lemma pipe_body_P1 (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (s : pipe_st) :
    pipe_body pn γp L -∗ pipe_qauth (pn_queue γp) s -∗
    ⌜ps_ws s `prefix_of` L⌝.
  Proof using .
    iIntros "Hb Ha". iDestruct "Hb" as (s0) "(Hf & _ & _ & _ & %Hpre & _ & _ & _)".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-. by iPureIntro.
  Qed.

  (* (P2), DERIVED: the start token is the write permit at 0, and the body
     holds the other half at [length (ps_ws s)]. *)
  Lemma pipe_body_P2 (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (s : pipe_st) :
    pipe_body pn γp L -∗ wtok pn -∗ pipe_qauth (pn_queue γp) s -∗
    ⌜ps_ws s = []⌝.
  Proof using .
    iIntros "Hb Ht Ha". iDestruct "Hb" as (s0) "(Hf & _ & Hw & _ & _ & _ & _ & _)".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    rewrite /wtok. iDestruct (wcur_agree with "Hw Ht") as %Hlen.
    iPureIntro. by apply nil_length_inv.
  Qed.

  Lemma pipe_body_P3 (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (s : pipe_st) (w : list (bv 8)) :
    pipe_body pn γp L -∗ eof_shot pn w -∗ pipe_qauth (pn_queue γp) s -∗
    ⌜w = ps_ws s /\ ps_wo s = false⌝.
  Proof using .
    iIntros "Hb #Hs Ha".
    iDestruct "Hb" as (s0) "(Hf & _ & _ & _ & _ & _ & [Hp | Heof] & _)".
    - iDestruct (eof_pending_shot with "Hp Hs") as %[].
    - iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
      iDestruct "Heof" as (w') "[#Hs' %Hw]".
      iDestruct (eof_shot_agree with "Hs Hs'") as %<-. by iPureIntro.
  Qed.

  (* (P4), the mirror of (P3) on the OTHER flag, and the one law lane
     PIPE-PROTO-2 exists for: the read end, once a writer's observation node
     has seen it shut, is shut in every later state. *)
  Lemma pipe_body_P4 (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (s : pipe_st) :
    pipe_body pn γp L -∗ ro_shot pn -∗ pipe_qauth (pn_queue γp) s -∗
    ⌜ps_ro s = false⌝.
  Proof using .
    iIntros "Hb #Hs Ha".
    iDestruct "Hb" as (s0) "(Hf & _ & _ & _ & _ & _ & _ & [Hp | [_ %Hro]])".
    - iDestruct (ro_pending_shot with "Hp Hs") as %[].
    - iDestruct (pipe_queue_agree with "Ha Hf") as %<-. by iPureIntro.
  Qed.

  (* (P5) at the kernel's authority, the shape every link reads its
     properties at. *)
  Lemma pipe_body_P5 (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (s : pipe_st) :
    pipe_body pn γp L -∗ pipe_qauth (pn_queue γp) s -∗
    ⌜(ps_rp s <= length (ps_ws s))%nat⌝.
  Proof using .
    iIntros "Hb Ha".
    iDestruct "Hb" as (s0) "(Hf & _ & _ & _ & _ & %Hrle & _ & _)".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-. by iPureIntro.
  Qed.

  (* WHY (P5) IS A CONJUNCT OF THE BODY AND NOT A CONSEQUENCE OF IT, at
     the STATEMENT (design SS4.3g's third owed item; lane PIPE-EXEC-ECHO).
     Nothing else in the body constrains [ps_rp]: (P1) is about [ps_ws],
     (P3) about [ps_ws]/[ps_wo], (P4) about [ps_ro], and the two cursors
     only AGREE with the state.  So the body WITHOUT (P5) is satisfied at a
     state whose reader has run off the end of the contents, and at such a
     state a READ PERMIT AT [c > 0] SAYS NOTHING ABOUT THE LINE -- which is
     exactly what [pws_lb_of_rcur] below has to deny.  The witness: *)
  Lemma pipe_body_needs_P5 (L : list (bv 8)) :
    exists s : pipe_st,
      ps_ws s `prefix_of` L /\ ps_rp s = 1%nat
      /\ ps_wo s = false /\ ps_ro s = false
      /\ ~ (ps_rp s <= length (ps_ws s))%nat.
  Proof using .
    exists (MkPipeSt [] 1%nat false false). cbn.
    split_and!; [ apply prefix_nil | reflexivity | reflexivity
                | reflexivity | lia ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  THE REGISTRATION, AND THE ALLOCATION                            *)
  (* ------------------------------------------------------------------- *)

  (* THE CLOSE LINK, AT EITHER END, ANY NUMBER OF TIMES -- which is what a
     pipe-holding verified program's run carries per row
     ([PipeReg.pipe_reg]) and what its exit spends.  It needs NO knowledge
     at all: [pst_close] leaves [ps_ws] and [ps_rp] alone and only clears a
     flag, so (P1), the two cursors and (P3) all survive -- (P3) because the
     flag it clears can only make [ps_wo] FALSER. *)
  Lemma pipe_clink_of_inv (E : coPset) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (w : bool) :
    ↑pipeN ⊆ E ->
    pipe_inv pn γp L -∗ pipe_clink (pn_queue γp) w emp.
  Proof using .
    intros HE. rewrite /pipe_inv /pipe_clink. iIntros "#Hinv" (s) "Ha".
    iInv "Hinv" as (s0) ">(Hf & Hh & Hw & Hr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_close w s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hclose" with "[Hf Hh Hw Hr Heof Hro]") as "_".
    { iNext. iExists (pst_close w s0). rewrite pst_close_ws pst_close_rp.
      iFrame "Hf Hh Hw Hr". iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iSplitL "Heof".
      - iDestruct "Heof" as "[Hp | Heof]"; [by iLeft |].
        iRight. iDestruct "Heof" as (w0) "[Hs %Hw0]". iExists w0. iFrame "Hs".
        iPureIntro. destruct Hw0 as [Hw1 Hw2]. split; [exact Hw1 |].
        destruct w; [ reflexivity | exact Hw2 ].
      - (* (P4): [ps_ro] is MONOTONE, so a shot survives either close *)
        iDestruct "Hro" as "[Hp | [Hs %Hro]]"; [by iLeft |].
        iRight. iFrame "Hs". iPureIntro.
        destruct w; [ exact Hro | reflexivity ]. }
    iModIntro. by iFrame "Ha".
  Qed.

  (* ...and that IS the registration (design SS3's table, first row; lane
     PIPE-REG's [pipe_reg]).  The handle is persistent, so the [□] costs
     nothing. *)
  Lemma pipe_reg_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8)) :
    pipe_inv pn γp L -∗ pipe_reg γp.
  Proof using .
    iIntros "#Hinv". rewrite /pipe_reg. iIntros "!>" (w).
    rewrite /pipe_cpay. iLeft.
    iApply (pipe_clink_of_inv ⊤ pn γp L w with "Hinv"). solve_ndisj.
  Qed.

  (* VACUITY, the other way round: NOBODY ELSE CAN HOLD THE FRAGMENT once
     the protocol owns it.  This is what makes "registering CONSUMES the
     fragment" (lane PIPE-REG's refutation 2) honest rather than a
     convenience, and it is why every payment on this pipe from here on has
     to come out of the handle. *)
  Lemma pipe_inv_frag_excl (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (s : pipe_st) :
    pipe_inv pn γp L -∗ pipe_qfrag (pn_queue γp) s ={⊤}=∗ False.
  Proof using .
    iIntros "#Hinv Hfr".
    iInv "Hinv" as (s0) ">(Hf & _ & _ & _ & _ & _)" "Hclose".
    iDestruct (pipe_qfrag_excl with "Hf Hfr") as %[].
  Qed.

  (* THE ALLOCATION, right after pipe(2) and before the first fork1.  This
     is LITERALLY [UkReadPipe.wp_uk_pipe_read_end]'s registrar premise
     [∀ γp, pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ Rp γp] at
     [Rp γp := ∃ pn, pipe_inv pn γp L ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗
     side_R pn] -- registering CONSUMES the fragment, and this is where it
     goes. *)
  Lemma pipe_proto_alloc (γp : pipe_names) (L : list (bv 8)) :
    pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗
    ∃ pn : pnames,
      pipe_inv pn γp L ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn
      ∗ pipe_reg γp.
  Proof using .
    iIntros "Hfrag".
    iMod (own_alloc (●ML ([] : list (leibnizO (bv 8))))) as (gh) "Hh";
      [ apply mono_list_auth_valid |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_eofR)) as (ge) "He"; [ done |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_roR)) as (go) "Ho"; [ done |].
    iMod (ghost_var_alloc (0%nat)) as (gw) "Hw".
    iMod (ghost_var_alloc (0%nat)) as (gr) "Hr".
    iMod (own_alloc (Excl ())) as (gl) "Hsl"; [ done |].
    iMod (own_alloc (Excl ())) as (gs) "Hsr"; [ done |].
    iDestruct (ghost_var_split (pn_wcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hw]") as "[Hw1 Hw2]";
      [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split (pn_rcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hr]") as "[Hr1 Hr2]";
      [ by rewrite Qp.half_half | ].
    iMod (inv_alloc pipeN ⊤
            (pipe_body (MkPNames gh ge go gw gr gl gs) γp L)
            with "[Hfrag Hh Hw1 Hr1 He Ho]") as "#Hinv".
    { iNext. iExists pst0. rewrite /pst0 /=. iFrame "Hfrag Hh Hw1 Hr1".
      iSplitR; [ iPureIntro; apply prefix_nil | ].
      iSplitR; [ iPureIntro; cbn; lia | ].
      iSplitL "He"; [ by iLeft | by iLeft ]. }
    iModIntro. iExists (MkPNames gh ge go gw gr gl gs).
    iDestruct (pipe_reg_of_inv _ γp L with "Hinv") as "#Hreg".
    rewrite /wtok /rtok /side_L /side_R /=.
    iFrame "Hinv Hw2 Hr2 Hsl Hsr Hreg".
  Qed.


  (* ------------------------------------------------------------------- *)
  (*  4.  THE WRITER'S CHAIN: echo's payment, at a cursor into the line   *)
  (* ------------------------------------------------------------------- *)

  (* WHAT ECHO KNOWS AFTER [j] OF THIS CALL'S BYTES HAVE LANDED: the write
     permit at [c + j] -- EXACT, because the permit is exclusive and the
     body holds its other half at [length (ps_ws s)] -- and the persistent
     lower bound saying those bytes are in the history.  The permit is also
     what makes the chain COMPOSE across echo's several [write]s (word,
     space, ..., newline, four [kecho_w]s): call number two starts at the
     cursor call number one handed back.

     [Qe] hands the CURSOR back (an observation SPENDS its node --
     design/pipe.md -- so that is the only thing it can do for the caller)
     AND, since 3.1b, the READ-END SHOT: the arm of [pipe_wpost] that fires
     this node is exactly the one whose state has [ps_ro s = false], and
     that is the world echo has to be able to keep writing in.  The shot
     rides a WAND from that pure fact for the same reason [pipe_rQe]'s does:
     [pipe_olink] is a [forall s], ONE node that must be producible at every
     state, so "records nothing when the read end is still open" is not a
     second node but this wand being vacuous there. *)
  Definition pipe_wQ (pn : pnames) (L : list (bv 8)) (c j : nat) : iProp Σ :=
    (wcur pn (c + j) ∗ pws_lb pn (take (c + j) L))%I.

  Definition pipe_wQe (pn : pnames) (L : list (bv 8)) (c j : nat)
      (s : pipe_st) : iProp Σ :=
    (pipe_wQ pn L c j ∗ (⌜ps_ro s = false⌝ -∗ ro_shot pn))%I.

  (* the writer's twin of [pipe_rQe_eof]: at the state the observation arm
     of [pipe_wpost] names, the node yields the cursor AND the shot *)
  Lemma pipe_wQe_ro_shot (pn : pnames) (L : list (bv 8)) (c j : nat)
      (s : pipe_st) :
    ps_ro s = false ->
    pipe_wQe pn L c j s -∗ pipe_wQ pn L c j ∗ ro_shot pn.
  Proof using .
    intros Hro. rewrite /pipe_wQe. iIntros "[HQ Hw]". iFrame "HQ".
    by iApply "Hw".
  Qed.

  (* "THE LINE IS IN": a node whose cursor has reached the end of the line
     hands out the lower bound that rides echo's exit payload to sh. *)
  Lemma pipe_wQ_line (pn : pnames) (L : list (bv 8)) (c n : nat) :
    (c + n)%nat = length L ->
    pipe_wQ pn L c n -∗ wcur pn (length L) ∗ pws_lb pn L.
  Proof using .
    intros He. rewrite /pipe_wQ He (take_ge L (length L) (Nat.le_refl _)).
    by iIntros "[$ $]".
  Qed.

  (* THE CHAIN, built from the handle alone.  The premise on [M] is the
     pointwise reading copyin's post gives the caller: the byte at [ua + k]
     is the line's byte at [c + k]. *)
  Lemma pipe_wchain_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (c j cnt : nat) :
    (c + j + cnt <= length L)%nat ->
    (forall k : nat, (j <= k < j + cnt)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k)%nat)) ->
    pipe_inv pn γp L -∗ pipe_wQ pn L c j -∗
    pipe_wchain (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c) j cnt.
  Proof using .
    revert j. induction cnt as [| cnt IH]; intros j Hle HM.
    { iIntros "#Hinv HQ". iExact "HQ". }
    iIntros "#Hinv HQ". cbn [pipe_wchain].
    iSplit; [ iExact "HQ" | ]. iSplit.
    { (* THE OBSERVATION: the cursor comes back, and where it fires at a
         SHUT READ END it shoots (P4)'s one-shot inside the invariant. *)
      rewrite /pipe_olink. iIntros (s) "Ha".
      destruct (decide (ps_ro s = false)) as [Hro | Hro].
      - iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro')"
          "Hclose".
        iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
        iAssert (|==> ro_shot pn
                      ∗ (ro_pending pn ∨ (ro_shot pn ∗ ⌜ps_ro s0 = false⌝)))%I
          with "[Hro']" as ">[#Hsh Hro']".
        { iDestruct "Hro'" as "[Hp | [#Hsh %Hr]]".
          - iMod (ro_shoot pn with "Hp") as "#Hsh". iModIntro.
            iSplitR; [ iExact "Hsh" | ]. iRight. iFrame "Hsh". by iPureIntro.
          - iModIntro. iSplitR; [ iExact "Hsh" | ].
            iRight. iFrame "Hsh". by iPureIntro. }
        iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro']") as "_".
        { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro'". by iPureIntro. }
        iModIntro. iFrame "Ha". rewrite /pipe_wQe. iFrame "HQ".
        iIntros "_". iExact "Hsh".
      - iModIntro. iFrame "Ha". rewrite /pipe_wQe. iFrame "HQ".
        iIntros "%He". by destruct (Hro He). }
    (* [%Hro] is INTRODUCED AND IGNORED here (lane PQ-FLAG-2): this builder
       is the good-path chain, whose (P1) obligation the write-open premise
       alone discharges.  The read-open premise is what lane PIPE-PROTO-2
       spends, in the DERAILED builder past a short write. *)
    iIntros (b) "%Hb". rewrite /pipe_wlink. iIntros (s) "%Hwo %Hro Ha".
    iDestruct "HQ" as "[Hw #Hlb]".
    iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro')"
      "Hclose".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
    (* (P3)'S SNAPSHOT ARM IS REFUTED BY THE WRITE LINK'S OWN PREMISE.  This
       is the whole of lane PQ-FLAG's contribution (design SS3.1): a write
       link cannot fire at a state whose write end is shut, and a snapshot
       is only ever taken at such a state -- so the contents are frozen. *)
    iDestruct "Heof" as "[Hp | Heof]";
      [ | iDestruct "Heof" as (w0) "[_ %Hw0]"; exfalso;
          destruct Hw0 as [_ Hwo0]; rewrite Hwo0 in Hwo; discriminate ].
    (* the body's cursor pins the contents EXACTLY, which is what tells this
       node WHICH byte of the line it is appending *)
    assert (Hws : ps_ws s0 = take (c + j) L).
    { destruct Hpre as [t Ht]. rewrite -Hlen Ht take_app_length. reflexivity. }
    assert (Hbv : b = L !!! (c + j)%nat).
    { assert (Hj : (j <= j < j + S cnt)%nat) by lia.
      specialize (HM j Hj). rewrite Hb in HM. by simplify_eq. }
    assert (Hcj : (c + j < length L)%nat) by lia.
    assert (Hws' : ps_ws s0 ++ [b] = take (c + S j)%nat L).
    { rewrite Hws Hbv Nat.add_succ_r. symmetry.
      apply take_S_r, list_lookup_lookup_total_lt. exact Hcj. }
    assert (Hlen' : length (ps_ws s0 ++ [b]) = (c + S j)%nat).
    { rewrite Hws' length_take. lia. }
    iMod (pipe_queue_update _ _ _ (pst_write b s0) with "Ha Hf") as "[Ha Hf]".
    iMod (pws_auth_grow pn (ps_ws s0) b with "Hh") as "[Hh #Hlb']".
    iMod (wcur_move pn _ _ (c + S j)%nat with "Hbw Hw") as "[Hbw Hw]".
    iMod ("Hclose" with "[Hf Hh Hbw Hbr Hp Hro']") as "_".
    { iNext. iExists (pst_write b s0).
      rewrite !pst_write_ws !pst_write_rp Hlen'. iFrame "Hf Hh Hbw Hbr".
      iSplitR; [ iPureIntro; rewrite Hws'; apply prefix_take | ].
      (* (P5) across a write: the read pointer did not move and the
         contents grew *)
      iSplitR; [ iPureIntro; lia | ].
      iSplitL "Hp"; [ by iLeft | ].
      (* (P4) rides across a write: [pst_write] does not touch [ps_ro] *)
      iDestruct "Hro'" as "[Hp | [#Hsh %Hr]]"; [ by iLeft | ].
      iRight. iFrame "Hsh". iPureIntro. exact Hr. }
    iModIntro. iFrame "Ha".
    assert (Hle2 : (c + S j + cnt <= length L)%nat) by lia.
    assert (HM2 : forall k : nat, (S j <= k < S j + cnt)%nat ->
              M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k)%nat)).
    { intros k Hk. apply HM. lia. }
    iApply (IH (S j) Hle2 HM2 with "Hinv [Hw]").
    rewrite /pipe_wQ. iFrame "Hw". rewrite -Hws'. iExact "Hlb'".
  Qed.

  (* THE PAYMENT, which is what [UkWritePipe.wp_uk_ecall_write_pipe_std]
     takes at ledger slot 1 (design SS5.4 / lane PIPE-STD). *)
  Lemma pipe_wpay_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (c n : nat) :
    (c + n <= length L)%nat ->
    (forall k : nat, (k < n)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k)%nat)) ->
    pipe_inv pn γp L -∗ wcur pn c -∗ pws_lb pn (take c L) -∗
    pipe_wpay (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c) n.
  Proof using .
    intros Hle HM. iIntros "#Hinv Hw #Hlb". rewrite /pipe_wpay. iLeft.
    assert (Hle2 : (c + 0 + n <= length L)%nat) by lia.
    assert (HM2 : forall k : nat, (0 <= k < 0 + n)%nat ->
              M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k)%nat)).
    { intros k Hk. apply HM. lia. }
    iApply (pipe_wchain_of_inv pn γp L M ua c 0 n Hle2 HM2 with "Hinv [Hw]").
    rewrite /pipe_wQ Nat.add_0_r. iFrame "Hw Hlb".
  Qed.

  (* THE LOWER BOUND A PERMIT HOLDER CAN ALWAYS RECOVER, so that a program
     which crosses [exec] with nothing but the handle and its permit (echo
     does) can start its chain.  This is (P1) plus the permit's exactness,
     read out in one fupd. *)
  Lemma pws_lb_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (c : nat) :
    pipe_inv pn γp L -∗ wcur pn c ={⊤}=∗ wcur pn c ∗ pws_lb pn (take c L).
  Proof using .
    iIntros "#Hinv Hw".
    iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
    iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
    assert (Hws : ps_ws s0 = take c L).
    { destruct Hpre as [t Ht]. rewrite -Hlen Ht take_app_length. reflexivity. }
    iDestruct (pws_auth_lb with "Hh") as "[Hh #Hlb]".
    iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro]") as "_".
    { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro". by iPureIntro. }
    iModIntro. iFrame "Hw". rewrite -Hws. iExact "Hlb".
  Qed.

  Lemma pipe_wpay_of_inv_fupd (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64) (c n : nat) :
    (c + n <= length L)%nat ->
    (forall k : nat, (k < n)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k)%nat)) ->
    pipe_inv pn γp L -∗ wcur pn c ={⊤}=∗
    pipe_wpay (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c) n.
  Proof using .
    intros Hle HM. iIntros "#Hinv Hw".
    iMod (pws_lb_of_inv pn γp L c with "Hinv Hw") as "[Hw #Hlb]".
    iModIntro. iApply (pipe_wpay_of_inv pn γp L M ua c n Hle HM with "Hinv Hw Hlb").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  4b.  THE DERAILED CHAIN: what a writer pays AFTER a short write      *)
  (* ------------------------------------------------------------------- *)

  (* THE WALL ECHO-PIPE FOUND: echo's four writes do not compose past a
     write that stopped SHORT, because the next chain's nodes would have to
     re-establish (P1) with bytes that no longer continue the pipe's
     contents.  Design SS3.1b's ruling closes it from the OTHER side: once
     (P4)'s shot is out, every write link is VACUOUS -- it is handed
     [⌜ps_ro s = true⌝] (lane PQ-FLAG-2) and the shot says [ps_ro s = false].
     So a chain past a short write needs NO cursor, NO lower bound, NO bound
     on the count and NO knowledge of the caller's bytes: the nodes' [Q]/[Qe]
     can be ANY single resource [R] the caller is willing to carry through,
     because the additive conjunction hands the same [R] to the node's value
     and to its observation and the link branch is never taken.

     This is the exact mirror of (P3)'s refutation by [⌜ps_wo s = true⌝] in
     [pipe_wchain_of_inv] -- and it is why the derailed builder must NOT
     carry [wcur]: [pipe_wQ] pins [ps_ws s] through [wcur_agree], which is
     precisely the knowledge a derailed writer has lost. *)
  Lemma pipe_wchain_of_ro_shot (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64)
      (R : iProp Σ) (j cnt : nat) :
    pipe_inv pn γp L -∗ ro_shot pn -∗ R -∗
    pipe_wchain (pn_queue γp) M ua (fun _ : nat => R)
      (fun (_ : nat) (_ : pipe_st) => R) j cnt.
  Proof using .
    revert j. induction cnt as [| cnt IH]; intros j.
    { iIntros "#Hinv #Hsh HR". iExact "HR". }
    iIntros "#Hinv #Hsh HR". cbn [pipe_wchain].
    iSplit; [ iExact "HR" | ]. iSplit.
    { rewrite /pipe_olink. iIntros (s) "Ha". iModIntro. iFrame "Ha".
      iExact "HR". }
    iIntros (b) "_". rewrite /pipe_wlink. iIntros (s) "_ %Hro Ha".
    (* THE LINK IS VACUOUS: (P4) against the read-open premise *)
    iInv "Hinv" as ">Hb" "Hclose".
    iDestruct (pipe_body_P4 with "Hb Hsh Ha") as %Hro'.
    rewrite Hro' in Hro. discriminate.
  Qed.

  Lemma pipe_wpay_of_inv_after_short (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64)
      (R : iProp Σ) (n : nat) :
    pipe_inv pn γp L -∗ ro_shot pn -∗ R -∗
    pipe_wpay (pn_queue γp) M ua (fun _ : nat => R)
      (fun (_ : nat) (_ : pipe_st) => R) n.
  Proof using .
    iIntros "#Hinv #Hsh HR". rewrite /pipe_wpay. iLeft.
    iApply (pipe_wchain_of_ro_shot pn γp L M ua R 0 n with "Hinv Hsh HR").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  5.  THE READER'S CHAIN: cat's payment, at its read pointer          *)
  (* ------------------------------------------------------------------- *)

  (* WHAT CAT KNOWS HAVING TAKEN [acc] OUT OF THE PIPE: the read permit at
     [c + length acc] (exact, as the writer's is) and the pure fact that the
     dequeued bytes ARE the line's bytes at [c..] -- which is (P1) read at
     the dequeued byte, and which is what cat's console write at cursor [c]
     needs (design SS4.1: cat's cursor is [ps_rp s], there is no offset and
     no held descriptor anywhere).

     THE OBSERVATION carries the EOF snapshot as a WAND from [pst_eof s].
     It has to: an observation node must be producible at EVERY state (the
     [pipe_olink] is a [forall s]), and the design's "records nothing at an
     empty ring with [ps_wo s = true]" is exactly that wand being vacuous
     there.  Where the state IS an end-of-file the node SHOOTS the one-shot
     inside the invariant and the wand is then trivial; [pipe_rpost_img]'s
     observation arm hands cat [ps_wo s = false] precisely when it delivered
     nothing, which is the turn of cat's loop where the read answers 0. *)
  Definition pipe_rQ (pn : pnames) (L : list (bv 8)) (c : nat)
      (acc : list (bv 8)) : iProp Σ :=
    (rcur pn (c + length acc) ∗ ⌜acc = take (length acc) (drop c L)⌝)%I.

  Definition pipe_rQe (pn : pnames) (L : list (bv 8)) (c : nat)
      (acc : list (bv 8)) (s : pipe_st) : iProp Σ :=
    (pipe_rQ pn L c acc
     ∗ (⌜pst_eof s⌝ -∗ eof_shot pn (take (c + length acc) L)))%I.

  Lemma pipe_rQe_eof (pn : pnames) (L : list (bv 8)) (c : nat)
      (acc : list (bv 8)) (s : pipe_st) :
    pst_eof s ->
    pipe_rQe pn L c acc s -∗
    pipe_rQ pn L c acc ∗ eof_shot pn (take (c + length acc) L).
  Proof using .
    intros He. rewrite /pipe_rQe. iIntros "[HQ Hw]". iFrame "HQ".
    by iApply "Hw".
  Qed.

  Lemma pipe_rchain_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (c : nat) (acc : list (bv 8)) (cnt : nat) :
    pipe_inv pn γp L -∗ pipe_rQ pn L c acc -∗
    pipe_rchain (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) acc cnt.
  Proof using .
    revert acc. induction cnt as [| cnt IH]; intros acc.
    { iIntros "#Hinv HQ". iExact "HQ". }
    iIntros "#Hinv HQ". cbn [pipe_rchain].
    iSplit; [ iExact "HQ" | ]. iSplit.
    { (* THE OBSERVATION *)
      rewrite /pipe_olink. iIntros (s) "Ha".
      iDestruct "HQ" as "[Hr %Hacc]".
      destruct (decide (pst_eof s)) as [Heof | Hne].
      - (* an end-of-file: SHOOT the snapshot at the frozen contents *)
        iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Hoe & Hro)" "Hclose".
        iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
        iDestruct (rcur_agree with "Hbr Hr") as %Hrp.
        assert (Hws : ps_ws s0 = take (c + length acc)%nat L).
        { destruct Heof as [Hemp _]. destruct Hpre as [t Ht].
          rewrite /pst_empty in Hemp.
          rewrite -Hrp Hemp Ht take_app_length. reflexivity. }
        iAssert (|==> eof_shot pn (ps_ws s0)
                      ∗ (eof_pending pn
                         ∨ ∃ w : list (bv 8), eof_shot pn w
                             ∗ ⌜w = ps_ws s0 /\ ps_wo s0 = false⌝))%I
          with "[Hoe]" as ">[#Hs Hoe]".
        { iDestruct "Hoe" as "[Hp | Hoe]".
          - iMod (eof_shoot pn (ps_ws s0) with "Hp") as "#Hs".
            iModIntro. iSplitR; [ iExact "Hs" | ].
            iRight. iExists (ps_ws s0). iSplitR; [ iExact "Hs" | ].
            iPureIntro. split; [ reflexivity | by destruct Heof as [_ Hwo] ].
          - iDestruct "Hoe" as (w0) "[#Hs0 %Hw0]". iModIntro.
            destruct Hw0 as [Hw1 Hw2].
            iSplitR; [ rewrite -Hw1; iExact "Hs0" | ].
            iRight. iExists w0. iSplitR; [ iExact "Hs0" | ].
            iPureIntro. split; [ exact Hw1 | exact Hw2 ]. }
        iMod ("Hclose" with "[Hf Hh Hbw Hbr Hoe Hro]") as "_".
        { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Hoe Hro". by iPureIntro. }
        iModIntro. iFrame "Ha". rewrite /pipe_rQe.
        iSplitL "Hr"; [ rewrite /pipe_rQ; iFrame "Hr"; by iPureIntro | ].
        iIntros "_". rewrite -Hws. iExact "Hs".
      - (* not an end-of-file: the node records nothing at all *)
        iModIntro. iFrame "Ha". rewrite /pipe_rQe.
        iSplitL "Hr"; [ rewrite /pipe_rQ; iFrame "Hr"; by iPureIntro | ].
        iIntros "%He". by destruct (Hne He). }
    (* THE READ LINK *)
    rewrite /pipe_rlink. iIntros (s b) "%Hnext Ha".
    iDestruct "HQ" as "[Hr %Hacc]".
    iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Hoe & Hro)" "Hclose".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iDestruct (rcur_agree with "Hbr Hr") as %Hrp.
    (* THE DEQUEUED BYTE IS THE LINE'S, at the reader's own cursor: (P1) at
       the byte, which is design SS3's cat row. *)
    assert (HLb : L !! (c + length acc)%nat = Some b).
    { rewrite -Hrp. eapply prefix_lookup_Some; [ | exact Hpre ].
      rewrite /pst_next in Hnext. exact Hnext. }
    (* (P5) IS WHAT A READ RESTORES, and it restores it because the link
       fired at all: [pst_next s0 = Some b] is [ps_rp s0 < length
       (ps_ws s0)]. *)
    assert (Hlt : (ps_rp s0 < length (ps_ws s0))%nat).
    { apply lookup_lt_is_Some_1. rewrite /pst_next in Hnext. by exists b. }
    assert (Hlenb : length (acc ++ [b]) = (length acc + 1)%nat)
      by (rewrite length_app /=; lia).
    assert (Hacc' : acc ++ [b] = take (length acc + 1)%nat (drop c L)).
    { replace (length acc + 1)%nat with (S (length acc)) by lia.
      rewrite (take_S_r (drop c L) (length acc) b);
        [ by rewrite -Hacc | rewrite lookup_drop; exact HLb ]. }
    iMod (pipe_queue_update _ _ _ (pst_read s0) with "Ha Hf") as "[Ha Hf]".
    iMod (rcur_move pn _ _ (S (ps_rp s0)) with "Hbr Hr") as "[Hbr Hr]".
    iMod ("Hclose" with "[Hf Hh Hbw Hbr Hoe Hro]") as "_".
    { iNext. iExists (pst_read s0). iFrame "Hf".
      rewrite !pst_read_ws !pst_read_rp. iFrame "Hh Hbw Hbr".
      iSplitR; [ by iPureIntro | ]. iSplitR; [ iPureIntro; lia | ].
      iSplitL "Hoe".
      - iDestruct "Hoe" as "[Hp | Hoe]"; [ by iLeft | ].
        iDestruct "Hoe" as (w0) "[#Hs %Hw0]". iRight. iExists w0. iFrame "Hs".
        iPureIntro. exact Hw0.
      - iDestruct "Hro" as "[Hp | [#Hs %Hro]]"; [ by iLeft | ].
        iRight. iFrame "Hs". iPureIntro. exact Hro. }
    iModIntro. iFrame "Ha".
    iApply (IH (acc ++ [b]) with "Hinv [Hr]").
    rewrite /pipe_rQ Hlenb.
    replace (c + (length acc + 1))%nat with (S (ps_rp s0)) by lia.
    iFrame "Hr". by iPureIntro.
  Qed.

  (* THE PAYMENT, which is what [UkReadPipe.wp_uk_ecall_read_pipe_std]
     takes at ledger slot 0.  No bound premise: a read takes what is there. *)
  Lemma pipe_rpay_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (c cap : nat) :
    pipe_inv pn γp L -∗ rcur pn c -∗
    pipe_rpay (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) cap.
  Proof using .
    iIntros "#Hinv Hr". rewrite /pipe_rpay. iLeft.
    iApply (pipe_rchain_of_inv pn γp L c [] cap with "Hinv [Hr]").
    rewrite /pipe_rQ /= Nat.add_0_r. iFrame "Hr". by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  5a. THE READER-SIDE LOWER BOUND (design SS4.3g, the round's third    *)
  (*      owed item)                                                      *)
  (*                                                                      *)
  (*  [pws_lb_of_inv] is the WRITER's: a write permit at [c] says the      *)
  (*  first [c] bytes of the line are in.  This is its mirror one cursor   *)
  (*  over, and it is what lets a READER say so -- which is the only way   *)
  (*  cat can produce a witness that "a byte reached the reader" for the   *)
  (*  two children's exclusion ([PipeBoth]'s [YR]).  It needs (P5), and    *)
  (*  nothing weaker: see [pipe_body_needs_P5].                            *)
  (* ------------------------------------------------------------------- *)
  Lemma pws_lb_of_rcur (E : coPset) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (c : nat) :
    ↑pipeN ⊆ E ->
    pipe_inv pn γp L -∗ rcur pn c ={E}=∗ rcur pn c ∗ pws_lb pn (take c L).
  Proof using .
    intros HE. iIntros "#Hinv Hr".
    iInv "Hinv" as (s0)
      ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
    iDestruct (rcur_agree with "Hbr Hr") as %Hrp.
    iDestruct (pws_auth_lb with "Hh") as "[Hh #Hlb]".
    (* (P1) + (P5): the reader's cursor is inside the contents, and the
       contents are a prefix of the line, so the line's first [c] bytes ARE
       the contents' first [c] bytes. *)
    assert (Hle : (c <= length (ps_ws s0))%nat) by (rewrite -Hrp; exact Hrle).
    assert (Htk : take c L = take c (ps_ws s0)).
    { destruct Hpre as [t Ht]. rewrite Ht take_app_le; [ reflexivity | lia ]. }
    iDestruct (pws_lb_weaken pn (ps_ws s0) (take c L) with "Hlb") as "#Hlb'".
    { rewrite Htk. apply prefix_take. }
    iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro]") as "_".
    { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro". by iPureIntro. }
    iModIntro. iFrame "Hr". iExact "Hlb'".
  Qed.

  (* ...AND THE EXCLUSION THE ROUND SPENDS (design SS4.3g, R2's item 3).
     [PipeBoth]'s two child byte steps take [box (XL -* YR ={Eex}=* False)]
     with [Eex ⊆ ⊤ ∖ ↑uartN Uart0 ∖ ↑N]; at the honest instance [XL] is
     echo's write permit at ZERO (the left child's exec failed, so it still
     holds its whole lend and NOTHING was ever written) and [YR] is "a byte
     reached the reader".  The two cannot both hold: an untouched write
     permit forces the contents EMPTY (P2), and an empty history has no
     lower bound of length one.  The line's non-emptiness is the only
     premise, and every line ends in a newline. *)
  Lemma pipe_excl_wtok_lb (E : coPset) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) :
    ↑pipeN ⊆ E -> L <> [] ->
    pipe_inv pn γp L -∗
    □ (wcur pn 0%nat -∗ pws_lb pn (take 1%nat L) ={E}=∗ False).
  Proof using .
    intros HE HL. iIntros "#Hinv !> Hw #Hlb".
    iInv "Hinv" as (s0)
      ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
    iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
    assert (Hws : ps_ws s0 = []) by (by apply nil_length_inv).
    iDestruct (pws_lb_prefix with "Hh Hlb") as %Hp.
    rewrite Hws in Hp. apply prefix_nil_inv in Hp.
    exfalso. destruct L as [| b L']; [ by destruct (HL eq_refl) | ].
    rewrite /= in Hp. discriminate.
  Qed.

  (* the instance the round applies, at the protocol's own namespace --
     disjoint from the console port's and from the block family's, which is
     what [PipeBoth.pblk2_cstep_L]'s mask side condition asks. *)
  Lemma pipe_excl_wtok_lb_pipeN (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) :
    L <> [] ->
    pipe_inv pn γp L -∗
    □ (wcur pn 0%nat -∗ pws_lb pn (take 1%nat L) ={↑pipeN}=∗ False).
  Proof using .
    intros HL. exact (pipe_excl_wtok_lb (↑pipeN) pn γp L
                        ltac:(reflexivity) HL).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  6.  SH'S END-OF-ROUND READING (design SS4.2, as amended by SH-PIPE)  *)
  (* ------------------------------------------------------------------- *)

  (* PRan: echo's lower bound and (P1) pin the contents to the line, and
     (P3) says the reader's snapshot IS the contents. *)
  Lemma pipe_body_ran (pn : pnames) (γp : pipe_names) (L w : list (bv 8)) :
    pipe_body pn γp L -∗ pws_lb pn L -∗ eof_shot pn w -∗ ⌜w = L⌝.
  Proof using .
    iIntros "Hb #Hlb #Hs".
    iDestruct "Hb" as (s) "(Hf & Hh & _ & _ & %Hpre & _ & Hoe & _)".
    iDestruct (pws_lb_prefix with "Hh Hlb") as %HL.
    assert (Hws : ps_ws s = L).
    { apply (prefix_length_eq _ _ Hpre). by apply prefix_length. }
    iDestruct "Hoe" as "[Hp | Hoe]".
    - iDestruct (eof_pending_shot with "Hp Hs") as %[].
    - iDestruct "Hoe" as (w') "[#Hs' %Hw']".
      iDestruct (eof_shot_agree with "Hs Hs'") as %<-.
      iPureIntro. destruct Hw' as [Hw1 _]. by rewrite Hw1.
  Qed.

  (* PExecL: sh has the START token back, so (P2) forces the pipe empty and
     (P3) makes the reader's snapshot empty too -- cat printed nothing. *)
  Lemma pipe_body_execL (pn : pnames) (γp : pipe_names) (L w : list (bv 8)) :
    pipe_body pn γp L -∗ wtok pn -∗ eof_shot pn w -∗ ⌜w = []⌝.
  Proof using .
    iIntros "Hb Ht #Hs".
    iDestruct "Hb" as (s) "(Hf & _ & Hbw & _ & _ & _ & Hoe & _)".
    rewrite /wtok. iDestruct (wcur_agree with "Hbw Ht") as %Hlen.
    assert (Hws : ps_ws s = []) by (by apply nil_length_inv).
    iDestruct "Hoe" as "[Hp | Hoe]".
    - iDestruct (eof_pending_shot with "Hp Hs") as %[].
    - iDestruct "Hoe" as (w') "[#Hs' %Hw']".
      iDestruct (eof_shot_agree with "Hs Hs'") as %<-.
      iPureIntro. destruct Hw' as [Hw1 _]. by rewrite Hw1.
  Qed.

  Lemma pipe_round_ran (pn : pnames) (γp : pipe_names) (L w : list (bv 8)) :
    pipe_inv pn γp L -∗ pws_lb pn L -∗ eof_shot pn w ={⊤}=∗ ⌜w = L⌝.
  Proof using .
    iIntros "#Hinv #Hlb #Hs". iInv "Hinv" as ">Hb" "Hclose".
    iDestruct (pipe_body_ran with "Hb Hlb Hs") as %Heq.
    iMod ("Hclose" with "[Hb]") as "_"; [ iNext; iExact "Hb" | ].
    iModIntro. by iPureIntro.
  Qed.

  Lemma pipe_round_execL (pn : pnames) (γp : pipe_names) (L w : list (bv 8)) :
    pipe_inv pn γp L -∗ wtok pn -∗ eof_shot pn w ={⊤}=∗ wtok pn ∗ ⌜w = []⌝.
  Proof using .
    iIntros "#Hinv Ht #Hs". iInv "Hinv" as ">Hb" "Hclose".
    iDestruct (pipe_body_execL with "Hb Ht Hs") as %Heq.
    iMod ("Hclose" with "[Hb]") as "_"; [ iNext; iExact "Hb" | ].
    iModIntro. iFrame "Ht". by iPureIntro.
  Qed.

  (* PExecR (design SS4.2, and the arm lane PIPE-PROTO-2 adds): the left
     child came back MID-LINE -- it holds its permit at some cursor [c] and
     (P4)'s shot, because its own write stopped on a shut read end.  Then the
     pipe's frozen contents are the line's first [c] bytes, no more and no
     less.  [pipe_body_execL] is this at [c = 0] and needs no shot; the shot
     is what lets sh KNOW the left child stopped rather than never started. *)
  Lemma pipe_body_short (pn : pnames) (γp : pipe_names) (L w : list (bv 8))
      (c : nat) :
    pipe_body pn γp L -∗ wcur pn c -∗ eof_shot pn w -∗ ⌜w = take c L⌝.
  Proof using .
    iIntros "Hb Hc #Hs".
    iDestruct "Hb" as (s) "(Hf & _ & Hbw & _ & %Hpre & _ & Hoe & _)".
    iDestruct (wcur_agree with "Hbw Hc") as %Hlen.
    assert (Hws : ps_ws s = take c L).
    { destruct Hpre as [t Ht]. rewrite -Hlen Ht take_app_length. reflexivity. }
    iDestruct "Hoe" as "[Hp | Hoe]".
    - iDestruct (eof_pending_shot with "Hp Hs") as %[].
    - iDestruct "Hoe" as (w') "[#Hs' %Hw']".
      iDestruct (eof_shot_agree with "Hs Hs'") as %<-.
      iPureIntro. destruct Hw' as [Hw1 _]. by rewrite Hw1.
  Qed.

  Lemma pipe_round_short (pn : pnames) (γp : pipe_names) (L w : list (bv 8))
      (c : nat) :
    pipe_inv pn γp L -∗ wcur pn c -∗ eof_shot pn w ={⊤}=∗
    wcur pn c ∗ ⌜w = take c L⌝.
  Proof using .
    iIntros "#Hinv Hc #Hs". iInv "Hinv" as ">Hb" "Hclose".
    iDestruct (pipe_body_short with "Hb Hc Hs") as %Heq.
    iMod ("Hclose" with "[Hb]") as "_"; [ iNext; iExact "Hb" | ].
    iModIntro. iFrame "Hc". by iPureIntro.
  Qed.

  (* THE SYMMETRIC PAYLOAD.  A [wait(0)] cannot tell sh's two children apart
     (SH-PIPE's R-2: [wp_kshr_fork1] needs one payload at every return value
     and the pid-refuting form is dropped), so BOTH children exit with the
     same [Qc] and the side is told by which exclusive token came back. *)
  Definition pipe_Qc (pn : pnames) (PL PR : iProp Σ) : iProp Σ :=
    ((side_L pn ∗ PL) ∨ (side_R pn ∗ PR))%I.

  (* ...AND TWO ANSWERS CANNOT BOTH BE THE SAME SIDE. *)
  Lemma pipe_Qc_two (pn : pnames) (PL PR : iProp Σ) :
    pipe_Qc pn PL PR -∗ pipe_Qc pn PL PR -∗
    (side_L pn ∗ PL) ∗ (side_R pn ∗ PR).
  Proof using .
    rewrite /pipe_Qc.
    iIntros "[[HL HP] | [HR HP]] [[HL' HP'] | [HR' HP']]".
    - iDestruct (side_L_excl with "HL HL'") as %[].
    - iFrame "HL HP HR' HP'".
    - iFrame "HL' HP' HR HP".
    - iDestruct (side_R_excl with "HR HR'") as %[].
  Qed.

  (* the campaign's two payloads: echo's ("the line is in", or the start
     token back because its exec failed) and cat's (the frozen snapshot) *)
  (* THREE arms, not two (lane ECHO-PIPE's finding 2, closed here): the
     cursor at the line's END ("the line is in"), the cursor at ZERO (the
     left exec failed and the start token came straight back), or MID-LINE
     with (P4)'s shot -- which is the only other place echo can stop, since
     the copy-in fault is refuted by its own mapped source run and the kill
     is the taint.  The mid-line arm is what a DERAILED round hands back. *)
  Definition pipe_payL (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    (pws_lb pn L ∨ wtok pn ∨ (∃ c : nat, wcur pn c ∗ ro_shot pn))%I.
  Definition pipe_payR (pn : pnames) : iProp Σ :=
    (∃ w : list (bv 8), eof_shot pn w)%I.

  (* THE ROUND, OFF THE TWO EXIT PAYLOADS: one invariant access, and the
     alternative is decided. *)
  Lemma pipe_round_reading (pn : pnames) (γp : pipe_names) (L : list (bv 8)) :
    pipe_inv pn γp L -∗
    pipe_Qc pn (pipe_payL pn L) (pipe_payR pn) -∗
    pipe_Qc pn (pipe_payL pn L) (pipe_payR pn)
    ={⊤}=∗ ∃ w : list (bv 8),
      eof_shot pn w
      ∗ ((pws_lb pn L ∗ ⌜w = L⌝)                                  (* PRan *)
         ∨ (wtok pn ∗ ⌜w = []⌝)                        (* PExecL / PSilent *)
         ∨ (∃ c : nat, wcur pn c ∗ ro_shot pn ∗ ⌜w = take c L⌝)). (* PExecR *)
  Proof using .
    iIntros "#Hinv H1 H2".
    iDestruct (pipe_Qc_two with "H1 H2") as "[[_ HL] [_ HR]]".
    iDestruct "HR" as (w) "#Hs". rewrite /pipe_payL.
    iDestruct "HL" as "[#Hlb | [Ht | Hsh]]".
    - iMod (pipe_round_ran pn γp L w with "Hinv Hlb Hs") as %->.
      iModIntro. iExists L. iFrame "Hs". iLeft. iFrame "Hlb". by iPureIntro.
    - iMod (pipe_round_execL pn γp L w with "Hinv Ht Hs") as "[Ht %Hw]".
      iModIntro. iExists w. iFrame "Hs". iRight. iLeft. iFrame "Ht".
      by iPureIntro.
    - iDestruct "Hsh" as (c) "[Hc #Hsh]".
      iMod (pipe_round_short pn γp L w c with "Hinv Hc Hs") as "[Hc %Hw]".
      iModIntro. iExists w. iFrame "Hs". iRight. iRight. iExists c.
      iFrame "Hc Hsh". by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  7.  THE CONSUMER TEST, at the RESOURCE level                        *)
  (* ------------------------------------------------------------------- *)

  (* EVERY ARM of the write post hands echo its cursor back, because [Qe] IS
     [Q] -- which is what makes echo's four writes compose. *)
  Lemma pipe_wpost_cursor_line (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64) (c : nat)
      (Rk : iProp Σ) (n : nat) (r : mword 64) :
    pipe_wpost Pt (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c)
      Rk n r -∗
    (∃ k : nat, ⌜(k <= n)%nat⌝ ∗ pipe_wQ pn L c k)
    ∨ (app_taint
       ∗ pipe_wpay (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c) n).
  Proof using .
    iIntros "H". iDestruct (pipe_wpost_cursor with "H") as "[H | H]";
      [ | iRight; iExact "H" ]. iLeft.
    iDestruct "H" as (k) "[%Hk H]". iExists k. iSplitR; [ by iPureIntro | ].
    iDestruct "H" as "[(_ & _ & HQ) | [(_ & _ & _ & HQ) | (_ & _ & Hobs)]]".
    - iExact "HQ".
    - iExact "HQ".
    - iDestruct "Hobs" as (s) "[_ HQ]". rewrite /pipe_wQe.
      iDestruct "HQ" as "[$ _]".
  Qed.

  (* THE SAME READING, WITH THE REASON -- which is what a WRITER needs, and
     what lane ECHO-PIPE-2 spends.  Every arm hands the cursor back and says
     why the call stopped there: the whole run went in (or copyin could not
     read byte [k] of the caller's source, which a mapped run refutes), the
     writer was KILLED, or THE READ END IS SHUT -- and that last arm hands
     out (P4)'s shot, which is what makes every later write payable
     ([pipe_wpay_of_inv_after_short]).  [pipe_wpost_cursor_line] above is
     this without the reason. *)
  Lemma pipe_wpost_line_reason (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64) (c : nat)
      (Rk : iProp Σ) (n : nat) (r : mword 64) :
    pipe_wpost Pt (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c)
      Rk n r -∗
    (∃ k : nat, ⌜(k <= n)%nat⌝ ∗ pipe_wQ pn L c k
       ∗ (⌜k = n \/ ~ UserPtTree.uva_rmapped Pt
                        (uint (add_vec_int ua (Z.of_nat k)))⌝
          ∨ Rk ∨ ro_shot pn))
    ∨ (app_taint
       ∗ pipe_wpay (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c) n).
  Proof using .
    iIntros "H". iDestruct (pipe_wpost_cursor with "H") as "[H | H]";
      [ | iRight; iExact "H" ]. iLeft.
    iDestruct "H" as (k) "[%Hk H]". iExists k. iSplitR; [ by iPureIntro | ].
    iDestruct "H" as "[(_ & %Hs & HQ) | [(_ & _ & Hk & HQ) | (_ & _ & Hobs)]]".
    - iFrame "HQ". iLeft. by iPureIntro.
    - iFrame "HQ". iRight. by iLeft.
    - iDestruct "Hobs" as (s) "[%Hro HQ]".
      iDestruct (pipe_wQe_ro_shot pn L c k s Hro with "HQ") as "[$ #Hsh]".
      iRight. iRight. iExact "Hsh".
  Qed.

  (* ...AND EVERY ARM of the read post hands cat its cursor back, with the
     observation arm carrying the EOF snapshot at the turn of cat's loop
     where nothing was delivered (which is where [piperead] answered 0). *)
  Lemma pipe_rpost_img_line (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (c : nat) (Rk : iProp Σ) (n : nat) (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    pipe_rpost_img Pt (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c)
      Rk n r M' addr -∗
    (∃ (acc : list (bv 8)) (d : nat),
       ⌜(length acc <= n)%nat⌝ ∗ pipe_rQ pn L c acc
       ∗ ((⌜(d < n)%nat /\ length acc = d
            /\ r = (mword_of_int (Z.of_nat d) : mword 64)⌝
           ∗ (⌜d = 0%nat⌝ -∗ eof_shot pn (take (c + length acc)%nat L)))
          ∨ pipe_rstop_noobs Pt addr Rk n d r))
    ∨ (app_taint
       ∗ pipe_rpay (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) n).
  Proof using .
    iIntros "H". iDestruct (pipe_rpost_img_cursor with "H") as "[H | H]";
      [ | iRight; iExact "H" ]. iLeft.
    iDestruct "H" as (acc d) "(%H1 & %H2 & [Hobs | (%H3 & Hno & HQ)])".
    - iDestruct "Hobs" as "[%Hpure Hobs]".
      iDestruct "Hobs" as (s) "[%Hs Hqe]".
      iDestruct "Hqe" as "[HQ Hwand]".
      iExists acc, d. iSplitR; [ by iPureIntro | ]. iFrame "HQ".
      iLeft. iSplitR; [ by iPureIntro | ]. iIntros "%Hd0".
      iApply "Hwand". iPureIntro. rewrite /pst_eof. split; [ apply Hs | ].
      by apply (proj2 Hs).
    - iExists acc, d. iSplitR; [ by iPureIntro | ]. iFrame "HQ".
      iRight. iExact "Hno".
  Qed.

  (* ...AND THE SAME READING A PROGRAM CAN WALK ON (lane CAT-PIPE's finding
     3, folded back here because it is entirely general).
     [pipe_rpost_img_line] above is the right reading for
     [pipe_proto_test]'s question and the WRONG one for a walk: its proof
     drops the post's IMAGE ROW -- the one fact that turns the ghost [acc]
     into the caller's buffer function -- and drops [length acc = d] on the
     non-observation arms, so a reader cannot say how many of its buffer
     bytes the call filled.  This is the same reading with both kept, and
     with the four [pipe_rstop_noobs] arms SORTED BY WHAT A READER'S LOOP
     BRANCHES ON: the answer is a count [d], or it is -1 and then [d = 0]
     and one of three things happened.  ([pipe_rstop_noobs] is NOT pure --
     its kill arm carries [Rk] -- so it is destructed in the logic.) *)
  Lemma pipe_rpost_line (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (c : nat) (Rk : iProp Σ) (n : nat) (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    pipe_rpost_img Pt (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c)
      Rk n r M' addr -∗
    (∃ (acc : list (bv 8)) (d : nat),
       ⌜(length acc <= n)%nat /\ length acc = d⌝
       ∗ ⌜(forall i : nat, (i < d)%nat ->
             uint (add_vec_int addr (Z.of_nat i))
             = (uint addr + Z.of_nat i)%Z) ->
          forall j : nat, (j < d)%nat ->
            M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (acc !!! j)⌝
       ∗ pipe_rQ pn L c acc
       ∗ ((⌜r = (mword_of_int (Z.of_nat d) : mword 64)⌝
           ∗ (⌜d = 0%nat⌝ -∗ ⌜(0 < n)%nat⌝ -∗
                eof_shot pn (take (c + d)%nat L)))
          ∨ (⌜r = (mword_of_int (-1) : mword 64) /\ d = 0%nat⌝
             ∗ (⌜~ UserPtTree.uva_wmapped Pt
                     (uint (add_vec_int addr (Z.of_nat d)))⌝
                ∨ Rk ∨ ⌜n = 0%nat⌝))))
    ∨ (app_taint
       ∗ pipe_rpay (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) n).
  Proof using .
    iIntros "H". iDestruct (pipe_rpost_img_cursor with "H") as "[H | H]";
      [ | iRight; iExact "H" ]. iLeft.
    iDestruct "H" as (acc d) "(%H1 & %H2 & [Hobs | (%H3 & Hno & HQ)])".
    - (* THE OBSERVATION: the ring ran dry at node [acc] *)
      iDestruct "Hobs" as "[%Hpure Hobs]".
      iDestruct "Hobs" as (s) "[%Hs Hqe]".
      iDestruct "Hqe" as "[HQ Hwand]".
      iExists acc, d. iSplitR; [ iPureIntro; split; [ exact H1 | apply Hpure ] | ].
      iSplitR; [ by iPureIntro | ]. iFrame "HQ".
      iLeft. iSplitR; [ iPureIntro; apply Hpure | ].
      iIntros "%Hd0 _".
      assert (Hacc : length acc = d) by apply Hpure.
      rewrite -Hacc.
      iApply "Hwand". iPureIntro. rewrite /pst_eof. split; [ apply Hs | ].
      apply (proj2 Hs). exact Hd0.
    - (* THE FOUR NON-OBSERVING STOPS *)
      iExists acc, d. iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iFrame "HQ".
      rewrite /pipe_rstop_noobs.
      iDestruct "Hno" as "[%Hmet | [%Hflt | [[%Hkp Hk] | %Hsg]]]".
      + iLeft. iSplitR; [ iPureIntro; apply Hmet | ].
        iIntros "%Hz %Hpos". exfalso. destruct Hmet as [Hdn _]. lia.
      + destruct Hflt as (Hdn & Hnm & [(Hd0 & Hr) | (Hd0 & Hr)]).
        * iLeft. iSplitR; [ by iPureIntro | ].
          iIntros "%Hz _". exfalso. lia.
        * iRight. iSplitR; [ by iPureIntro | ]. iLeft. by iPureIntro.
      + iRight. iSplitR; [ iPureIntro; split; [ apply Hkp | apply Hkp ] | ].
        iRight. by iLeft.
      + iRight. iSplitR; [ iPureIntro; split; [ apply Hsg | apply Hsg ] | ].
        iRight. iRight. iPureIntro. apply Hsg.
  Qed.

  (* THE READING THAT CLOSES THE ROUND: the bytes the reader took out of
     the pipe ARE the line.  (P1) put them at [L]'s positions, the round's
     reading says the frozen contents are the whole of [L], and cat's own
     node says [acc] is that prefix -- so [acc = L]. *)
  Lemma pipe_reader_saw_line (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (acc : list (bv 8)) :
    pipe_inv pn γp L -∗ pws_lb pn L -∗ pipe_rQ pn L 0 acc -∗
    eof_shot pn (take (0 + length acc)%nat L) ={⊤}=∗
    pipe_rQ pn L 0 acc ∗ ⌜acc = L⌝.
  Proof using .
    iIntros "#Hinv #Hlb HQ #Hs".
    iMod (pipe_round_ran pn γp L (take (0 + length acc)%nat L)
            with "Hinv Hlb Hs") as %Heq.
    iDestruct "HQ" as "[Hr %Hacc]". iModIntro.
    iSplitL "Hr"; [ rewrite /pipe_rQ; iFrame "Hr"; by iPureIntro | ].
    iPureIntro. rewrite drop_0 in Hacc. cbn in Heq. rewrite Heq in Hacc.
    exact Hacc.
  Qed.

  (* THE TEST ITSELF, and it is a RESOURCE-LEVEL test (the brief's
     alternative): a full WP test would have to supply three programs'
     instruction streams, registers and heaps, and the two leaves it would
     go through are already landed and stated (lane PIPE-STD).  What is
     tested here is exactly the seam this lane owns -- the payments BUILT at
     the shapes the two [_std] leaves take, and the round's reading DERIVED
     from what their posts hand back:

       pipe(2) -> register  ->  the left child's whole-line write payment
                            ->  the right child's read payment
                            ->  "the reader saw L"                          *)
  Lemma pipe_proto_test (γp : pipe_names) (L : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (cap : nat) :
    (forall k : nat, (k < length L)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! k)) ->
    pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗
    ∃ pn : pnames,
      (* sh, right after pipe(2): the registration its two pipe rows' closes
         are paid with, the handle, and the two side tokens *)
      pipe_reg γp ∗ pipe_inv pn γp L ∗ side_L pn ∗ side_R pn
      (* echo's payment for the WHOLE line *)
      ∗ pipe_wpay (pn_queue γp) M ua (pipe_wQ pn L 0) (pipe_wQe pn L 0)
          (length L)
      (* cat's payment for its first read *)
      ∗ pipe_rpay (pn_queue γp) (pipe_rQ pn L 0) (pipe_rQe pn L 0) cap
      (* ...and the round's reading, off the two exit payloads *)
      ∗ (∀ acc : list (bv 8),
           pws_lb pn L -∗ pipe_rQ pn L 0 acc -∗
           eof_shot pn (take (0 + length acc)%nat L) ={⊤}=∗ ⌜acc = L⌝).
  Proof using .
    intros HM.
    assert (Hle0 : (0 + length L <= length L)%nat) by lia.
    assert (HM0 : forall k : nat, (k < length L)%nat ->
              M !! uint (add_vec_int ua (Z.of_nat k))
              = Some (L !!! (0 + k)%nat)).
    { intros k Hk. rewrite Nat.add_0_l. by apply HM. }
    iIntros "Hfrag".
    iMod (pipe_proto_alloc γp L with "Hfrag")
      as (pn) "(#Hinv & Hw & Hr & HsL & HsR & #Hreg)".
    rewrite /wtok /rtok.
    iMod (pws_lb_of_inv pn γp L 0 with "Hinv Hw") as "[Hw #Hlb0]".
    iModIntro. iExists pn. iFrame "Hreg Hinv HsL HsR".
    iSplitL "Hw".
    { iApply (pipe_wpay_of_inv pn γp L M ua 0 (length L) Hle0 HM0
                with "Hinv Hw Hlb0"). }
    iSplitL "Hr".
    { iApply (pipe_rpay_of_inv pn γp L 0 cap with "Hinv Hr"). }
    iIntros (acc) "#Hlb HQ #Hs".
    iMod (pipe_reader_saw_line pn γp L acc with "Hinv Hlb HQ Hs")
      as "[_ %Hacc]".
    iModIntro. by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  7b.  THE DERAILED RUN (lane PIPE-PROTO-2's headline)                 *)
  (* ------------------------------------------------------------------- *)

  (* ONE ROUND, DERAILED, end to end at the resource level: a write stops
     SHORT because the read end is shut (design SS4.2's [PExecR] world), and
     the very next write -- at ANOTHER buffer, ANOTHER count and with NO
     cursor -- is payable anyway.

     The three arms out are exactly the three reachable stops, and the
     mapped-source premise is what removes the fourth (copyin cannot be the
     reason for a caller that owns its run; ECHO-PIPE proves that premise
     from [UkRunSys.usrc_ok]):

       - the whole run went in: the cursor is at [c + n] and echo's chain
         composes exactly as before;
       - the writer was KILLED: [Rk] in hand, the cursor wherever it got to
         (the taint is the campaign's price for a kill -- ECHO-PIPE's route
         (c), still owed by the kernel's write post);
       - THE READ END WAS SHUT, or the pipe was tainted: the second write is
         paid, and this is the arm 3.1b opened.

     This is what retires [UEchoPipe.ep_derail]: its body is
     [pipe_wpay_of_inv_after_short] at [R := ep_halt pn L]. *)
  Lemma pipe_proto_derail_test (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64) (c n : nat)
      (Rk : iProp Σ) (r : mword 64)
      (M2 : gmap Z (bv 8)) (ua2 : mword 64) (n2 : nat) (R : iProp Σ) :
    (forall j : nat, (j < n)%nat ->
       UserPtTree.uva_rmapped Pt (uint (add_vec_int ua (Z.of_nat j)))) ->
    pipe_inv pn γp L -∗ R -∗
    pipe_wpost Pt (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c)
      Rk n r -∗
    pipe_wQ pn L c n
    ∨ (Rk ∗ ∃ k : nat, pipe_wQ pn L c k)
    ∨ pipe_wpay (pn_queue γp) M2 ua2 (fun _ : nat => R)
        (fun (_ : nat) (_ : pipe_st) => R) n2.
  Proof using .
    intros Hmap. iIntros "#Hinv HR H".
    iDestruct (pipe_wpost_line_reason with "H") as "[H | [#Ht _]]"; last first.
    { (* the pipe was tainted: the payment is the credential's *)
      iRight. iRight. iApply (pipe_wpay_taint with "Ht"). }
    iDestruct "H" as (k) "(%Hk & HQ & [%Hs | [Hkl | #Hsh]])".
    - (* the whole run went in -- the copy-in reason is refuted *)
      assert (Hkn : k = n).
      { destruct Hs as [Hkn | Hnm]; [ exact Hkn | ].
        destruct (decide (k = n)) as [Hkn | Hne]; [ exact Hkn | ].
        exfalso. apply Hnm. apply Hmap. lia. }
      subst k. iLeft. iExact "HQ".
    - iRight. iLeft. iFrame "Hkl". iExists k. iExact "HQ".
    - (* THE DERAIL: the shot pays the next write outright *)
      iRight. iRight.
      iApply (pipe_wpay_of_inv_after_short pn γp L M2 ua2 R n2
                with "Hinv Hsh HR").
  Qed.


  (* ------------------------------------------------------------------- *)
  (*  8.  THE SHORT ROUND, AND WHY THE PROTOCOL CANNOT REFUTE IT          *)
  (*      (design SS4.3v as ruled -- REFUTED here at its second bullet;   *)
  (*       lane SH-PIPE-ROUND-10)                                         *)
  (*                                                                      *)
  (*  THE ARM.  [UShPipeAssembly.pipe_round_reading_at] leaves one block   *)
  (*  beside the round's four codes: cat printed a PROPER PREFIX of the    *)
  (*  line ([0 < c < length L]) while echo's exit says its write stopped   *)
  (*  because the READ END WAS SHUT ([pipe_payL]'s third arm).  Design     *)
  (*  SS4.3v rules that a FIRST-ENDER one-shot refutes it: the writer's    *)
  (*  observation shoots [RoFirst] (it sees the read end shut while no     *)
  (*  end-of-file has been read), the reader's end-of-file shoots          *)
  (*  [EofFirst], and two values of one agreement cell are [False].        *)
  (*                                                                      *)
  (*  THE FIRST HALF IS MINTABLE AND THE SECOND IS NOT.  [RoFirst] costs   *)
  (*  nothing: the writer's observation node ([pipe_wchain_of_inv]'s       *)
  (*  [pipe_olink] arm) opens this body, and (P3)'s LEFT arm being there   *)
  (*  IS the fact that no end-of-file has been read.  [EofFirst] cannot    *)
  (*  be minted:                                                           *)
  (*  the reader's end-of-file node would have to know that the read end   *)
  (*  is still OPEN at the state it fires at, and                          *)
  (*                                                                      *)
  (*    - [PipeQueue.pipe_olink] is a [forall s] with NO premise, and      *)
  (*      [PipeQueue.pipe_rlink] carries no [ps_ro] premise either -- lane *)
  (*      PQ-FLAG measured why and design SS3.1 records it: [piperead]      *)
  (*      never loads [pi->readopen], so the only route is the caller's    *)
  (*      own [pipe_ref γp false q], and the FILE layer cannot supply the  *)
  (*      end (nobody publishes that a pipe file's two ends are            *)
  (*      complementary);                                                  *)
  (*    - and no addition to THIS BODY can supply it either, because the   *)
  (*      close link is FREE AT BOTH ENDS by [PipeReg.pipe_reg]'s own      *)
  (*      contract -- a registered pipe is one whose ends may be closed by *)
  (*      anybody at any time without anybody owing anything -- so the     *)
  (*      fact that the read end is still open is not a consequence of any *)
  (*      resource the reader can hold.                                    *)
  (*                                                                      *)
  (*  WHAT IS MECHANISED BELOW.  [pipe_short_trace]: the short round is a  *)
  (*  RUN OF THIS PROTOCOL'S OWN TRANSITION SYSTEM -- every premise the    *)
  (*  landed links put on every step is met, in order (echo's [c] writes   *)
  (*  at both flags open, the read end's close, echo's observation at a    *)
  (*  shut read end with its own end still open, the write end's close,    *)
  (*  cat's [c] reads, cat's end-of-file).  [pipe_short_round_realisable]  *)
  (*  and [pipe_short_round_payloads]: the two EXIT PAYLOADS of that run   *)
  (*  are derivable from the pipe's birth alone, so the pair is not merely *)
  (*  unrefuted, it is REACHABLE.  [pipe_no_short_not_of_inv]: therefore   *)
  (*  the law below cannot be proved from the invariant.                   *)
  (*                                                                      *)
  (*  [pipe_no_short] is that law, NAMED, so that the round can take it as *)
  (*  one antecedent and whoever buys the reader-side fact can discharge   *)
  (*  it in one place.                                                     *)
  (* ------------------------------------------------------------------- *)

  (* THE LAW THE ROUND IS OWED: a proper prefix of the line cannot have
     been printed by a reader that saw an end-of-file while the writer's
     halt says the read end was shut.  True of the machine -- the read end
     is shut only by cat's own exit, which comes after cat's end-of-file
     read, and an end-of-file needs every write end shut, so the two views
     order the two closes oppositely -- and NOT a consequence of the
     protocol (see [pipe_short_round_payloads]). *)
  Definition pipe_no_short (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    (□ (∀ c : nat, ⌜(0 < c)%nat /\ (c < length L)%nat⌝ -∗
          ro_shot pn -∗ eof_shot pn (take c L) ={⊤}=∗ False))%I.

  Global Instance pipe_no_short_persistent pn L :
    Persistent (pipe_no_short pn L).
  Proof using . rewrite /pipe_no_short. apply _. Qed.

  (* THE RUN.  Nothing here is about ghosts: it is the pure check that the
     short round's states are the ones the landed links step between, and
     that each link's premises hold at the state it fires at.  [pipe_wlink]
     asks for BOTH flags open (lanes PQ-FLAG / PQ-FLAG-2) and gets them;
     [pipe_rlink] asks only for a byte to be there; [pipe_clink] and
     [pipe_olink] ask for nothing at all -- which is the whole finding. *)
  Lemma pipe_short_trace (L : list (bv 8)) (c : nat) :
    (0 < c)%nat -> (c < length L)%nat ->
    (* (1) echo's [c] write links, each at BOTH ends open *)
    (forall j : nat, (j < c)%nat ->
       ps_wo (MkPipeSt (take j L) 0%nat true true) = true
       /\ ps_ro (MkPipeSt (take j L) 0%nat true true) = true
       /\ pst_write (L !!! j) (MkPipeSt (take j L) 0%nat true true)
          = MkPipeSt (take (S j) L) 0%nat true true)
    (* (2) the READ end is shut -- the close link needs nothing *)
    /\ pst_close false (MkPipeSt (take c L) 0%nat true true)
       = MkPipeSt (take c L) 0%nat false true
    (* (3) echo's observation fires HERE: the read end is shut and its own
       end is still open, which is [pipe_wpost]'s third arm and the state
       [pipe_wQe] shoots [ro_shot] at *)
    /\ ps_ro (MkPipeSt (take c L) 0%nat false true) = false
    /\ ps_wo (MkPipeSt (take c L) 0%nat false true) = true
    (* (4) echo exits: the WRITE end is shut *)
    /\ pst_close true (MkPipeSt (take c L) 0%nat false true)
       = MkPipeSt (take c L) 0%nat false false
    (* (5) cat's [c] read links, each with its byte in the ring *)
    /\ (forall j : nat, (j < c)%nat ->
          pst_next (MkPipeSt (take c L) j false false) = Some (L !!! j)
          /\ pst_read (MkPipeSt (take c L) j false false)
             = MkPipeSt (take c L) (S j) false false)
    (* (6) ...and cat's observation is an END OF FILE -- at a state whose
       read end has been shut since (2), which is exactly the premise a
       first-ender shot would need and cannot have *)
    /\ pst_eof (MkPipeSt (take c L) c false false)
    /\ ps_ro (MkPipeSt (take c L) c false false) = false.
  Proof using .
    intros Hc0 HcL. split_and!.
    - intros j Hj. split_and!; [ reflexivity | reflexivity | ].
      rewrite /pst_write /=. f_equal. symmetry.
      apply take_S_r, list_lookup_lookup_total_lt. lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros j Hj. split; [ | reflexivity ].
      rewrite /pst_next /=. rewrite lookup_take; [ | lia ].
      apply list_lookup_lookup_total_lt. lia.
    - rewrite /pst_eof /pst_empty /=. split; [ | reflexivity ].
      rewrite length_take. lia.
    - reflexivity.
  Qed.

  (* THE RUN'S TWO EXIT PAYLOADS, BUILT.  What the round reads off the two
     children is [pipe_payL]'s third arm on the left and [pipe_payR] on the
     right; here they are, out of the pipe's birth state and nothing else,
     at a cursor that is a PROPER PREFIX of the line. *)
  Lemma pipe_short_round_realisable (γp : pipe_names) (L : list (bv 8))
      (c : nat) :
    (0 < c)%nat -> (c <= length L)%nat ->
    pipe_qauth (pn_queue γp) pst0 -∗ pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗
    ∃ pn : pnames,
      pipe_inv pn γp L
      ∗ pipe_qauth (pn_queue γp) (MkPipeSt (take c L) c false false)
      (* echo's halt: the cursor and (P4)'s shot *)
      ∗ wcur pn c ∗ ro_shot pn
      (* cat's exit: the frozen snapshot at the SAME cursor *)
      ∗ eof_shot pn (take c L)
      ∗ rcur pn c ∗ side_L pn ∗ side_R pn.
  Proof using .
    intros Hc0 HcL. iIntros "Ha Hf".
    set (s := MkPipeSt (take c L) c false false).
    iMod (pipe_queue_update _ _ _ s with "Ha Hf") as "[Ha Hf]".
    iMod (own_alloc (●ML ((take c L) : list (leibnizO (bv 8))))) as (gh) "Hh";
      [ apply mono_list_auth_valid | ].
    iMod (own_alloc
            (Cinr (to_agree ((take c L) : leibnizO (list (bv 8))))
             : pipe_eofR)) as (ge) "#He"; [ done | ].
    iMod (own_alloc (Cinr (to_agree ()) : pipe_roR)) as (go) "#Ho"; [ done | ].
    iMod (ghost_var_alloc c) as (gw) "Hw".
    iMod (ghost_var_alloc c) as (gr) "Hr".
    iMod (own_alloc (Excl ())) as (gl) "Hsl"; [ done | ].
    iMod (own_alloc (Excl ())) as (gs) "Hsr"; [ done | ].
    set (pn := MkPNames gh ge go gw gr gl gs).
    iDestruct (ghost_var_split (pn_wcur pn) c (1/2) (1/2) with "[Hw]")
      as "[Hw1 Hw2]"; [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split (pn_rcur pn) c (1/2) (1/2) with "[Hr]")
      as "[Hr1 Hr2]"; [ by rewrite Qp.half_half | ].
    assert (Hlen : length (take c L) = c) by (rewrite length_take; lia).
    iMod (inv_alloc pipeN ⊤ (pipe_body pn γp L) with "[Hf Hh Hw1 Hr1]")
      as "#Hinv".
    { iNext. iExists s. rewrite /s /=. rewrite Hlen. iFrame "Hf Hh Hw1 Hr1".
      iSplitR; [ iPureIntro; apply prefix_take | ].
      iSplitR; [ iPureIntro; lia | ].
      iSplitR.
      - iRight. iExists (take c L). rewrite /eof_shot. iFrame "He".
        iPureIntro. split; reflexivity.
      - iRight. rewrite /ro_shot. iFrame "Ho". by iPureIntro. }
    iModIntro. iExists pn. rewrite /wcur /rcur /side_L /side_R /eof_shot.
    iFrame "Hinv Ha Hw2 Ho He Hr2 Hsl Hsr".
  Qed.

  (* ...AND THE SAME, READ AS THE ROUND READS IT: the two symmetric exit
     payloads, both derivable, whose reading is the arm with no code.  So
     the SHORT ROUND is not an unrefuted possibility -- it is a DERIVABLE
     configuration of the protocol, and no strengthening of [pipe_body]
     can exclude it while the read side keeps its landed premises. *)
  Lemma pipe_short_round_payloads (L : list (bv 8)) (c : nat) :
    (0 < c)%nat -> (c <= length L)%nat ->
    ⊢ |={⊤}=> ∃ (γp : pipe_names) (pn : pnames),
        pipe_inv pn γp L
        ∗ pipe_Qc pn (pipe_payL pn L) (pipe_payR pn)
        ∗ pipe_Qc pn (pipe_payL pn L) (pipe_payR pn).
  Proof using .
    intros Hc0 HcL.
    iMod (pipe_queue_alloc) as (γq) "[Ha Hf]".
    set (γp := MkPipeNames 1%positive 1%positive 1%positive 1%positive γq).
    iMod (pipe_short_round_realisable γp L c Hc0 HcL with "Ha Hf")
      as (pn) "(#Hinv & _ & Hw & #Hro & #Heof & _ & HsL & HsR)".
    iModIntro. iExists γp, pn. iFrame "Hinv".
    iSplitL "HsL Hw".
    - rewrite /pipe_Qc. iLeft. iFrame "HsL". rewrite /pipe_payL.
      iRight. iRight. iExists c. iFrame "Hw Hro".
    - rewrite /pipe_Qc. iRight. iFrame "HsR". rewrite /pipe_payR.
      iExists (take c L). iExact "Heof".
  Qed.

  (* THE REFUTATION, at the statement: if the law were a consequence of the
     invariant, the logic would prove [False].  (The conclusion is not
     [False] in Rocq -- it cannot be, it is a claim about the logic -- but
     [|={⊤}=> ⌜False⌝] with no premise is absurd in any model of it, which
     is the same standard [PipeReg.pipe_reg_not_free] is stated at.) *)
  Lemma pipe_no_short_not_of_inv (L : list (bv 8)) (c : nat) :
    (0 < c)%nat -> (c < length L)%nat ->
    (forall (pn : pnames) (γp : pipe_names),
       pipe_inv pn γp L -∗ pipe_no_short pn L) ->
    ⊢@{iPropI Σ} |={⊤}=> ⌜False⌝.
  Proof using .
    intros Hc0 HcL Hlaw.
    iMod (pipe_queue_alloc) as (γq) "[Ha Hf]".
    set (γp := MkPipeNames 1%positive 1%positive 1%positive 1%positive γq).
    iMod (pipe_short_round_realisable γp L c Hc0 ltac:(lia) with "Ha Hf")
      as (pn) "(#Hinv & _ & _ & #Hro & #Heof & _ & _ & _)".
    iDestruct (Hlaw pn γp with "Hinv") as "#Hno".
    iMod ("Hno" $! c with "[%] Hro Heof") as %[].
    split; [ exact Hc0 | exact HcL ].
  Qed.

End PipeProto.
