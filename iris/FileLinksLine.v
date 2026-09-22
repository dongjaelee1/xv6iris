(* ===================================================================== *)
(*  FileLinksLine.v -- THE FILE APPLICATION'S CREDENTIAL FAMILIES.        *)
(*                                                                       *)
(*  Lane LINK-GEN-2.  [LinkRec.LinkRec]'s fields at the FILE claim:       *)
(*  [EchoLinks.v]'s and [EchoLinksLine.v]'s pure shapes and credential    *)
(*  families, restated at [FileOutPure]'s model -- [pro_pin_f],           *)
(*  [proc_before_f], [proc_stream_f], [pro_idx_f] and [FileDisc.          *)
(*  fstate_upto] -- and proved through [FileLinks.file_links].               *)
(*                                                                       *)
(*  WHAT IS SHARED AND NOT RESTATED: the PROLOGUE.  [pro_of], [pro_from], *)
(*  [pro_done], [pro_fail], [pro_rounds], [pro_alts], /init's banner and  *)
(*  the shell's prompt are [EchoDisc]'s and the file application runs the *)
(*  same /init, so [EchoLinks.pro_of_open_snoc_eq], [wr_prompt_head],     *)
(*  [wr_prompt_tail], [wr_prompt_len], [wr_pro_alts_0], [wr_ban_head],    *)
(*  [bodies_of_app_nonl], [nlines_app_nonl], [rest_of_app_nonl] and       *)
(*  [pro_rounds_one] are IMPORTED, not twinned.                           *)
(*                                                                       *)
(*  WHAT IS NEW, and it is the whole of what the file adds: the BLOCK a   *)
(*  line owes is [FileDisc.cont] at the state [fstate_upto] says the file is *)
(*  in, where echo's was [EchoDisc.line_alts_of] of the words that were   *)
(*  typed.  A program above the links names NO state, so the record's     *)
(*  [lk_ab] is the block AT THE ALTERNATIVES WHOSE OUTPUT DOES NOT DEPEND *)
(*  ON ONE -- every [ralt] but [RCRan] ([fstate_free]) -- and is [[]]        *)
(*  elsewhere, which makes the block-byte step premise-free exactly as    *)
(*  echo's is ([EchoDisc.line_alts_lt]).  cat's own round, the one        *)
(*  [RCRan] round, is stated at an EXPLICIT stage ([UCatOut] section 1)   *)
(*  and does not go through this family.                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import LineModel.       (* the line model, and its writer-side reading *)
Require Import LineModelLinks.
Require Import LineModelInst.   (* the stream equations at [file_lm] *)
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import EchoLinks.        (* the SHARED prologue/prompt lemmas *)
Require Import EchoLinksLine.    (* ...and the SHARED alternative lengths *)
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.


(* ===================================================================== *)
(*  S0  THE LINE, ITS ALTERNATIVES' OUTPUT, AND STATE-FREEDOM             *)
(* ===================================================================== *)

(* the line the last COMPLETE body of [I] parses to *)
Definition fline (I : list (bv 8)) : uline :=
  uline_of (bodies_of I !!! (nlines I - 1)%nat).

(* ...and when that line is a redirect, its words are among the input's
   redirect lines -- which is what turns the read's witness
   ([flw]: every [echof_lines_in I] word list is in the claim's ledger)
   into the [ws ∈ ls] the open and the write credential ask for. *)
Lemma fline_echof_in (I : list (bv 8)) (ws : list (list (bv 8))) :
  (0 < nlines I)%nat -> fline I = LEchoF ws -> ws ∈ echof_lines_in I.
Proof using.
  intros Hp Hf. rewrite /echof_lines_in. apply elem_of_list_omap.
  exists (LEchoF ws). split; [ | reflexivity ].
  rewrite /lines_of -Hf /fline. apply elem_of_list_fmap.
  eexists. split; [ reflexivity | ].
  apply elem_of_list_lookup. exists (nlines I - 1)%nat.
  apply list_lookup_lookup_total_lt. rewrite /nlines in Hp |- *. lia.
Qed.

(* the alternatives whose console output is a function of the LINE alone.
   [RCRan] is the only one that reads the file's state, and it is cat's
   own round. *)
Definition fstate_free (a : ralt) : bool :=
  match a with RCRan => false | _ => true end.

Lemma cont_state_free (s s' : fstate) (l : uline) (a : ralt) :
  fstate_free a = true -> cont s l a = cont s' l a.
Proof using. destruct a; cbn [fstate_free]; try discriminate; reflexivity. Qed.

(* THE RECORD'S [lk_ab]: the block alternative [a] owes at input [I],
   GUARDED so that a byte lookup alone says the alternative is admissible
   and state-free -- which is what makes the block-byte step premise-free. *)
Definition fab (I : list (bv 8)) (a : nat) : list (bv 8) :=
  if decide (ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true)
  then cont None (fline I) (ralt_dec a) else [].

(* THE RECORD'S [lk_apr]: the alternative ends with the shell's prompt,
   i.e. it is admissible, state-free and does NOT reopen the prologue. *)
Definition fapr (I : list (bv 8)) (a : nat) : Prop :=
  ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true
  /\ ralt_panic (ralt_dec a) = false.




(* ---- THE SHELL'S OWN TWO ALTERNATIVES ARE PER-LINE.  This is lane
        LINK-GEN's [lk_pan]/[lk_exf] found to be the WRONG TYPE: at the
        echo application there is one line shape and the fork panic is
        the constant 3, but [FileDisc.ralt_ok] admits [RFFork] only at an
        [LEchoF] line, [RCFork] only at an [LCat] one and [REcho 3] only
        at an [LEcho] one.  The panic's BYTES are the same at all three
        ([alt_panic]); the exec-failed child's are NOT ([alt_execcat] at
        a cat line), because sh prints "exec %s failed" with the command
        name. ---- *)
Definition fpan_of (l : uline) : nat :=
  match l with
  | LEcho _ => 3%nat
  | LEchoF _ => ralt_enc RFFork
  | LCat => ralt_enc RCFork
  (* the DEAD arm: [FileDisc.ralt_ok] gives [LPipe] exactly [LCat]'s five,
     so all four of this file's per-line choices are [LCat]'s verbatim *)
  | LPipe _ => ralt_enc RCFork
  end.

Definition fexf_of (l : uline) : nat :=
  match l with
  | LEcho _ => 1%nat
  | LEchoF _ => ralt_enc RFExec
  | LCat => ralt_enc RCExec
  | LPipe _ => ralt_enc RCExec
  end.

(* ...and the bytes the exec-failed child prints, per line *)
Definition fexfb (l : uline) : list (bv 8) :=
  match l with
  | LEcho _ => alt_execfail
  | LEchoF _ => alt_execfail
  | LCat => alt_execcat
  | LPipe _ => alt_execcat
  end.

Definition fnoc : nat := ralt_enc RFSilent.


(* ---- the block's LAST TWO BYTES are the shell's prompt, at every
        admissible, state-free, non-panic alternative.  [FileDisc.
        cont_shape] says so under [uline_ok], which a WRITER does not
        hold; this reads it off the twelve cases instead, four of which
        are literals. ---- *)



(* ===================================================================== *)
(*  THE STATE-AWARE BLOCK (PROGRAM-STREAM stretch 11, defect 3).           *)
(*                                                                       *)
(*  [fab] gives an alternative's bytes from the INPUT alone, and is [[]]  *)
(*  at the one alternative whose bytes are a function of the FILE --      *)
(*  [RCRan], "cat printed the contents".  So a block at [RCRan] had no    *)
(*  bytes here, [fapr] excluded it, and the line credential could not     *)
(*  hold a round in which cat printed a non-empty file.                   *)
(*                                                                       *)
(*  The model underneath was never the problem: [pending_at_f] speaks     *)
(*  [cont] at the round's own state, [fstate_upto cs s0 ...], and [fab]   *)
(*  reaches it only through [cont_state_free].  [fabs] is that reading    *)
(*  with the state kept: the era's boot state [s0] and the choice list    *)
(*  [cs] filed so far determine it.  [fab] is its instance at a           *)
(*  state-free alternative ([fabs_fab]), and the block lemmas below are   *)
(*  proved at [fabs]; their [fab] statements are corollaries.             *)
(* ===================================================================== *)
Definition fabs (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat)
  : list (bv 8) :=
  cont (fstate_upto cs s0 (bodies_of I) (nlines I - 1)%nat) (fline I)
    (ralt_dec a).

(* [fapr] without state-freedom: admissible, and not a panic *)
Definition faprs (I : list (bv 8)) (a : nat) : Prop :=
  ralt_ok (fline I) (ralt_dec a) /\ ralt_panic (ralt_dec a) = false.



(* every non-panic admissible alternative's block ENDS WITH THE PROMPT, at
   every state: the file's contents come BEFORE it *)





(* ---- the two PER-LINE alternatives, and the "nobody chose" one ---- *)
Lemma fpan_of_ok (l : uline) : ralt_ok l (ralt_dec (fpan_of l)).
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fpan_of].
  - rewrite (ralt_dec_lt4 3%nat ltac:(lia)) /ralt_ok. lia.
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.

Lemma fpan_of_free (l : uline) : fstate_free (ralt_dec (fpan_of l)) = true.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fpan_of].
  - by rewrite (ralt_dec_lt4 3%nat ltac:(lia)).
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.

Lemma fpan_of_panic (l : uline) : ralt_panic (ralt_dec (fpan_of l)) = true.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fpan_of].
  - rewrite (ralt_dec_lt4 3%nat ltac:(lia)). by vm_compute.
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.

Lemma cont_fpan (s : fstate) (l : uline) :
  cont s l (ralt_dec (fpan_of l)) = alt_panic.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fpan_of].
  - rewrite (ralt_dec_lt4 3%nat ltac:(lia)). cbn [cont uline_ws].
    exact (line_alts_of_3 ws).
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.


Lemma fexf_of_ok (l : uline) : ralt_ok l (ralt_dec (fexf_of l)).
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fexf_of].
  - rewrite (ralt_dec_lt4 1%nat ltac:(lia)) /ralt_ok. lia.
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
Qed.

Lemma fexf_of_free (l : uline) : fstate_free (ralt_dec (fexf_of l)) = true.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fexf_of].
  - by rewrite (ralt_dec_lt4 1%nat ltac:(lia)).
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
Qed.

Lemma fexf_of_nopanic (l : uline) : ralt_panic (ralt_dec (fexf_of l)) = false.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fexf_of].
  - rewrite (ralt_dec_lt4 1%nat ltac:(lia)). by vm_compute.
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
Qed.

Lemma cont_fexf (s : fstate) (l : uline) :
  cont s l (ralt_dec (fexf_of l)) = fexfb l.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fexf_of fexfb].
  - rewrite (ralt_dec_lt4 1%nat ltac:(lia)). cbn [cont uline_ws].
    exact (line_alts_of_1 ws).
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
Qed.



(* the alternative a round takes when NOBODY wrote: the shell's own
   prompt IS the block's first byte, and which code that is depends on the
   line ([REcho 2] at an echo line, [RFSilent] at a redirect one,
   [RCSilent] at a cat one) -- all three print [u_prompt]. *)
Definition fnoc_of (l : uline) : nat :=
  match l with
  | LEcho _ => 2%nat
  | LEchoF _ => ralt_enc RFSilent
  | LCat => ralt_enc RCSilent
  | LPipe _ => ralt_enc RCSilent
  end.

Lemma fnoc_of_ok (l : uline) : ralt_ok l (ralt_dec (fnoc_of l)).
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fnoc_of].
  - rewrite (ralt_dec_lt4 2%nat ltac:(lia)) /ralt_ok. lia.
  - by rewrite (ralt_dec_enc RFSilent).
  - by rewrite (ralt_dec_enc RCSilent).
  - by rewrite (ralt_dec_enc RCSilent).
Qed.

Lemma fnoc_of_free (l : uline) : fstate_free (ralt_dec (fnoc_of l)) = true.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fnoc_of].
  - by rewrite (ralt_dec_lt4 2%nat ltac:(lia)).
  - by rewrite (ralt_dec_enc RFSilent).
  - by rewrite (ralt_dec_enc RCSilent).
  - by rewrite (ralt_dec_enc RCSilent).
Qed.

Lemma fnoc_of_nopanic (l : uline) : ralt_panic (ralt_dec (fnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fnoc_of].
  - rewrite (ralt_dec_lt4 2%nat ltac:(lia)). by vm_compute.
  - by rewrite (ralt_dec_enc RFSilent).
  - by rewrite (ralt_dec_enc RCSilent).
  - by rewrite (ralt_dec_enc RCSilent).
Qed.

Lemma cont_fnoc (s : fstate) (l : uline) :
  cont s l (ralt_dec (fnoc_of l)) = u_prompt.
Proof using.
  destruct l as [ws | ws | | ws]; cbn [fnoc_of].
  - rewrite (ralt_dec_lt4 2%nat ltac:(lia)). cbn [cont uline_ws].
    exact (EchoLinks.wr_line_alts_2 ws).
  - by rewrite (ralt_dec_enc RFSilent).
  - by rewrite (ralt_dec_enc RCSilent).
  - by rewrite (ralt_dec_enc RCSilent).
Qed.






(* ---- THE MODEL'S HOOKS ([LineModelLinks.lm_hooks] at the file model):
        the per-line alternatives the shell's own code names, state-
        freedom, and what a WRITER knows of a continuation without the
        discipline's premises.  Everything section 0 said of [fab] /
        [fabs] / [fapr] is then [LineModelLinks]'s lemma read back through
        the equations below ([fab] IS [lm_ab] up to the decision term). ---- *)
Lemma cont_prompt (s : fstate) (l : uline) (a : ralt) :
  ralt_ok l a -> ralt_panic a = false ->
  exists u : list (bv 8), cont s l a = u ++ u_prompt.
Proof using.
  intros Hok Hp. revert s.
  destruct a as [k | sel | | | | | | | | | |]; intros st.
  { (* [REcho]: on its own, so no [vm_compute] meets the line *)
    rewrite /ralt_ok in Hok. destruct l as [ws | ws | | ws];
      cbn in Hok; try done.
    cbn [ralt_panic] in Hp. apply bool_decide_eq_false in Hp.
    cbn [cont uline_ws].
    pose proof (EchoLinksLine.line_alts_len_ge2 ws k ltac:(lia)) as Hl.
    pose proof (EchoLinksLine.line_alts_dollar ws k ltac:(lia)) as Hd.
    pose proof (EchoLinksLine.line_alts_space ws k ltac:(lia)) as Hsp.
    set (bl := line_alts_of ws !!! k) in *.
    exists (take (length bl - 2) bl).
    rewrite -{1}(take_drop (length bl - 2) bl). f_equal.
    apply list_eq. intros i. rewrite lookup_drop.
    destruct i as [| [| i]].
    - rewrite Nat.add_0_r Hd. by vm_compute.
    - replace (length bl - 2 + 1)%nat with (length bl - 1)%nat by lia.
      rewrite Hsp. by vm_compute.
    - rewrite lookup_ge_None_2; [ | lia ].
      symmetry. apply lookup_ge_None_2. vm_compute. lia. }
  all: try (cbn [ralt_panic] in Hp; by discriminate Hp).
  all: cbn [cont].
  (* [RCRan]: the contents, then the prompt -- or the diagnostic *)
  all: try (destruct st as [bs |]; [ by exists bs | ]).
  (* a CONSTANT block: its own bytes but the last two *)
  all: match goal with
       | |- exists pre : list (bv 8), ?c = pre ++ u_prompt =>
           exists (take (length c - 2) c); by vm_compute
       end.
Qed.

Lemma cont_nonnil_dec (s : fstate) (l : uline) (a : ralt) :
  ralt_ok l a \/ a = ralt_dec 0%nat -> cont s l a <> [].
Proof using.
  rewrite (ralt_dec_lt4 0%nat ltac:(lia)). exact (cont_nonnil s l a).
Qed.

Definition file_hooks : lm_hooks file_lm :=
  MkLMH file_lm fstate_free None fpan_of fexf_of fexfb fnoc_of ralt_ok_dec
    cont_state_free (fun _ _ => eq_refl)
    fpan_of_ok fpan_of_free fpan_of_panic
    fexf_of_ok fexf_of_free fexf_of_nopanic cont_fexf
    fnoc_of_ok fnoc_of_free fnoc_of_nopanic cont_fnoc
    (fun s l a Hok Hp _ => cont_prompt s l a Hok Hp)
    cont_nonnil_dec.

Lemma fline_lm (I : list (bv 8)) : fline I = lm_line_at file_lm I.
Proof using. reflexivity. Qed.

Lemma fab_lm (I : list (bv 8)) (a : nat) : fab I a = lm_ab file_lm file_hooks I a.
Proof using.
  rewrite /fab /lm_ab. case_decide as H1; case_decide as H2;
    [reflexivity | by destruct (H2 H1) | by destruct (H1 H2) | reflexivity].
Qed.

Lemma fapr_lm (I : list (bv 8)) (a : nat) : fapr I a <-> lm_apr file_lm file_hooks I a.
Proof using. reflexivity. Qed.

Lemma fabs_lm (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  fabs s0 cs I a = lm_abs file_lm s0 cs I a.
Proof using. rewrite /fabs /lm_abs fstate_upto_lm. reflexivity. Qed.

Lemma faprs_lm (I : list (bv 8)) (a : nat) : faprs I a <-> lm_aprs file_lm I a.
Proof using.
  split.
  - intros [H1 H2]. exact (conj H1 (conj H2 eq_refl)).
  - intros (H1 & H2 & _). exact (conj H1 H2).
Qed.

(* the stream, at a boot state that may be unfiled *)
Lemma pending_at_f_lm_o ps cs f0 I :
  pending_at_f ps cs f0 I = lm_pending_at file_lm ps cs (f0_st f0) I.
Proof using. reflexivity. Qed.

Lemma proc_before_from_f_lm_o ps cs f0 pre I :
  proc_before_from_f ps cs f0 pre I
  = lm_proc_before_from file_lm ps cs (f0_st f0) pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre; [reflexivity |].
  cbn. by rewrite IH.
Qed.

Lemma proc_before_f_lm_o ps cs f0 I :
  proc_before_f ps cs f0 I = lm_proc_before file_lm ps cs (f0_st f0) I.
Proof using. apply proc_before_from_f_lm_o. Qed.

Lemma proc_stream_f_lm_o ps cs f0 I :
  proc_stream_f ps cs f0 I = lm_proc_stream file_lm ps cs (f0_st f0) I.
Proof using. rewrite /proc_stream_f /lm_proc_stream. by rewrite proc_before_f_lm_o. Qed.

Lemma rd_stage_f_lm ps0 cs0 I : rd_stage_f ps0 cs0 I <-> lm_rd_stage file_lm ps0 cs0 I.
Proof using.
  rewrite /rd_stage_f /lm_rd_stage.
  split; intros (H1 & H2 & H3 & H4);
    (split_and!; [exact H1 | exact H2 | by apply pro_pin_f_lm | exact H4]).
Qed.

(* ---- what section 0 said, as corollaries ---- *)
Lemma fab_ok (I : list (bv 8)) (a i : nat) (b : bv 8) :
  fab I a !! i = Some b ->
  ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true.
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_ok file_lm file_hooks).
Qed.

Lemma fab_is (I : list (bv 8)) (a : nat) :
  ralt_ok (fline I) (ralt_dec a) -> fstate_free (ralt_dec a) = true ->
  fab I a = cont None (fline I) (ralt_dec a).
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_is file_lm file_hooks).
Qed.

Lemma fab_at (I : list (bv 8)) (a : nat) (s : fstate) :
  ralt_ok (fline I) (ralt_dec a) -> fstate_free (ralt_dec a) = true ->
  fab I a = cont s (fline I) (ralt_dec a).
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_at file_lm file_hooks).
Qed.

Lemma fab_len_ge2 (I : list (bv 8)) (a : nat) :
  fapr I a -> (2 <= length (fab I a))%nat.
Proof using.
  rewrite fab_lm. intros Hpr.
  exact (lm_ab_len_ge2 file_lm file_hooks I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fab_dollar (I : list (bv 8)) (a : nat) :
  fapr I a ->
  fab I a !! (length (fab I a) - 2)%nat = Some (u_prompt !!! 0%nat).
Proof using.
  rewrite fab_lm. intros Hpr.
  exact (lm_ab_dollar file_lm file_hooks I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fab_space (I : list (bv 8)) (a : nat) :
  fapr I a ->
  fab I a !! (length (fab I a) - 1)%nat = Some (u_prompt !!! 1%nat).
Proof using.
  rewrite fab_lm. intros Hpr.
  exact (lm_ab_space file_lm file_hooks I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fapr_faprs (I : list (bv 8)) (a : nat) : fapr I a -> faprs I a.
Proof using.
  intros (H1 & _ & H3). exact (conj H1 H3).
Qed.

Lemma fabs_fab (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  fapr I a -> fabs s0 cs I a = fab I a.
Proof using.
  rewrite fabs_lm fab_lm. intros Hpr.
  exact (lm_abs_ab file_lm file_hooks s0 cs I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fabs_prompt (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a -> exists pre : list (bv 8), fabs s0 cs I a = pre ++ u_prompt.
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_prompt file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fabs_len_ge2 (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a -> (2 <= length (fabs s0 cs I a))%nat.
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_len_ge2 file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fabs_dollar (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a ->
  fabs s0 cs I a !! (length (fabs s0 cs I a) - 2)%nat
  = Some (u_prompt !!! 0%nat).
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_dollar file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fabs_space (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a ->
  fabs s0 cs I a !! (length (fabs s0 cs I a) - 1)%nat
  = Some (u_prompt !!! 1%nat).
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_space file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fab_pan (I : list (bv 8)) : fab I (fpan_of (fline I)) = alt_panic.
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_pan file_lm file_lm_laws file_hooks).
Qed.

Lemma fab_exf (I : list (bv 8)) :
  fab I (fexf_of (fline I)) = fexfb (fline I).
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_exf file_lm file_hooks).
Qed.

Lemma fapr_exf (I : list (bv 8)) : fapr I (fexf_of (fline I)).
Proof using.
  apply fapr_lm. apply (lm_apr_exf file_lm file_hooks).
Qed.

Lemma fab_noc (I : list (bv 8)) : fab I (fnoc_of (fline I)) = u_prompt.
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_noc file_lm file_hooks).
Qed.

Lemma fapr_noc (I : list (bv 8)) : fapr I (fnoc_of (fline I)).
Proof using.
  apply fapr_lm. apply (lm_apr_noc file_lm file_hooks).
Qed.


(* ===================================================================== *)
(*  S1  THE PURE SHAPES, AT THE FILE MODEL                                *)
(*                                                                       *)
(*  [EchoLinks]'s [wr_pro] / [wr_blk] / [wr_open] / [wr_sp] / [wr_owed] / *)
(*  [wr_ban] and [EchoLinksLine]'s [wr_tail] / [wr_blk_t] / [wr_sp_t] /   *)
(*  [wr_open_t] / [blkcs], with [pro_pin_f], [proc_before_f],             *)
(*  [proc_stream_f], [pro_idx_f] and the era's BOOT STATE [s0] threaded.  *)
(*  Where echo tested [cs !!! (nlines I - 1) = 3] the file tests          *)
(*  [ralt_panic (ralt_at cs (nlines I - 1))], so the two new line shapes' *)
(*  fork alternatives open a round too.                                   *)
(* ===================================================================== *)
Definition wr_pro_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true)
  /\ ~ pro_done (pro_from (pro_idx_f cs (nlines I)) ps)
  /\ P = length (proc_stream_f ps cs (Some s0) I).

Definition wr_blk_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_f ps cs (Some s0) I).

Definition wr_open_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (pro_idx_f cs (nlines I) < pro_rounds ps)%nat
  /\ P = length (proc_stream_f ps cs (Some s0) I).

Definition wr_owed_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  wr_pro_f ps cs s0 I P \/ wr_blk_f ps cs s0 I P.

Definition wr_sp_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  wr_open_f ps cs s0 I (S P)
  /\ proc_stream_f ps cs (Some s0) I !! P = Some (u_prompt !!! 1%nat).

Definition wr_pre_f (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then [] else alt_panic.

Definition wr_ban_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_f cs (nlines I)) ps = pro_fail j
        /\ P = (length (proc_before_f ps cs (Some s0) I)
                + length (wr_pre_f I) + pro_round * j)%nat).

Definition wr_tail_f (ps cs : list nat) : Prop :=
  pro_from (S (pro_idx_f cs (length cs))) ps = [].

Definition wr_blk_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop := wr_blk_f ps cs s0 I P /\ wr_tail_f ps cs.

Definition wr_sp_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop := wr_sp_f ps cs s0 I P /\ wr_tail_f ps cs.

Definition wr_open_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop := wr_open_f ps cs s0 I P /\ wr_tail_f ps cs.

Definition blkcs_f (cs : list nat) (a i : nat) : list nat :=
  match i with O => cs | S _ => cs ++ [a] end.

(* ---- the writer's stages are [LineModel]'s, by the stream equations ---- *)
Lemma wr_pro_f_lm ps cs s0 I P : wr_pro_f ps cs s0 I P = lm_wr_pro file_lm ps cs s0 I P.
Proof using. rewrite /wr_pro_f /lm_wr_pro ?proc_stream_f_lm ?proc_before_f_lm pro_idx_f_lm. reflexivity. Qed.
Lemma wr_blk_f_lm ps cs s0 I P : wr_blk_f ps cs s0 I P = lm_wr_blk file_lm ps cs s0 I P.
Proof using. rewrite /wr_blk_f /lm_wr_blk ?proc_stream_f_lm ?proc_before_f_lm. reflexivity. Qed.
Lemma wr_open_f_lm ps cs s0 I P : wr_open_f ps cs s0 I P = lm_wr_open file_lm ps cs s0 I P.
Proof using. rewrite /wr_open_f /lm_wr_open ?proc_stream_f_lm ?proc_before_f_lm pro_idx_f_lm. reflexivity. Qed.
Lemma wr_owed_f_lm ps cs s0 I P : wr_owed_f ps cs s0 I P = lm_wr_owed file_lm ps cs s0 I P.
Proof using. rewrite /wr_owed_f /lm_wr_owed wr_pro_f_lm wr_blk_f_lm. reflexivity. Qed.
Lemma wr_sp_f_lm ps cs s0 I P : wr_sp_f ps cs s0 I P = lm_wr_sp file_lm ps cs s0 I P.
Proof using. rewrite /wr_sp_f /lm_wr_sp wr_open_f_lm proc_stream_f_lm. reflexivity. Qed.
Lemma wr_ban_f_lm ps cs s0 I P : wr_ban_f ps cs s0 I P = lm_wr_ban file_lm ps cs s0 I P.
Proof using. rewrite /wr_ban_f /lm_wr_ban ?proc_stream_f_lm ?proc_before_f_lm pro_idx_f_lm. reflexivity. Qed.
Lemma wr_tail_f_lm ps cs : wr_tail_f ps cs = lm_wr_tail file_lm ps cs.
Proof using. rewrite /wr_tail_f /lm_wr_tail pro_idx_f_lm. reflexivity. Qed.
Lemma wr_blk_t_f_lm ps cs s0 I P : wr_blk_t_f ps cs s0 I P = lm_wr_blk_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_blk_t_f /lm_wr_blk_t wr_blk_f_lm wr_tail_f_lm. reflexivity. Qed.
Lemma wr_sp_t_f_lm ps cs s0 I P : wr_sp_t_f ps cs s0 I P = lm_wr_sp_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_sp_t_f /lm_wr_sp_t wr_sp_f_lm wr_tail_f_lm. reflexivity. Qed.
Lemma wr_open_t_f_lm ps cs s0 I P : wr_open_t_f ps cs s0 I P = lm_wr_open_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_open_t_f /lm_wr_open_t wr_open_f_lm wr_tail_f_lm. reflexivity. Qed.


(* ===================================================================== *)
(*  S2  THE PURE LEMMAS                                                   *)
(* ===================================================================== *)

(* ---- the stage's own readings ---- *)
Lemma pro_pin_f_nil (ps cs : list nat) : pro_pin_f ps cs [].
Proof using.
  apply pro_pin_f_lm. apply (lm_pro_pin_nil file_lm).
Qed.

Lemma pro_pin_f_at (ps cs : list nat) (I : list (bv 8)) (q : nat) :
  pro_pin_f ps cs I -> (q < nstarted I)%nat ->
  (pro_idx_f cs q < pro_rounds ps)%nat.
Proof using.
  intros H Hq. rewrite pro_idx_f_lm.
  exact (lm_pro_pin_at file_lm ps cs I q (proj1 (pro_pin_f_lm _ _ _) H) Hq).
Qed.

Lemma wr_blk_nonnil_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : wr_blk_f ps cs s0 I P -> I <> [].
Proof using.
  rewrite wr_blk_f_lm. apply (lm_wr_blk_nonnil file_lm).
Qed.

Lemma wr_blk_lines_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : wr_blk_f ps cs s0 I P -> nlines I = S (length cs).
Proof using.
  rewrite wr_blk_f_lm. apply (lm_wr_blk_lines file_lm).
Qed.

Lemma wr_blk_started_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : wr_blk_f ps cs s0 I P -> nstarted I = S (length cs).
Proof using.
  rewrite wr_blk_f_lm. apply (lm_wr_blk_started file_lm).
Qed.

(* the stage [UCatOut.cat_stage] names, with the line abstract *)
Lemma wr_blk_t_stage_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_blk_t_f ps cs s0 I P ->
  rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_f ps cs (Some s0) I)
  /\ pro_pin_f ps cs I
  /\ wr_tail_f ps cs.
Proof using.
  rewrite wr_blk_t_f_lm proc_before_f_lm wr_tail_f_lm. intros Hw.
  destruct (lm_wr_blk_t_stage file_lm ps cs s0 I P Hw) as (H1 & H2 & H3 & H4 & H5).
  split_and!; [exact H1 | exact H2 | exact H3 | by apply pro_pin_f_lm | exact H5].
Qed.

(* ---- filing an alternative reads no round below the boundary ---- *)
Lemma wr_blk_pin_snoc_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) : wr_blk_f ps cs s0 I P -> pro_pin_f ps (cs ++ [a]) I.
Proof using.
  rewrite wr_blk_f_lm. intros Hw. apply pro_pin_f_lm.
  exact (lm_wr_blk_pin_snoc file_lm ps cs s0 I P a Hw).
Qed.

(* ...and it moves no byte of what is already out ---- *)
Lemma wr_blk_low_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  proc_before_f ps (cs ++ [a]) (Some s0) I = proc_before_f ps cs (Some s0) I.
Proof using.
  rewrite wr_blk_f_lm !proc_before_f_lm. apply (lm_wr_blk_low file_lm).
Qed.

(* THE BLOCK THE ROUND OWES once alternative [a] is filed, at a NON-PANIC
   state-free alternative: exactly [fab]. *)
Lemma wr_blk_pending_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  ralt_panic (ralt_dec a) = false ->
  pending_at_f ps (cs ++ [a]) (Some s0) I = fabs s0 cs I a.
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm fabs_lm. apply (lm_wr_blk_pending_s file_lm).
Qed.

Lemma wr_blk_pending_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  fapr I a ->
  pending_at_f ps (cs ++ [a]) (Some s0) I = fab I a.
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_pending file_lm file_hooks ps cs s0 I P a Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR *)
Lemma wr_blk_byte_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a j : nat) (b : bv 8) :
  wr_blk_f ps cs s0 I P -> ralt_panic (ralt_dec a) = false ->
  fabs s0 cs I a !! j = Some b ->
  proc_stream_f ps (cs ++ [a]) (Some s0) I !! (P + j)%nat = Some b.
Proof using.
  rewrite wr_blk_f_lm proc_stream_f_lm fabs_lm. apply (lm_wr_blk_byte_s file_lm).
Qed.

Lemma wr_blk_byte_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a j : nat) (b : bv 8) :
  wr_blk_f ps cs s0 I P -> fapr I a ->
  fab I a !! j = Some b ->
  proc_stream_f ps (cs ++ [a]) (Some s0) I !! (P + j)%nat = Some b.
Proof using.
  rewrite wr_blk_f_lm proc_stream_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_byte file_lm file_hooks ps cs s0 I P a j b Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

(* ---- the round index does not move at a non-panic alternative ---- *)
Lemma fd_snoc_lookup_total (cs : list nat) (a : nat) :
  (cs ++ [a]) !!! length cs = a.
Proof using.
  apply ll_snoc_lookup_total.
Qed.

Lemma pro_idx_f_snoc_ne (cs : list nat) (a : nat) :
  ralt_panic (ralt_dec a) = false ->
  pro_idx_f (cs ++ [a]) (S (length cs)) = pro_idx_f cs (length cs).
Proof using.
  rewrite !pro_idx_f_lm. apply (lm_pro_idx_snoc_ne file_lm).
Qed.

Lemma pro_idx_f_snoc_pan (cs : list nat) (a : nat) :
  ralt_panic (ralt_dec a) = true ->
  pro_idx_f (cs ++ [a]) (S (length cs)) = S (pro_idx_f cs (length cs)).
Proof using.
  rewrite !pro_idx_f_lm. apply (lm_pro_idx_snoc_pan file_lm).
Qed.

(* the block's bytes are a PREFIX of what the round then owes -- an
   equality at a non-panic alternative, a prefix at the panic one (whose
   block runs on into the next round's prologue).  That is all a BYTE
   lookup needs, so [wr_blk_byte_f] does not ask for [fapr]. *)
Lemma wr_blk_pending_pre_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  ralt_ok (fline I) (ralt_dec a) -> fstate_free (ralt_dec a) = true ->
  fab I a `prefix_of` pending_at_f ps (cs ++ [a]) (Some s0) I.
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm fab_lm fline_lm. apply (lm_wr_blk_pending_pre file_lm file_hooks).
Qed.

Lemma wr_tail_snoc_f (ps cs : list nat) (a : nat) :
  ralt_panic (ralt_dec a) = false -> wr_tail_f ps cs -> wr_tail_f ps (cs ++ [a]).
Proof using.
  rewrite !wr_tail_f_lm. apply (lm_wr_tail_snoc file_lm).
Qed.

(* ---- the prologue grows by exactly its alternative ---- *)
Lemma pending_at_f_round_snoc (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (a : nat) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true) ->
  ~ pro_done (pro_from (pro_idx_f cs (nlines I)) ps) ->
  (pro_idx_f cs (nlines I) <= pro_rounds ps)%nat ->
  pending_at_f (ps ++ [a]) cs (Some s0) I
  = pending_at_f ps cs (Some s0) I ++ pro_alts !!! a.
Proof using.
  rewrite !pending_at_f_lm !pro_idx_f_lm.
  apply (lm_pending_at_round_snoc file_lm file_lm_laws).
Qed.


(* ===================================================================== *)
(*  S3  THE ROUND'S BANNER, STILL OWED                                    *)
(* ===================================================================== *)
Lemma wr_ban_pro_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_ban_f ps cs s0 I P -> wr_pro_f ps cs s0 I P.
Proof using.
  rewrite wr_ban_f_lm wr_pro_f_lm. apply (lm_wr_ban_pro file_lm file_lm_laws).
Qed.

Lemma wr_ban_low_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_ban_f ps cs s0 I P ->
  proc_before_f (ps ++ [3%nat]) cs (Some s0) I = proc_before_f ps cs (Some s0) I.
Proof using.
  rewrite wr_ban_f_lm !proc_before_f_lm. apply (lm_wr_ban_low file_lm).
Qed.

Lemma wr_ban_filed_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_ban_f ps cs s0 I P ->
  exists j : nat,
    pro_from (pro_idx_f cs (nlines I)) (ps ++ [3%nat]) = pro_fail j ++ [3%nat]
    /\ P = (length (proc_before_f (ps ++ [3%nat]) cs (Some s0) I)
            + length (wr_pre_f I) + pro_round * j)%nat.
Proof using.
  rewrite wr_ban_f_lm proc_before_f_lm pro_idx_f_lm. intros Hw.
  destruct (lm_wr_ban_filed file_lm ps cs s0 I P Hw) as (j & H1 & H2).
  exists j. exact (conj H1 H2).
Qed.

Lemma wr_ban_byte_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P i : nat) (b : bv 8) :
  wr_ban_f ps cs s0 I P -> u_banner !! i = Some b ->
  proc_stream_f (ps ++ [3%nat]) cs (Some s0) I !! (P + i)%nat = Some b.
Proof using.
  rewrite wr_ban_f_lm proc_stream_f_lm. apply (lm_wr_ban_byte file_lm file_lm_laws).
Qed.

Lemma wr_ban_done_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_ban_f ps cs s0 I P ->
  wr_pro_f (ps ++ [3%nat]) cs s0 I (P + length u_banner)%nat.
Proof using.
  rewrite wr_ban_f_lm wr_pro_f_lm. apply (lm_wr_ban_done file_lm file_lm_laws).
Qed.

(* THE TRANSCRIPT'S HEAD *)
Lemma wr_ban_round0_f (s0 : fstate) : wr_ban_f [] [] s0 [] 0%nat.
Proof using.
  rewrite wr_ban_f_lm. apply (lm_wr_ban_round0 file_lm).
Qed.


(* ===================================================================== *)
(*  S4  THE GAP LAW AND THE LINE'S READ                                   *)
(* ===================================================================== *)
Lemma proc_before_from_gap_f (ps cs : list nat) (f0 : option fstate)
    (pre k : list (bv 8)) :
  (forall J : list (bv 8), J `prefix_of` k -> J <> k ->
     pending_at_f ps cs f0 (pre ++ J) = []) ->
  proc_before_from_f ps cs f0 pre k = [].
Proof using.
  rewrite proc_before_from_f_lm_o. intros Hj.
  apply (lm_proc_before_from_gap file_lm). intros J HJ Hne.
  rewrite -pending_at_f_lm_o. exact (Hj J HJ Hne).
Qed.

Lemma proc_before_line_f (ps cs : list nat) (f0 : option fstate)
    (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l ->
  proc_before_f ps cs f0 (I ++ l ++ [wl_nl]) = proc_stream_f ps cs f0 I.
Proof using.
  rewrite proc_before_f_lm_o proc_stream_f_lm_o. apply (lm_proc_before_line file_lm).
Qed.


(* ===================================================================== *)
(*  S5  THE STEPS, PURE                                                   *)
(* ===================================================================== *)

(* (1) the round's CHOICE BYTE at an open prologue: filing alternative 0
       appends the prompt's two bytes to the round's block *)
Lemma wr_pro_dollar_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_pro_f ps cs s0 I P -> wr_sp_f (ps ++ [0%nat]) cs s0 I (S P).
Proof using.
  rewrite wr_pro_f_lm wr_sp_f_lm. apply (lm_wr_pro_dollar file_lm file_lm_laws).
Qed.

(* (2) the LINE's choice byte at a settled round: the shell's '$' is the
       block's first byte and files the round's "nobody wrote" alternative,
       whichever of the three line shapes it is *)
Lemma wr_blk_dollar_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_blk_f ps cs s0 I P ->
  wr_sp_f ps (cs ++ [fnoc_of (fline I)]) s0 I (S P).
Proof using.
  rewrite wr_blk_f_lm wr_sp_f_lm. apply (lm_wr_blk_dollar file_lm file_hooks).
Qed.

(* (3) the SPACE, and (4) the READ *)
Lemma wr_sp_open_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_sp_f ps cs s0 I P -> wr_open_f ps cs s0 I (S P).
Proof using.
  rewrite wr_sp_f_lm wr_open_f_lm. apply (lm_wr_sp_open file_lm).
Qed.

Lemma wr_open_read_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) (l : list (bv 8)) :
  wr_open_f ps cs s0 I P -> wl_nl ∉ l ->
  wr_blk_f ps cs s0 (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_f_lm wr_blk_f_lm. apply (lm_wr_open_read file_lm).
Qed.


(* ===================================================================== *)
(*  S6  THE TIGHT STEPS ([EchoLinksLine]'s S2 at the file model)          *)
(* ===================================================================== *)
Lemma wr_blk_open_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> ralt_panic (ralt_dec a) = false ->
  wr_open_t_f ps (cs ++ [a]) s0 I (P + length (fabs s0 cs I a))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_open_t_f_lm fabs_lm. apply (lm_wr_blk_open_s file_lm).
Qed.

Lemma wr_blk_open_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> fapr I a ->
  wr_open_t_f ps (cs ++ [a]) s0 I (P + length (fab I a))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_open_t_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_open file_lm file_hooks ps cs s0 I P a Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma wr_blk_sp_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> faprs I a ->
  wr_sp_t_f ps (cs ++ [a]) s0 I (P + (length (fabs s0 cs I a) - 1))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_sp_t_f_lm fabs_lm. intros Hw Hpr.
  exact (lm_wr_blk_sp_s file_lm file_hooks ps cs s0 I P a Hw (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma wr_blk_sp_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> fapr I a ->
  wr_sp_t_f ps (cs ++ [a]) s0 I (P + (length (fab I a) - 1))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_sp_t_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_sp file_lm file_hooks ps cs s0 I P a Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma wr_sp_open_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_sp_t_f ps cs s0 I P -> wr_open_t_f ps cs s0 I (S P).
Proof using.
  rewrite wr_sp_t_f_lm wr_open_t_f_lm. apply (lm_wr_sp_open_t file_lm).
Qed.

Lemma wr_open_read_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) (l : list (bv 8)) :
  wr_open_t_f ps cs s0 I P -> wl_nl ∉ l ->
  wr_blk_t_f ps cs s0 (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_t_f_lm wr_blk_t_f_lm. apply (lm_wr_open_read_t file_lm).
Qed.

Lemma wr_pro_tail_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_pro_f ps cs s0 I P -> wr_tail_f (ps ++ [0%nat]) cs.
Proof using.
  rewrite wr_pro_f_lm wr_tail_f_lm. apply (lm_wr_pro_tail file_lm).
Qed.

Lemma wr_pro_dollar_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_pro_f ps cs s0 I P -> wr_sp_t_f (ps ++ [0%nat]) cs s0 I (S P).
Proof using.
  rewrite wr_pro_f_lm wr_sp_t_f_lm. apply (lm_wr_pro_dollar_t file_lm file_lm_laws).
Qed.

(* the PANIC alternative opens a fresh round at the same input *)
Lemma wr_blk_pending_pan_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_blk_f ps cs s0 I P ->
  pending_at_f ps (cs ++ [fpan_of (fline I)]) (Some s0) I
  = alt_panic ++ pro_of (pro_from (S (pro_idx_f cs (length cs))) ps).
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm !pro_idx_f_lm.
  apply (lm_wr_blk_pending_pan file_lm file_lm_laws file_hooks).
Qed.

Lemma wr_blk_ban_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_blk_t_f ps cs s0 I P ->
  wr_ban_f ps (cs ++ [fpan_of (fline I)]) s0 I (P + length (fab I (fpan_of (fline I))))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_ban_f_lm fab_lm.
  apply (lm_wr_blk_ban file_lm file_lm_laws file_hooks).
Qed.


(* ===================================================================== *)
(*  S7  THE DISCIPLINE LEMMA: an untainted input past a boundary means    *)
(*      the boundary's prompt was written ([EchoLinks.                    *)
(*      wr_owed_read_refute] at the file model).                          *)
(*                                                                       *)
(*  BOTH SIDES READ THE SAME BOOT STATE.  At the echo application the     *)
(*  stream is a function of [ps]/[cs]/[I] alone; here it also reads the   *)
(*  era's [s0], and the two halves agree because the writer's credential  *)
(*  and the reader's residue both carry [f0_lb] at the era's ONE file pin *)
(*  ([FileOut.file_era_pin_agree], then [f0_lb_agree]) -- which is what   *)
(*  [f0w] below packages.                                                 *)
(* ===================================================================== *)
Lemma pending_at_f_nonnil_at (ps cs0 : list nat) (f0 : option fstate)
    (I I0 : list (bv 8)) :
  I `prefix_of` I0 -> alts_pre I0 cs0 -> I <> [] -> rest_of I = [] ->
  pending_at_f ps cs0 f0 I <> [].
Proof using.
  rewrite pending_at_f_lm_o. apply (lm_pending_at_nonnil_at file_lm file_hooks).
Qed.

Lemma wr_owed_read_refute_f (ps cs ps0 cs0 : list nat) (s0 : fstate)
    (I I0 : list (bv 8)) (P : nat) :
  wr_owed_f ps cs s0 I P ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage_f ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
  (length (proc_before_f ps0 cs0 (Some s0) I0) <= P)%nat -> False.
Proof using.
  rewrite wr_owed_f_lm proc_before_f_lm. intros Hw HI Hne Hrs.
  exact (lm_wr_owed_read_refute file_lm file_lm_laws file_hooks ps cs ps0 cs0 s0 I I0 P
           Hw HI Hne (proj1 (rd_stage_f_lm _ _ _) Hrs)).
Qed.


Lemma alt_panic_len5 : length alt_panic = 5%nat.
Proof using.
  exact lb_panic_len.
Qed.

(* the banner's shape, indexed by how many of its bytes are out: the
   FIRST byte files the letter, so from then on the resolution names it *)
Definition wr_banp_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P i : nat) : Prop :=
  match i with
  | O => wr_ban_f ps cs s0 I P
  | S _ => exists ps' : list nat, ps = ps' ++ [3%nat] /\ wr_ban_f ps' cs s0 I P
  end.


(* ===================================================================== *)
(*  S8  THE CREDENTIAL FAMILIES, AS RESOURCES                             *)
(*                                                                       *)
(*  [EchoLinks]'s [ewc_*] and [EchoLinksLine]'s, with the era's BOOT      *)
(*  STATE under the same existential as the three bounds and pinned by    *)
(*  the era's own file pin ([f0w]).  ONE arm is new and it is the whole   *)
(*  of what the file adds above the links: the era's FIRST process byte   *)
(*  has not been written yet, so there is no boot state to pin -- what    *)
(*  stands in its place is the deed's own typed witness, which            *)
(*  [FileLinks.file_write_link_first] consumes ([fhead]).                 *)
(* ===================================================================== *)
Section file_links_line.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FT := (file_taint (fgn_cl g)).

  (* THE ERA'S EXTRA STATE, as a resource.  The index is pinned to the
     CONSOLE era because the reader's residue has to agree with it and the
     record's [lk_rres] field is not indexed by the era. *)
  Definition f0w (k : nat) (s0 : fstate) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ ∃ vf : file_era, file_era_pin g k vf ∗ f0_lb vf s0)%I.

  Global Instance f0w_persistent k s : Persistent (f0w k s).
  Proof using . rewrite /f0w. apply _. Qed.
  Global Instance f0w_timeless k s : Timeless (f0w k s).
  Proof using . rewrite /f0w. apply _. Qed.

  Lemma f0w_agree (k k' : nat) (s s' : fstate) :
    f0w k s -∗ f0w k' s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "[-> H] [-> H']".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_lb_agree with "Hl Hl'").
  Qed.

  (* THE READER'S BOOT WITNESS (RULING F0-BOOT): the boot ledger's entry
     alone, which init mints at boot -- so the reader's residue exists at
     the era's head, where nothing has been filed yet.  A writer's [f0w]
     is this beside the filed token, and the two agree on the state. *)
  Definition f0bw (k : nat) (s0 : fstate) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ ∃ vf : file_era, file_era_pin g k vf ∗ f0_bl vf s0)%I.

  Global Instance f0bw_persistent k s : Persistent (f0bw k s).
  Proof using . rewrite /f0bw. apply _. Qed.
  Global Instance f0bw_timeless k s : Timeless (f0bw k s).
  Proof using . rewrite /f0bw. apply _. Qed.

  Lemma f0bw_agree (k k' : nat) (s s' : fstate) :
    f0bw k s -∗ f0bw k' s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "[-> H] [-> H']".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_bl_agree with "Hl Hl'").
  Qed.

  Lemma f0w_bw (k : nat) (s : fstate) : f0w k s -∗ f0bw k s.
  Proof using .
    iIntros "[-> H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iSplitR; [ by iPureIntro | ]. iExists vf. iFrame "Hp".
    iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma f0w_bw_agree (k k' : nat) (s s' : fstate) :
    f0w k s -∗ f0bw k' s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "H H'". iDestruct (f0w_bw with "H") as "H".
    iApply (f0bw_agree with "H H'").
  Qed.

  (* the writer's cursor at a NAMED stage *)
  Definition fcur (v : era_pins) (ps cs : list nat) (s0 : fstate)
      (I : list (bv 8)) (P k : nat) : iProp Σ :=
    (turn v P ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I ∗ f0w k s0)%I.

  Global Instance fcur_timeless v ps cs s0 I P k :
    Timeless (fcur v ps cs s0 I P k).
  Proof using . rewrite /fcur. apply _. Qed.

  (* THE ERA'S HEAD: nothing written, the boot state not yet filed, and
     the deed's typed witness in its place *)
  (* ...AND THE HEAD'S PRECONDITION: the typed witness of the boot state
     beside its (already minted) boot-ledger entry (RULING F0-BOOT) *)
  Definition f0pre : iProp Σ :=
    (∃ s : fstate, ⌜fstate_ok s⌝ ∗ (f0_typed g s ∨ FT) ∗ f0bw (S gen_id) s)%I.

  Definition fhead (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (⌜I = []⌝ ∗ ⌜k = S gen_id⌝ ∗ turn v 0%nat ∗ ps_lb v [] ∗ cs_lb v []
     ∗ inp_lb v [] ∗ (∃ vf : file_era, file_era_pin g k vf) ∗ f0pre)%I.

  Global Instance f0pre_timeless : Timeless f0pre.
  Proof using . rewrite /f0pre. apply _. Qed.
  Global Instance fhead_timeless k v I : Timeless (fhead k v I).
  Proof using . rewrite /fhead. apply _. Qed.

  (* THE DISPATCH FOR THE ELEVEN FAMILIES BELOW, NOT [apply _].  The tree
     carries 455 [Timeless] instances and most of the definitions under
     them are transparent, so the hint net cannot discriminate and a
     search tries nearly all of them: ~1.3s per GOAL at this altitude,
     which made the instance block 98s of this 111s file.  Descend through
     the CONNECTIVES and name the leaf instance, so no search runs at all.
     The dispatch must be SYNTACTIC: a [first [...]] spelling unifies up
     to delta and peels straight through a name that has its own
     instance. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (fcur _ _ _ _ _ _ _) => apply fcur_timeless
    | |- Timeless (fhead _ _ _) => apply fhead_timeless
    | |- Timeless f0pre => apply f0pre_timeless
    | |- Timeless (f0w _ _) => apply f0w_timeless
    | |- Timeless (f0_typed _ _) => apply f0_typed_timeless
    | |- Timeless (file_taint _) => apply file_taint_timeless
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (file_era_pin _ _ _) => apply file_era_pin_timeless
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; tl_leaf
    | |- Persistent (bi_sep _ _) => apply bi.sep_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_or _ _) => apply bi.or_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- Persistent (inp_lb _ _) => apply inp_lb_persistent
    | |- Persistent (f0w _ _) => apply f0w_persistent
    | |- Persistent (f0_typed _ _) => apply f0_typed_persistent
    | |- Persistent (file_taint _) => apply file_taint_persistent
    | |- Persistent (file_era_pin _ _ _) => apply file_era_pin_persistent
    | |- _ => apply _
    end.

  (* ---- the eleven families ---- *)
  Definition fwc_pro (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_pro_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k)
     ∨ fhead k v I ∨ FT)%I.

  Definition fwc_blk (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_blk_t_f ps cs s0 I P⌝
        ∗ turn v (P + i)%nat ∗ ps_lb v ps ∗ cs_lb v (blkcs_f cs a i)
        ∗ inp_lb v I ∗ f0w k s0)
     ∨ FT)%I.

  Definition fwc_owed (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_owed_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k)
     ∨ fhead k v I ∨ FT)%I.

  Definition fwc_sp (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_sp_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_open (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_open_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_sp_t (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_sp_t_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_open_t (k : nat) (v : era_pins) (I : list (bv 8))
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_open_t_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_ban (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_banp_f ps cs s0 I P i⌝
        ∗ turn v (P + i)%nat ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I
        ∗ f0w k s0)
     ∨ (⌜i = 0%nat⌝ ∗ fhead k v I) ∨ FT)%I.

  (* A BLOCK WRITTEN UP TO ITS PROMPT, AT THE ROUND'S OWN STATE (stretch 11,
     defect 3).  [fwc_blk _ _ _ a (length (fab I a) - 2)] said this at an
     index computed from the INPUT, which cannot name a block whose bytes
     are the file's ([RCRan]).  The index here is computed INSIDE, from the
     choice list the credential itself holds ([fabs s0 cs I a]); the old
     shape is its instance at a state-free alternative
     ([fwc_post_of_blk]). *)
  Definition fwc_post (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_blk_t_f ps cs s0 I P⌝
        ∗ turn v (P + (length (fabs s0 cs I a) - 2))%nat ∗ ps_lb v ps
        ∗ cs_lb v (blkcs_f cs a (length (fabs s0 cs I a) - 2)%nat)
        ∗ inp_lb v I ∗ f0w k s0)
     ∨ FT)%I.

  Definition fwc_line (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (fwc_pro k v I
     ∨ ∃ a : nat, ⌜faprs I a⌝ ∗ fwc_post k v I a)%I.

  Definition fwc_lend (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
        ⌜wr_blk_t_f ps cs s0 I P⌝ ∗ fcur v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_pr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => fwc_owed k v I
    | S O => fwc_sp k v I
    | _ => fwc_open k v I
    end.

  Definition fwc_lpr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => fwc_line k v I
    | S O => fwc_sp_t k v I
    | S (S O) => fwc_open_t k v I
    | _ => fwc_blk k v I 0%nat 0%nat
    end.

  (* THE READER'S RESIDUE ([UShLine.rd_res] at the file model) *)
  Definition fwc_rres (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ (ps0 cs0 : list nat) (s0 : fstate),
       ⌜rd_stage_f ps0 cs0 I⌝
       ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0) I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ f0bw (S gen_id) s0)%I.

  Global Instance fwc_rres_persistent v I : Persistent (fwc_rres v I).
  Proof using . rewrite /fwc_rres. tl_leaf. Qed.
  Global Instance fwc_rres_timeless v I : Timeless (fwc_rres v I).
  Proof using . rewrite /fwc_rres. tl_leaf. Qed.

  (* THE TYPED LINES' WITNESS (the PROGRAM STREAM, stretch 9): every
     [echo ... > f] line of the input the reader has consumed is in a list
     the LEDGER has a lower bound of -- which is what the child that writes
     the line to `f` owes the claim ([FileWrite.file_wq]'s [ws ∈ ls]).  It
     is read off the consumed bytes' TAGS ([FileOut.ftag]) by
     [FileLineWit.echof_lines_of_consumed], and the left arm is the era's
     head, where no lower bound exists to be had. *)
  Definition flw (I : list (bv 8)) : iProp Σ :=
    (⌜echof_lines_in I = []⌝
     ∨ ∃ ls : list (list (list (bv 8))),
         fl_lb (fgn_cl g) ls ∗ ⌜forall w, w ∈ echof_lines_in I -> w ∈ ls⌝)%I.

  Global Instance flw_persistent I : Persistent (flw I).
  Proof using . rewrite /flw. apply _. Qed.
  Global Instance flw_timeless I : Timeless (flw I).
  Proof using . rewrite /flw. apply _. Qed.

  (* ...and THE RECORD'S RESIDUE: the cursor bounds with the witness *)
  Definition fwc_rresw (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (fwc_rres v I ∗ flw I)%I.

  Global Instance fwc_rresw_persistent v I : Persistent (fwc_rresw v I).
  Proof using . rewrite /fwc_rresw. apply _. Qed.
  Global Instance fwc_rresw_timeless v I : Timeless (fwc_rresw v I).
  Proof using . rewrite /fwc_rresw. apply _. Qed.

  Global Instance fwc_pro_timeless k v I : Timeless (fwc_pro k v I).
  Proof using . rewrite /fwc_pro. tl_leaf. Qed.
  Global Instance fwc_blk_timeless k v I a i : Timeless (fwc_blk k v I a i).
  Proof using . rewrite /fwc_blk. tl_leaf. Qed.
  Global Instance fwc_owed_timeless k v I : Timeless (fwc_owed k v I).
  Proof using . rewrite /fwc_owed. tl_leaf. Qed.
  Global Instance fwc_sp_timeless k v I : Timeless (fwc_sp k v I).
  Proof using . rewrite /fwc_sp. tl_leaf. Qed.
  Global Instance fwc_open_timeless k v I : Timeless (fwc_open k v I).
  Proof using . rewrite /fwc_open. tl_leaf. Qed.
  Global Instance fwc_sp_t_timeless k v I : Timeless (fwc_sp_t k v I).
  Proof using . rewrite /fwc_sp_t. tl_leaf. Qed.
  Global Instance fwc_open_t_timeless k v I : Timeless (fwc_open_t k v I).
  Proof using . rewrite /fwc_open_t. tl_leaf. Qed.
  Global Instance fwc_ban_timeless k v I i : Timeless (fwc_ban k v I i).
  Proof using . rewrite /fwc_ban. tl_leaf. Qed.
  Global Instance fwc_post_timeless k v I a : Timeless (fwc_post k v I a).
  Proof using . rewrite /fwc_post. tl_leaf. Qed.
  Global Instance fwc_line_timeless k v I : Timeless (fwc_line k v I).
  Proof using .
    rewrite /fwc_line.
    apply bi.or_timeless; [apply fwc_pro_timeless |].
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply fwc_post_timeless].
  Qed.
  Global Instance fwc_lend_timeless k v I : Timeless (fwc_lend k v I).
  Proof using . rewrite /fwc_lend. tl_leaf. Qed.
  Global Instance fwc_pr_timeless k v I p : Timeless (fwc_pr k v I p).
  Proof using .
    rewrite /fwc_pr. destruct p as [| [| p]];
      [apply fwc_owed_timeless | apply fwc_sp_timeless
      | apply fwc_open_timeless].
  Qed.
  Global Instance fwc_lpr_timeless k v I p : Timeless (fwc_lpr k v I p).
  Proof using .
    rewrite /fwc_lpr. destruct p as [| [| [| p]]];
      [apply fwc_line_timeless | apply fwc_sp_t_timeless
      | apply fwc_open_t_timeless | apply fwc_blk_timeless].
  Qed.

  (* ---- the taint inhabits every shape ---- *)
  Lemma fwc_pro_taint k v I : FT -∗ fwc_pro k v I.
  Proof using . iIntros "H". rewrite /fwc_pro. iRight. by iRight. Qed.
  Lemma fwc_blk_taint k v I a i : FT -∗ fwc_blk k v I a i.
  Proof using . iIntros "H". rewrite /fwc_blk. by iRight. Qed.
  Lemma fwc_owed_taint k v I : FT -∗ fwc_owed k v I.
  Proof using . iIntros "H". rewrite /fwc_owed. iRight. by iRight. Qed.
  Lemma fwc_sp_taint k v I : FT -∗ fwc_sp k v I.
  Proof using . iIntros "H". rewrite /fwc_sp. by iRight. Qed.
  Lemma fwc_open_taint k v I : FT -∗ fwc_open k v I.
  Proof using . iIntros "H". rewrite /fwc_open. by iRight. Qed.
  Lemma fwc_sp_t_taint k v I : FT -∗ fwc_sp_t k v I.
  Proof using . iIntros "H". rewrite /fwc_sp_t. by iRight. Qed.
  Lemma fwc_open_t_taint k v I : FT -∗ fwc_open_t k v I.
  Proof using . iIntros "H". rewrite /fwc_open_t. by iRight. Qed.
  Lemma fwc_ban_taint k v I i : FT -∗ fwc_ban k v I i.
  Proof using . iIntros "H". rewrite /fwc_ban. iRight. by iRight. Qed.
  Lemma fwc_line_taint k v I : FT -∗ fwc_line k v I.
  Proof using . iIntros "H". rewrite /fwc_line. iLeft. by iApply fwc_pro_taint. Qed.
  Lemma fwc_lend_taint k v I : FT -∗ fwc_lend k v I.
  Proof using . iIntros "H". rewrite /fwc_lend. by iRight. Qed.

  (* ---- the loose shapes and the tight ones ---- *)
  Lemma fwc_pro_owed k v I : fwc_pro k v I -∗ fwc_owed k v I.
  Proof using .
    rewrite /fwc_pro /fwc_owed.
    iIntros "[H | [H | H]]"; [| by iRight; iLeft | by iRight; iRight].
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. by left.
  Qed.

  Lemma fwc_blk_owed k v I a : fwc_blk k v I a 0%nat -∗ fwc_owed k v I.
  Proof using .
    rewrite /fwc_blk /fwc_owed.
    iIntros "[H | H]"; [| by iRight; iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [blkcs_f]. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, s0, P. rewrite /fcur. iFrame "Htn Hps Hcs HE Hf".
    iPureIntro. right. exact (proj1 Hw).
  Qed.

  Lemma fwc_sp_t_sp k v I : fwc_sp_t k v I -∗ fwc_sp k v I.
  Proof using .
    rewrite /fwc_sp_t /fwc_sp. iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma fwc_open_t_open k v I : fwc_open_t k v I -∗ fwc_open k v I.
  Proof using .
    rewrite /fwc_open_t /fwc_open. iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma fwc_blk_0 k v I a a' :
    fwc_blk k v I a 0%nat -∗ fwc_blk k v I a' 0%nat.
  Proof using . rewrite /fwc_blk. cbn [blkcs_f]. iIntros "H". iExact "H". Qed.

  Lemma fwc_post_taint k v I a : FT -∗ fwc_post k v I a.
  Proof using . iIntros "H". rewrite /fwc_post. by iRight. Qed.

  (* the landed shape is the instance at a state-free alternative *)
  Lemma fwc_post_of_blk k v I a :
    fapr I a -> fwc_blk k v I a (length (fab I a) - 2)%nat -∗ fwc_post k v I a.
  Proof using .
    intros Ha. rewrite /fwc_blk /fwc_post. iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    iLeft. iExists ps, cs, s0, P. rewrite (fabs_fab s0 cs I a Ha).
    iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
  Qed.

  Lemma fwc_line_of_blk0 k v I a : fwc_blk k v I a 0%nat -∗ fwc_line k v I.
  Proof using .
    iIntros "Hc". rewrite /fwc_line. iRight.
    iExists (fnoc_of (fline I)).
    iSplitR; [iPureIntro; exact (fapr_faprs _ _ (fapr_noc I)) |].
    iApply (fwc_post_of_blk k v I _ (fapr_noc I)).
    rewrite (fab_noc I) EchoLinks.wr_prompt_len.
    cbn [Nat.sub]. iApply (fwc_blk_0 with "Hc").
  Qed.

  Lemma fwc_line_of_post k v I a :
    fapr I a -> fwc_blk k v I a (length (fab I a) - 2)%nat -∗ fwc_line k v I.
  Proof using .
    intros Ha. iIntros "Hc". rewrite /fwc_line. iRight. iExists a.
    iSplitR; [iPureIntro; exact (fapr_faprs I a Ha) |].
    iApply (fwc_post_of_blk k v I a Ha with "Hc").
  Qed.

  (* ...and the state-aware producer, which is what a round whose bytes are
     the file's closes on *)
  Lemma fwc_line_of_posts k v I a :
    faprs I a -> fwc_post k v I a -∗ fwc_line k v I.
  Proof using .
    intros Ha. iIntros "Hc". rewrite /fwc_line. iRight. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma fwc_line_of_pro k v I : fwc_pro k v I -∗ fwc_line k v I.
  Proof using . iIntros "Hc". rewrite /fwc_line. by iLeft. Qed.

  Lemma fwc_lend_of_blk0 k v I a : fwc_blk k v I a 0%nat -∗ fwc_lend k v I.
  Proof using .
    rewrite /fwc_blk /fwc_lend. cbn [blkcs_f].
    iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    rewrite Nat.add_0_r. iLeft. iExists ps, cs, s0, P.
    rewrite /fcur. by iFrame "Htn Hps Hcs HE Hf".
  Qed.

  Lemma fwc_blk_sp k v I a :
    fapr I a ->
    fwc_blk k v I a (length (fab I a) - 1)%nat -∗ fwc_sp_t k v I.
  Proof using .
    intros Ha. rewrite /fwc_blk /fwc_sp_t. iIntros "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    pose proof (fab_len_ge2 I a Ha) as Hlen.
    assert (Hbc : blkcs_f cs a (length (fab I a) - 1)%nat = cs ++ [a]).
    { destruct (length (fab I a) - 1)%nat as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]), s0,
      (P + (length (fab I a) - 1))%nat.
    rewrite /fcur. iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (wr_blk_sp_f ps cs s0 I P a Hw Ha).
  Qed.

  (* ---- the banner's readings ---- *)
  Lemma fwc_ban_pro k v I : fwc_ban k v I 0%nat -∗ fwc_pro k v I.
  Proof using .
    rewrite /fwc_ban /fwc_pro.
    iIntros "[H | [[_ H] | H]]"; [| by iRight; iLeft | by iRight; iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [wr_banp_f] in Hw. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, s0, P. rewrite /fcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (wr_ban_pro_f ps cs s0 I P Hw).
  Qed.

  Lemma fwc_ban_owed k v I : fwc_ban k v I 0%nat -∗ fwc_owed k v I.
  Proof using .
    iIntros "Hc". iApply fwc_pro_owed. iApply (fwc_ban_pro with "Hc").
  Qed.

  Lemma fwc_ban_done_pro k v I :
    fwc_ban k v I (length u_banner) -∗ fwc_pro k v I.
  Proof using .
    rewrite /fwc_ban /fwc_pro.
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18.
    iIntros "[H | [[%Hq _] | H]]"; [| discriminate Hq | by iRight; iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [wr_banp_f] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, s0, (P + 18)%nat. rewrite /fcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    pose proof (wr_ban_done_f ps' cs s0 I P Hw) as H. by rewrite H18 in H.
  Qed.

  Lemma fwc_ban_done k v I :
    fwc_ban k v I (length u_banner) -∗ fwc_owed k v I.
  Proof using .
    iIntros "Hc". iApply fwc_pro_owed. iApply (fwc_ban_done_pro with "Hc").
  Qed.

  Lemma fwc_ban_done_line k v I :
    fwc_ban k v I (length u_banner) -∗ fwc_line k v I.
  Proof using .
    iIntros "Hc". iApply fwc_line_of_pro.
    iApply (fwc_ban_done_pro with "Hc").
  Qed.

  Lemma fwc_ban_inp k v I :
    fwc_ban k v I 0%nat -∗
    fwc_ban k v I 0%nat ∗ ((inp_lb v I ∗ ⌜rest_of I = []⌝) ∨ FT).
  Proof using .
    rewrite /fwc_ban.
    iIntros "[H | [[%Hi H] | #H]]"; last first.
    { iSplitR; [iRight; by iRight | iRight; iExact "H"]. }
    { iDestruct "H" as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iSplitR "".
      - iRight. iLeft. iSplitR; [by iPureIntro |].
        rewrite /fhead. by iFrame "Htn Hps Hcs HE Hvf Hpre".
      - iLeft. subst I. iFrame "HE". iPureIntro. exact rest_of_nil. }
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    cbn [wr_banp_f] in Hw.
    iSplitL "Htn".
    - iLeft. iExists ps, cs, s0, P. by iFrame "Htn Hps Hcs HE Hf".
    - iLeft. iFrame "HE". iPureIntro. exact (proj1 (proj2 Hw)).
  Qed.

  (* ---- the read of a completed line ---- *)
  Lemma fwc_read k v I l :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ fwc_open k v I -∗
    fwc_owed k v (I ++ l ++ [wl_nl]).
  Proof using .
    intros Hl. iIntros "#HE' Hc". rewrite /fwc_open /fwc_owed.
    iDestruct "Hc" as "[H | H]"; [| by iRight; iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & _ & Hf)".
    iLeft. iExists ps, cs, s0, P. rewrite /fcur.
    iFrame "Htn Hps Hcs HE' Hf". iPureIntro. right.
    exact (wr_open_read_f ps cs s0 I P l Hw Hl).
  Qed.

  Lemma fwc_read_t k v I a l :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ fwc_open_t k v I -∗
    fwc_blk k v (I ++ l ++ [wl_nl]) a 0%nat.
  Proof using .
    intros Hl. iIntros "#HE' Hc". rewrite /fwc_open_t /fwc_blk.
    iDestruct "Hc" as "[H | H]"; [| by iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & _ & Hf)".
    iLeft. iExists ps, cs, s0, P. cbn [blkcs_f]. rewrite Nat.add_0_r.
    iFrame "Htn Hps Hcs HE' Hf". iPureIntro.
    exact (wr_open_read_t_f ps cs s0 I P l Hw Hl).
  Qed.

  (* ---- the panic's five bytes leave the next round's banner ---- *)
  Lemma fwc_panic_done k v I :
    fwc_blk k v I (fpan_of (fline I))
      (length (fab I (fpan_of (fline I)))) -∗ fwc_ban k v I 0%nat.
  Proof using .
    rewrite /fwc_blk /fwc_ban.
    iIntros "[H | H]"; [| by iRight; iRight].
    iDestruct "H" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    assert (Hbc : blkcs_f cs (fpan_of (fline I))
                    (length (fab I (fpan_of (fline I))))
                  = cs ++ [fpan_of (fline I)]).
    { rewrite (fab_pan I) alt_panic_len5. reflexivity. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [fpan_of (fline I)]), s0,
      (P + length (fab I (fpan_of (fline I))))%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE Hf". iPureIntro. cbn [wr_banp_f].
    exact (wr_blk_ban_f ps cs s0 I P Hw).
  Qed.


  (* =================================================================== *)
  (*  S9  THE STEPS, THROUGH [FileLinks.file_links]                       *)
  (* =================================================================== *)
  Local Notation FPIN := (era_pin (fgn_echo g)).

  Lemma fi_pin_epin (k : nat) (v : era_pins) :
    era_pin (fgn_echo g) k v -∗ era_pin (fgn_echo g) k v.
  Proof using . by iIntros "$". Qed.

  (* ---- /init's banner ---- *)
  Lemma fban_step (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    u_banner !! i = Some b ->
    FPIN k v -∗ file_links g -∗ fwc_ban k v I i -∗
    (fwc_ban k v I (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_ban.
    iDestruct "Hc" as "[Hl | [[%Hi0 Hh] | #HT]]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_ban_taint. }
    { (* THE ERA'S HEAD: the first byte FILES the boot state *)
      subst i. rewrite /fhead.
      iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iDestruct "Hvf" as (vf) "#Hvf".
      iDestruct "Hpre" as (s0) "(%Hok & Hty & Hbw)".
      iDestruct "Hbw" as "[_ Hbw]". iDestruct "Hbw" as (vf') "[#Hvf' #Hbl]".
      iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
      iApply ("Hfst" $! (S gen_id) v vf 3%nat b s0 Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hbl Hty [HΦ]").
      { exact Hok. }
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_ban.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]";
        last by (iRight; iRight).
      iLeft. iExists [3%nat], [], s0, 0%nat.
      rewrite Nat.add_0_l. iFrame "Htn' Hps' Hcs' HE'".
      iSplitR.
      { iPureIntro. cbn [wr_banp_f]. exists []. split; [reflexivity |].
        exact (wr_ban_round0_f s0). }
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0". }
    iDestruct "Hl" as (ps cs s0 P)
      "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    destruct i as [| i'].
    - (* the first byte FILES the banner letter *)
      cbn [wr_banp_f] in Hw.
      pose proof (wr_ban_pro_f ps cs s0 I P Hw) as Hpr.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      destruct Hpr as (_ & _ & _ & _ & Hnd & HP).
      rewrite Nat.add_0_r.
      rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
      iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hpro" $! k v vf P 3%nat b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin0. }
      { exact Hnd. }
      { exact HP. }
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_ban.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by (iRight; iRight).
      iLeft. iExists (ps ++ [3%nat]), cs, s0, P.
      replace (P + 1)%nat with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE'".
      iSplitR; [iPureIntro; cbn [wr_banp_f]; by exists ps |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* every later byte is an ordinary write of the filed letter *)
      cbn [wr_banp_f] in Hw. destruct Hw as (ps' & -> & Hw).
      pose proof (wr_ban_byte_f ps' cs s0 I P (S i') b Hw Hb) as Hby.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
      iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
      iApply ("Hw" $! k v vf (P + S i')%nat b (ps' ++ [3%nat]) cs s0 I Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { lia. }
      { exact (pro_pin_f_mono ps' (ps' ++ [3%nat]) cs I ltac:(by eexists)
                 Hpin0). }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_ban.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by (iRight; iRight).
      iLeft. iExists (ps' ++ [3%nat]), cs, s0, P.
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'".
      iSplitR; [iPureIntro; cbn [wr_banp_f]; by exists ps' |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* ---- one byte of a block ---- *)
  Lemma fblk_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    fab I a !! i = Some b ->
    FPIN k v -∗ file_links g -∗ fwc_blk k v I a i -∗
    (fwc_blk k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_blk with "Hlk") as "#Hblk".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    destruct (fab_ok I a i b Hb) as [Hok Hfr].
    rewrite {1}/fwc_blk. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_blk_taint. }
    iDestruct "Hl" as (ps cs s0 P)
      "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    pose proof (proj1 Hw) as Hwb.
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    pose proof (wr_blk_nonnil_f ps cs s0 I P Hwb) as Hne.
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct i as [| i'].
    - (* THE BLOCK-FIRST BYTE files the alternative *)
      cbn [blkcs_f]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v vf P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hne. }
      { exact Hr. }
      { rewrite Hn. lia. }
      { exact Hpin0. }
      { exact HP. }
      { rewrite -/(fline I). exact Hok. }
      { rewrite -/(fline I) -(fab_at I a _ Hok Hfr). exact Hb. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_blk.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, cs, s0, P. cbn [blkcs_f].
      replace (P + 1)%nat with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* every byte after it, at the choice list the first one extended *)
      cbn [blkcs_f].
      iApply ("Hw" $! k v vf (P + S i')%nat b ps (cs ++ [a]) s0 I Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { rewrite length_app Hn. cbn [length]. lia. }
      { exact (wr_blk_pin_snoc_f ps cs s0 I P a Hwb). }
      { pose proof (wr_blk_pending_pre_f ps cs s0 I P a Hwb Hok Hfr) as Hpre.
        rewrite /proc_stream_f (wr_blk_low_f ps cs s0 I P a Hwb)
                lookup_app_r; [| lia].
        replace (P + S i' - length (proc_before_f ps cs (Some s0) I))%nat
          with (S i') by lia.
        exact (prefix_lookup_Some _ _ _ _ Hb Hpre). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_blk.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, cs, s0, P. cbn [blkcs_f].
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* ---- the era's very first byte, as the shell's bare prompt ---- *)
  Lemma wr_sp_f_head (s0 : fstate) : wr_sp_f [0%nat] [] s0 [] 1%nat.
  Proof using .
    assert (Hstr : proc_stream_f [0%nat] [] (Some s0) [] = u_prompt).
    { rewrite /proc_stream_f proc_before_f_nil pending_at_f_nil app_nil_l.
      by vm_compute. }
    split.
    - rewrite /wr_open_f. split_and!.
      + exact (pro_pin_f_nil _ _).
      + exact rest_of_nil.
      + by rewrite nlines_nil.
      + rewrite nlines_nil. cbn [pro_idx_f].
        rewrite EchoLinks.pro_rounds_one. lia.
      + rewrite Hstr EchoLinks.wr_prompt_len. reflexivity.
    - rewrite Hstr. exact EchoLinks.wr_prompt_tail.
  Qed.

  (* the head arm's '$': [file_write_link_first] at alternative 0 *)
  Lemma fhead_dollar (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fhead k v I -∗
    (fwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hh HΦ".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    rewrite /fhead.
    iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iDestruct "Hvf" as (vf) "#Hvf".
    iDestruct "Hpre" as (s0) "(%Hok & Hty & Hbw)".
    iDestruct "Hbw" as "[_ Hbw]". iDestruct "Hbw" as (vf') "[#Hvf' #Hbl]".
    iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
    iApply ("Hfst" $! (S gen_id) v vf 0%nat b s0 Φ
              with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hbl Hty [HΦ]").
    { exact Hok. }
    { rewrite pro_alts_length. lia. }
    { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_sp.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]";
      last by iRight.
    iLeft. iExists [0%nat], [], s0, 1%nat.
    iFrame "Htn' Hps' Hcs' HE'".
    iSplitR; [iPureIntro; exact (wr_sp_f_head s0) |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0".
  Qed.

  (* ---- the prompt's '$' at the LOOSE boundary ---- *)
  Lemma fprompt_dollar (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_owed k v I -∗
    (fwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_blk with "Hlk") as "#Hblk".
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_owed.
    iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_sp_taint. }
    { iApply (fhead_dollar k v I b Φ Hb with "Hpin Hlk Hh HΦ"). }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct Hw as [Hw | Hw].
    - (* the round's prologue is open: the '$' files alternative 0 *)
      pose proof (wr_pro_dollar_f ps cs s0 I P Hw) as Hsp.
      destruct Hw as (Hpin0 & Hm & Hdv & Hr & Hnd & HP).
      iApply ("Hpro" $! k v vf P 0%nat b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
      { exact Hnd. } { exact HP. }
      { rewrite pro_alts_length. lia. }
      { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists (ps ++ [0%nat]), cs, s0, (S P).
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* the round is settled: the '$' is the line's block-first byte *)
      pose proof (wr_blk_dollar_f ps cs s0 I P Hw) as Hsp.
      pose proof (wr_blk_nonnil_f ps cs s0 I P Hw) as Hne.
      pose proof Hw as (Hpin0 & Hm & Hdv & HP).
      iApply ("Hblk" $! k v vf P (fnoc_of (fline I)) b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hne. } { exact Hm. } { rewrite Hdv. lia. } { exact Hpin0. }
      { exact HP. }
      { rewrite -/(fline I). exact (fnoc_of_ok (fline I)). }
      { rewrite -/(fline I) (cont_fnoc _ (fline I)) Hb.
        exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, (cs ++ [fnoc_of (fline I)]), s0, (S P).
      iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* ---- the ' ' after it ---- *)
  Lemma fprompt_space (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    FPIN k v -∗ file_links g -∗ fwc_sp k v I -∗
    (fwc_open k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_sp. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_open_taint. }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct Hw as [Hop Hby].
    pose proof Hop as (Hpin0 & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v vf P b ps cs s0 I Φ
              with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
    { lia. } { exact Hpin0. } { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_open.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
      last by iRight.
    iLeft. iExists ps, cs, s0, (S P).
    iFrame "Htn' Hps' Hcs' HE'".
    iSplitR; [iPureIntro; exact (wr_sp_open_f ps cs s0 I P (conj Hop Hby)) |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  Lemma fprompt_dollar_ban (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_ban k v I 0%nat -∗
    (fwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (fprompt_dollar k v I b Φ Hb with "Hpin Hlk [Hc] HΦ").
    iApply (fwc_ban_owed with "Hc").
  Qed.

  (* ---- the prompt at the TIGHT shapes ---- *)
  Lemma fprompt_dollar_post (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) (b : bv 8) (Φ : iProp Σ) :
    fapr I a -> b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗
    fwc_blk k v I a (length (fab I a) - 2)%nat -∗
    (fwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Ha Hb. iIntros "#Hpin #Hlk Hc HΦ".
    pose proof (fab_len_ge2 I a Ha) as Hlen.
    assert (Hby : fab I a !! (length (fab I a) - 2)%nat = Some b)
      by (rewrite Hb; exact (fab_dollar I a Ha)).
    iApply (fblk_step k v I a (length (fab I a) - 2)%nat b Φ Hby
              with "Hpin Hlk Hc [HΦ]").
    iIntros "Hc". iApply "HΦ".
    replace (S (length (fab I a) - 2))%nat
      with (length (fab I a) - 1)%nat by lia.
    iApply (fwc_blk_sp k v I a Ha with "Hc").
  Qed.

  Lemma fprompt_space_t (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    FPIN k v -∗ file_links g -∗ fwc_sp_t k v I -∗
    (fwc_open_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_sp_t. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_open_t_taint. }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct Hw as [[Hop Hby] Htl].
    pose proof Hop as (Hpin0 & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v vf P b ps cs s0 I Φ
              with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
    { lia. } { exact Hpin0. } { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_open_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
      last by iRight.
    iLeft. iExists ps, cs, s0, (S P).
    iFrame "Htn' Hps' Hcs' HE'".
    iSplitR;
      [iPureIntro;
       exact (wr_sp_open_t_f ps cs s0 I P (conj (conj Hop Hby) Htl)) |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* THE PROMPT'S DOLLAR AT THE STATE-AWARE POST.  [fblk_step]'s two arms at
     the one index that matters here -- the block's last-but-one byte -- with
     the byte read off [fabs] at the credential's OWN choice list. *)
  Lemma fprompt_dollar_posts (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) (b : bv 8) (Φ : iProp Σ) :
    faprs I a -> b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_post k v I a -∗
    (fwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Ha Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_blk with "Hlk") as "#Hblk".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    pose proof Ha as [Hok Hnp].
    rewrite {1}/fwc_post. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /fwc_sp_t. by iRight. }
    iDestruct "Hl" as (ps cs s0 P)
      "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    pose proof (proj1 Hw) as Hwb.
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    pose proof (wr_blk_nonnil_f ps cs s0 I P Hwb) as Hne.
    pose proof (fabs_len_ge2 s0 cs I a Ha) as Hlen.
    pose proof (fabs_dollar s0 cs I a Ha) as Hby. rewrite -Hb in Hby.
    pose proof (wr_blk_sp_fs ps cs s0 I P a Hw Ha) as Hsp.
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    destruct (length (fabs s0 cs I a) - 2)%nat as [| i'] eqn:Hi.
    - (* the prompt IS the block's first byte: it files the alternative *)
      cbn [blkcs_f]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v vf P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hne. }
      { exact Hr. }
      { rewrite Hn. lia. }
      { exact Hpin0. }
      { exact HP. }
      { rewrite -/(fline I). exact Hok. }
      { rewrite -/(fline I). exact Hby. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_t.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, (cs ++ [a]), s0, (S P).
      replace (P + (length (fabs s0 cs I a) - 1))%nat with (S P) in Hsp by lia.
      replace (P + 1)%nat with (S P) by lia.
      rewrite /fcur. iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
    - (* an ordinary byte of a block already filed *)
      cbn [blkcs_f].
      iApply ("Hw" $! k v vf (P + S i')%nat b ps (cs ++ [a]) s0 I Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
      { rewrite length_app Hn. cbn [length]. lia. }
      { exact (wr_blk_pin_snoc_f ps cs s0 I P a Hwb). }
      { exact (wr_blk_byte_fs ps cs s0 I P a (S i') b Hwb Hnp Hby). }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_t.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, (cs ++ [a]), s0, (S (P + S i')).
      replace (P + (length (fabs s0 cs I a) - 1))%nat
        with (S (P + S i')) in Hsp by lia.
      rewrite /fcur. iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  Lemma fprompt_dollar_line (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ fwc_line k v I -∗
    (fwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    rewrite {1}/fwc_line. iDestruct "Hc" as "[Hc | Hc]"; last first.
    { iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (fprompt_dollar_posts k v I a b Φ Ha Hb with "Hpin Hlk Hc HΦ"). }
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_first with "Hlk") as "#Hfst".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    rewrite {1}/fwc_pro. iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply fwc_sp_t_taint. }
    { (* the era's head: the '$' is its first byte, and it lands TIGHT *)
      rewrite /fhead.
      iDestruct "Hh" as "(-> & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
      iDestruct "Hvf" as (vf) "#Hvf".
      iDestruct "Hpre" as (s0) "(%Hok & Hty & Hbw)".
      iDestruct "Hbw" as "[_ Hbw]". iDestruct "Hbw" as (vf') "[#Hvf' #Hbl]".
      iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
      iApply ("Hfst" $! (S gen_id) v vf 0%nat b s0 Φ
                with "[%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hbl Hty [HΦ]").
      { exact Hok. }
      { rewrite pro_alts_length. lia. }
      { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_t.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0) | #HT]";
        last by iRight.
      iLeft. iExists [0%nat], [], s0, 1%nat.
      iFrame "Htn' Hps' Hcs' HE'".
      iSplitR.
      { iPureIntro. split; [exact (wr_sp_f_head s0) |].
        rewrite /wr_tail_f. cbn [length pro_idx_f]. by vm_compute. }
      rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0". }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    pose proof (wr_pro_dollar_t_f ps cs s0 I P Hw) as Hsp.
    destruct Hw as (Hpin0 & Hm & Hdv & Hr & Hnd & HP).
    iApply ("Hpro" $! k v vf P 0%nat b ps cs s0 I Φ
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ]").
    { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
    { exact Hnd. } { exact HP. }
    { rewrite pro_alts_length. lia. }
    { rewrite EchoLinks.wr_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
    iIntros "Hres". iApply "HΦ". rewrite /fwc_sp_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
      last by iRight.
    iLeft. iExists (ps ++ [0%nat]), cs, s0, (S P).
    iFrame "Htn' Hps' Hcs' HE'". iSplitR; [by iPureIntro |].
    rewrite /f0w. iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hvf Hf0'".
  Qed.

  (* ---- the era's turn, and what it comes apart into ---- *)
  Definition fturn_pre (k : nat) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ FileOut.fturn_core g k ∗ f0pre)%I.

  Lemma fturn0 (k : nat) :
    fturn_pre k -∗
    (∃ v : era_pins, FPIN k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, FPIN k v ∗ fwc_ban k v [] 0%nat).
  Proof using .
    rewrite /fturn_pre /FileOut.fturn_core.
    iIntros "(%Hk & Ht & Hpre)".
    iDestruct "Ht" as (v vf)
      "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin". rewrite /fwc_ban. iRight. iLeft.
    iSplitR; [by iPureIntro |]. rewrite /fhead.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE Hpre". iExists vf. iExact "Hvf".
  Qed.

  (* ---- a read past a boundary whose prompt is unwritten is the taint ---- *)
  Lemma fowed_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    fwc_owed k v I -∗ fread_ret g k v n ws -∗ FT.
  Proof using .
    intros HIn Hws. iIntros "Hc Hr".
    rewrite /fread_ret.
    iDestruct "Hr" as "[[#HT _] | [Hdlr Hfacts]]"; [iExact "HT" |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & %Hboots & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0 vf s0)
      "(#Hcs0 & #Hps0 & #Hvf & #Hf0 & %Hbd & #Htlb & %Hrs)".
    set (J := (snd <$> (dl ++ ws))%list).
    assert (Hlen : length J = (n + length ws)%nat).
    { rewrite /J length_fmap length_app Hdl. reflexivity. }
    rewrite /fwc_owed.
    iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last by iExact "HT".
    - iDestruct "Hl" as (ps cs s1 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf']".
      iDestruct "Hvf'" as (vf') "[#Hvf' #Hf0']".
      iDestruct (file_era_pin_agree with "Hvf' Hvf") as %<-.
      iDestruct (f0_lb_agree with "Hf0' Hf0") as %<-.
      iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
      iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iDestruct (inp_lb_cmp with "HE Hinp") as %Hic.
      iExFalso. iPureIntro.
      assert (HI : I `prefix_of` J).
      { destruct Hic as [Hc | Hc]; [exact Hc |].
        exfalso. apply prefix_length in Hc. lia. }
      assert (Hne : I <> J) by (intros Hq; rewrite Hq Hlen in HIn; lia).
      exact (wr_owed_read_refute_f ps cs ps0 cs0 s1 I J P Hw HI Hne Hrs
               Hpsc Hcsc Hle).
    - rewrite /fhead.
      iDestruct "Hh" as "(-> & %Hk & Htn & #Hps & #Hcs & #HE & _ & _)".
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iExFalso. iPureIntro.
      assert (HI : ([] : list (bv 8)) `prefix_of` J) by apply prefix_nil.
      assert (Hne : ([] : list (bv 8)) <> J).
      { intros Hq. rewrite -Hq in Hlen. cbn [length] in Hlen.
        cbn [length] in HIn. lia. }
      refine (wr_owed_read_refute_f [] [] ps0 cs0 s0 [] J 0%nat _ HI Hne Hrs
                ltac:(left; apply prefix_nil) ltac:(left; apply prefix_nil)
                ltac:(lia)).
      left. rewrite /wr_pro_f. split_and!.
      + exact (pro_pin_f_nil _ _).
      + exact rest_of_nil.
      + by rewrite nlines_nil.
      + by left.
      + rewrite nlines_nil. cbn [pro_idx_f pro_from].
        rewrite -pro_fail_0. exact (pro_done_fail 0%nat).
      + rewrite /proc_stream_f proc_before_f_nil pending_at_f_nil.
        by cbn [app pro_of length].
  Qed.

  Lemma fban_read_taint (k : nat) (v : era_pins) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    fwc_ban k v I 0%nat -∗ fwc_rres v (I ++ l ++ [wl_nl]) -∗ FT.
  Proof using .
    intros Hnl. iIntros "Hc #Hres".
    rewrite /fwc_rres.
    iDestruct "Hres" as (ps0 cs0 s0) "(%Hrs & #Htlb & #Hps0 & #Hcs0 & #Hf0)".
    assert (Hpre : I `prefix_of` (I ++ l ++ [wl_nl])) by (by eexists).
    assert (Hne : I <> I ++ l ++ [wl_nl]).
    { intro Heq. apply (f_equal length) in Heq.
      rewrite !length_app length_cons in Heq. lia. }
    rewrite /fwc_ban.
    iDestruct "Hc" as "[Hl | [[_ Hh] | #HT]]"; last by iExact "HT".
    - iDestruct "Hl" as (ps cs s1 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      cbn [wr_banp_f] in Hw.
      iDestruct (f0w_bw_agree with "Hf Hf0") as %<-.
      iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
      iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
      rewrite Nat.add_0_r.
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iExFalso. iPureIntro.
      exact (wr_owed_read_refute_f ps cs ps0 cs0 s1 I (I ++ l ++ [wl_nl]) P
               (or_introl (wr_ban_pro_f ps cs s1 I P Hw)) Hpre Hne Hrs
               Hpsc Hcsc Hle).
    - rewrite /fhead.
      iDestruct "Hh" as "(-> & %Hk & Htn & #Hps & #Hcs & #HE & _ & _)".
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      rewrite app_nil_l in Hle.
      iExFalso. iPureIntro.
      refine (wr_owed_read_refute_f [] [] ps0 cs0 s0 [] (l ++ [wl_nl]) 0%nat
                _ ltac:(apply prefix_nil) _ Hrs
                ltac:(left; apply prefix_nil) ltac:(left; apply prefix_nil)
                ltac:(lia)).
      + left. rewrite /wr_pro_f. split_and!.
        * exact (pro_pin_f_nil _ _).
        * exact rest_of_nil.
        * by rewrite nlines_nil.
        * by left.
        * rewrite nlines_nil. cbn [pro_idx_f pro_from].
          rewrite -pro_fail_0. exact (pro_done_fail 0%nat).
        * rewrite /proc_stream_f proc_before_f_nil pending_at_f_nil.
          by cbn [app pro_of length].
      + intro Hq. apply (f_equal length) in Hq.
        rewrite length_app length_cons in Hq. cbn [length] in Hq. lia.
  Qed.

End file_links_line.
