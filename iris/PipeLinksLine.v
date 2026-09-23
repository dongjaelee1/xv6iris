(* ===================================================================== *)
(*  PipeLinksLine.v -- THE PIPELINE APPLICATION'S CREDENTIAL FAMILIES     *)
(*  AND THEIR LAWS, i.e. everything [LinkRec.LinkRec] asks of an          *)
(*  application besides the link BUNDLE ([PipeLinks.pipe_links]).         *)
(*                                                                       *)
(*  Lane PIPE-LINK-INST (design app-pipe.md section 5.8, STOP B).         *)
(*  [EchoLinks.v] + [EchoLinksLine.v] + [EchoLinksPro.v] at the PIPELINE  *)
(*  stage, in [FileLinksLine.v]'s layout and with [FileLinksLine]'s names *)
(*  spelled with a [p] where the file spells an [f] -- so that the        *)
(*  round's port ([UShRound.v], stated end to end at                      *)
(*  [FileLinkInst.file_link_inst_at]) is a rename.                        *)
(*                                                                       *)
(*  WHAT IS SIMPLER THAN THE FILE'S.  There is no era state: no [o_fh],   *)
(*  no boot value [s0], no typed witness and no file deed, so every       *)
(*  family is [EchoLinks]'s existential over [ps], [cs] and [P] alone and *)
(*  the record needs only ONE instance (there is no state to index it     *)
(*  at).  The alternative's output [pab I a] reads the LINE and the       *)
(*  ALTERNATIVE and nothing else ([PipeDisc.pcont]).                      *)
(*                                                                       *)
(*  WHAT THE DESIGN GOT WRONG, and the one place this file is not the     *)
(*  file's minus a field: [pab] still needs the ADMISSIBILITY guard.      *)
(*  The design (app-pipe.md section 5.7 finding 8, and the lane brief)    *)
(*  says [lk_ab I a := pcont (pline_at I) (palt_of a)] needs "NO guard".  *)
(*  It needs no STATE guard -- that is the file's [fst_free] and it is    *)
(*  genuinely gone -- but it must still keep [palt_ok]: [pcont l a] is    *)
(*  NON-EMPTY at every [a] whatsoever ([PipeOutPure.pcont_nonnil]),       *)
(*  including the ones the line does not admit ([PPipe] at an [LEcho]     *)
(*  line, [PEcho 1] at an [LPipe] one), whereas echo's                    *)
(*  [line_alts_of ws !!! a] is [[]] out of range and the file's [fab]     *)
(*  decides.  Unguarded, a byte lookup would say nothing and              *)
(*  [PipeLinks.pipe_write_link_blk]'s [palt_ok] premise would be          *)
(*  unsuppliable -- i.e. [lk_blk_step] would be unprovable.               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
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
Require Import PipeDiscDec.
Require Import PipeOutPure.
Require Import LineModel.       (* the line model, and its writer-side reading *)
Require Import LineModelLinks.
Require Import LineModelInst.   (* the stream equations at [pipe_lm] *)
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import EchoLinks.        (* the SHARED prologue/prompt lemmas *)
Require Import EchoLinksLine.    (* ...and the SHARED alternative lengths *)
Require Import EchoLinksPro.     (* ...and the SHARED prologue arithmetic *)
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
(* as in EchoDisc / PipeDisc / PipeOut: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.


(* ===================================================================== *)
(*  S0  THE LINE, AND ITS ALTERNATIVES' OUTPUT                            *)
(* ===================================================================== *)

(* the line the last COMPLETE body of [I] parses to ([FileLinksLine.fline]) *)
Definition pline_at (I : list (bv 8)) : pline :=
  pline_of (bodies_of I !!! (nlines I - 1)%nat).

(* THE RECORD'S [lk_ab]: the block alternative [a] owes at input [I],
   guarded by ADMISSIBILITY alone (see the header). *)
(* THE GUARD GAINS [palt_isforkS = false] (lane PIPE-MODEL-3): the
   terminal fork-failure round's block is NEVER written through this
   layer -- it is written by TWO processes at the two cursors and its
   code is never filed -- and [PipeOut.pecl_step_write_blk], which files
   the code at the block's FIRST byte, must not be reachable at it.  The
   guard is where the claim's [cs_nofork] comes from: [pab_nofork]
   carries it out of the same lookup [pab_ok] reads. *)
Definition pab_gd (I : list (bv 8)) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a) /\ palt_isforkS (palt_of a) = false.

Global Instance pab_gd_dec I a : Decision (pab_gd I a).
Proof using. rewrite /pab_gd. apply _. Defined.

Definition pab (I : list (bv 8)) (a : nat) : list (bv 8) :=
  if decide (pab_gd I a)
  then pcont (pline_at I) (palt_of a) else [].

(* THE RECORD'S [lk_apr]: the alternative is admissible and does not
   reopen the prologue -- which is exactly when its output ends with the
   shell's prompt ([PipeDisc.pcont_shape], minus the [pline_ok] premise a
   WRITER does not hold; [pcont_prompt] below). *)
Definition papr (I : list (bv 8)) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a) /\ palt_panic (palt_of a) = false
  /\ palt_isforkS (palt_of a) = false.




(* ---- THE BLOCK'S LAST TWO BYTES ARE THE SHELL'S PROMPT.  [pcont_shape]
        says so under [pline_ok]; a writer holds no such thing, so the
        "ends with the prompt" half is read off the eight constructors
        instead -- every one of them is literally [_ ++ u_prompt]. ---- *)
Lemma pcont_prompt (l : pline) (a : palt) :
  palt_ok l a -> palt_panic a = false -> palt_isforkS a = false ->
  exists u : list (bv 8), pcont l a = u ++ u_prompt.
Proof using.
  intros Hok Hp Hfk.
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont;
    [| | | | | | done |].
  - (* [PEcho k]: [k < 4] at an [LEcho] line, [k = 3] at an [LPipe] one --
       and the panic index is excluded, so [k < 3] either way. *)
    assert (Hk : (k < 3)%nat).
    { rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
      destruct l as [ws | ws]; cbn [palt_ok] in Hok; lia. }
    destruct k as [| [| [| k]]]; [| | | exfalso; lia].
    + exists (wl_line (drop 1 (pline_ws l))). exact (line_alts_of_0 _).
    + exists dg_execL. rewrite (line_alts_of_1 (pline_ws l)).
      by rewrite -alt_execL_echo /alt_execL.
    + exists []. rewrite (line_alts_of_2 (pline_ws l)). by rewrite app_nil_l.
  - exists (wl_line (drop 1 (pline_ws l))). reflexivity.
  - exists dg_execL. reflexivity.
  - exists dg_execR. reflexivity.
  - exists (pmerge sel dg_execL dg_execR). reflexivity.
  - exists (wl_line dg_pipe). reflexivity.
  - exists []. by rewrite app_nil_l.
Qed.

(* ...and what "ends with the prompt" buys, once, for the three readings
   the record asks for. *)
Lemma prompt_tail_facts (x u : list (bv 8)) :
  x = u ++ u_prompt ->
  (2 <= length x)%nat
  /\ x !! (length x - 2)%nat = Some (u_prompt !!! 0%nat)
  /\ x !! (length x - 1)%nat = Some (u_prompt !!! 1%nat).
Proof using.
  intros ->. rewrite length_app wr_prompt_len.
  split_and!; [lia | | ].
  - rewrite lookup_app_r; [| lia].
    replace (length u + 2 - 2 - length u)%nat with 0%nat by lia.
    exact wr_prompt_head.
  - rewrite lookup_app_r; [| lia].
    replace (length u + 2 - 1 - length u)%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.




(* ---- THE THREE NAMED ALTERNATIVES ------------------------------------ *)

(* THE PANIC is the LITERAL 3 at BOTH line shapes -- the coordinator's
   ruling of 2026-09-18 ([PipeDisc.palt_ok_pipe_panic]) is exactly what
   makes [lk_pan] a constant here where the file's is per-line. *)
Lemma palt_of_3 : palt_of 3%nat = PEcho 3%nat.
Proof using. apply palt_of_lt4. lia. Qed.

Lemma ppan_panic : palt_panic (palt_of 3%nat) = true.
Proof using. rewrite palt_of_3. by vm_compute. Qed.

Lemma ppan_ok (l : pline) : palt_ok l (palt_of 3%nat).
Proof using.
  rewrite palt_of_3. destruct l as [ws | ws]; cbn [palt_ok]; lia.
Qed.

Lemma pcont_ppan (l : pline) : pcont l (palt_of 3%nat) = alt_panic.
Proof using. apply pcont_panic. exact ppan_panic. Qed.

Lemma ppan_nofork : palt_isforkS (palt_of 3%nat) = false.
Proof using. rewrite palt_of_3. reflexivity. Qed.


(* THE EXEC-FAILED CHILD'S alternative is PER-LINE and the design's
   "literally 1" is refuted at the statement: [palt_ok (LPipe ws)
   (PEcho 1)] is FALSE (only [PEcho 3] joins a pipeline line's [PEcho]
   arms).  What IS echo's verbatim are the BYTES, through
   [PipeDisc.alt_execL_echo]. *)
Definition pexf_of (l : pline) : nat :=
  match l with LEcho _ => 1%nat | LPipe _ => palt_code PExecL end.

Definition pexfb (l : pline) : list (bv 8) :=
  match l with LEcho _ => alt_execfail | LPipe _ => alt_execL end.

Lemma pexfb_execfail (l : pline) : pexfb l = alt_execfail.
Proof using. destruct l; [reflexivity | exact alt_execL_echo]. Qed.

Lemma pexf_of_dec (l : pline) :
  palt_of (pexf_of l) = match l with LEcho _ => PEcho 1%nat | LPipe _ => PExecL end.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - apply palt_of_lt4. lia.
  - exact (palt_of_code PExecL).
Qed.

Lemma pexf_of_ok (l : pline) : palt_ok l (palt_of (pexf_of l)).
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). cbn [palt_ok]. lia.
  - rewrite (palt_of_code PExecL). exact I.
Qed.

Lemma pexf_of_nopanic (l : pline) : palt_panic (palt_of (pexf_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). by vm_compute.
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.

Lemma pcont_pexf (l : pline) : pcont l (palt_of (pexf_of l)) = pexfb l.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of pexfb].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). cbn [pcont pline_ws].
    exact (line_alts_of_1 ws).
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.

Lemma pexf_of_nofork (l : pline) : palt_isforkS (palt_of (pexf_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). reflexivity.
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.



(* THE ALTERNATIVE A ROUND TAKES WHEN NOBODY WROTE: the shell's own prompt
   IS the block's first byte.  [PEcho 2] at an echo line, [PSilent] at a
   pipeline one; both print [u_prompt]. *)
Definition pnoc_of (l : pline) : nat :=
  match l with LEcho _ => 2%nat | LPipe _ => palt_code PSilent end.

Lemma pnoc_of_dec (l : pline) :
  palt_of (pnoc_of l)
  = match l with LEcho _ => PEcho 2%nat | LPipe _ => PSilent end.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - apply palt_of_lt4. lia.
  - exact (palt_of_code PSilent).
Qed.

Lemma pnoc_of_ok (l : pline) : palt_ok l (palt_of (pnoc_of l)).
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). cbn [palt_ok]. lia.
  - rewrite (palt_of_code PSilent). exact I.
Qed.

Lemma pnoc_of_nopanic (l : pline) : palt_panic (palt_of (pnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). by vm_compute.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.

Lemma pcont_pnoc (l : pline) : pcont l (palt_of (pnoc_of l)) = u_prompt.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). cbn [pcont pline_ws].
    exact (EchoLinks.wr_line_alts_2 ws).
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.

Lemma pnoc_of_nofork (l : pline) : palt_isforkS (palt_of (pnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). reflexivity.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.






(* ---- THE MODEL'S HOOKS ([LineModelLinks.lm_hooks] at the pipeline
        model): the panic is the literal 3, the exec failure and the
        silent alternative are per-line, state-freedom is [~ PForkS] (the
        arm written by two processes never goes through this layer), and
        what a WRITER knows of a continuation is [pcont_prompt] /
        [PipeOutPure.pcont_nonnil].  Everything section 0 said of [pab] /
        [papr] is then [LineModelLinks]'s lemma read back through the
        equations below. ---- *)
Lemma pfree_term (a : palt) : negb (palt_isforkS a) = true -> palt_isforkS a = false.
Proof using. destruct (palt_isforkS a); [discriminate | reflexivity]. Qed.

Lemma pfree_of_nofork (a : palt) : palt_isforkS a = false -> negb (palt_isforkS a) = true.
Proof using. intros ->. reflexivity. Qed.

Lemma pcont_nonnil_dec (l : pline) (a : palt) :
  palt_ok l a \/ a = palt_of 0%nat -> pcont l a <> [].
Proof using.
  rewrite (palt_of_lt4 0%nat ltac:(lia)). exact (pcont_nonnil l a).
Qed.

Definition pipe_hooks : lm_hooks pipe_lm :=
  MkLMH pipe_lm (fun a => negb (palt_isforkS a)) tt (fun _ => 3%nat) pexf_of pexfb
    pnoc_of palt_ok_dec
    (fun _ _ _ _ _ => eq_refl) pfree_term
    ppan_ok (fun _ => pfree_of_nofork _ ppan_nofork) (fun _ => ppan_panic)
    pexf_of_ok (fun l => pfree_of_nofork _ (pexf_of_nofork l)) pexf_of_nopanic
    (fun _ l => pcont_pexf l)
    pnoc_of_ok (fun l => pfree_of_nofork _ (pnoc_of_nofork l)) pnoc_of_nopanic
    (fun _ l => pcont_pnoc l)
    (fun _ l a Hok Hp Ht => pcont_prompt l a Hok Hp Ht)
    (fun _ l a H => pcont_nonnil_dec l a H).

Lemma pline_at_lm (I : list (bv 8)) : pline_at I = lm_line_at pipe_lm I.
Proof using. reflexivity. Qed.

Lemma pab_lm (I : list (bv 8)) (a : nat) : pab I a = lm_ab pipe_lm pipe_hooks I a.
Proof using.
  rewrite /pab /lm_ab. case_decide as H1; case_decide as H2; [reflexivity | | | reflexivity].
  - exfalso. apply H2. split; [exact (proj1 H1) | exact (pfree_of_nofork _ (proj2 H1))].
  - exfalso. apply H1. split; [exact (proj1 H2) | exact (pfree_term _ (proj2 H2))].
Qed.

Lemma papr_lm (I : list (bv 8)) (a : nat) : papr I a <-> lm_apr pipe_lm pipe_hooks I a.
Proof using.
  split.
  - intros (H1 & H2 & H3). exact (conj H1 (conj (pfree_of_nofork _ H3) H2)).
  - intros (H1 & H2 & H3). exact (conj H1 (conj H3 (pfree_term _ H2))).
Qed.

Lemma rd_stage_p_lm ps0 cs0 I : rd_stage_p ps0 cs0 I <-> lm_rd_stage pipe_lm ps0 cs0 I.
Proof using.
  rewrite /rd_stage_p /lm_rd_stage.
  split; intros (H1 & H2 & H3 & H4);
    (split_and!; [exact H1 | exact H2 | by apply pro_pin_p_lm | exact H4]).
Qed.

(* ---- what section 0 said, as corollaries ---- *)
Lemma pab_ok (I : list (bv 8)) (a i : nat) (b : bv 8) :
  pab I a !! i = Some b -> palt_ok (pline_at I) (palt_of a).
Proof using.
  rewrite pab_lm. intros H. exact (proj1 (lm_ab_ok pipe_lm pipe_hooks I a i b H)).
Qed.

Lemma pab_nofork (I : list (bv 8)) (a i : nat) (b : bv 8) :
  pab I a !! i = Some b -> palt_isforkS (palt_of a) = false.
Proof using.
  rewrite pab_lm. intros H.
  exact (pfree_term _ (proj2 (lm_ab_ok pipe_lm pipe_hooks I a i b H))).
Qed.

Lemma pab_is (I : list (bv 8)) (a : nat) :
  pab_gd I a -> pab I a = pcont (pline_at I) (palt_of a).
Proof using.
  intros [H1 H2]. rewrite pab_lm.
  exact (lm_ab_is pipe_lm pipe_hooks I a H1 (pfree_of_nofork _ H2)).
Qed.

Lemma pab_len_ge2 (I : list (bv 8)) (a : nat) :
  papr I a -> (2 <= length (pab I a))%nat.
Proof using.
  rewrite pab_lm. intros Hpr.
  exact (lm_ab_len_ge2 pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma pab_dollar (I : list (bv 8)) (a : nat) :
  papr I a ->
  pab I a !! (length (pab I a) - 2)%nat = Some (u_prompt !!! 0%nat).
Proof using.
  rewrite pab_lm. intros Hpr.
  exact (lm_ab_dollar pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma pab_space (I : list (bv 8)) (a : nat) :
  papr I a ->
  pab I a !! (length (pab I a) - 1)%nat = Some (u_prompt !!! 1%nat).
Proof using.
  rewrite pab_lm. intros Hpr.
  exact (lm_ab_space pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma pab_pan (I : list (bv 8)) : pab I 3%nat = alt_panic.
Proof using.
  rewrite pab_lm. exact (lm_ab_pan pipe_lm pipe_lm_laws pipe_hooks I).
Qed.

Lemma pab_exf (I : list (bv 8)) :
  pab I (pexf_of (pline_at I)) = pexfb (pline_at I).
Proof using.
  rewrite pab_lm pline_at_lm. apply (lm_ab_exf pipe_lm pipe_hooks).
Qed.

Lemma papr_exf (I : list (bv 8)) : papr I (pexf_of (pline_at I)).
Proof using.
  apply papr_lm. apply (lm_apr_exf pipe_lm pipe_hooks).
Qed.

Lemma pab_noc (I : list (bv 8)) : pab I (pnoc_of (pline_at I)) = u_prompt.
Proof using.
  rewrite pab_lm pline_at_lm. apply (lm_ab_noc pipe_lm pipe_hooks).
Qed.

Lemma papr_noc (I : list (bv 8)) : papr I (pnoc_of (pline_at I)).
Proof using.
  apply papr_lm. apply (lm_apr_noc pipe_lm pipe_hooks).
Qed.

Lemma pab_noc_len (I : list (bv 8)) :
  (length (pab I (pnoc_of (pline_at I))) - 2)%nat = 0%nat.
Proof using.
  rewrite pab_lm pline_at_lm. apply (lm_ab_noc_len pipe_lm pipe_hooks).
Qed.


(* ===================================================================== *)
(*  S1  THE PURE SHAPES, AT THE PIPELINE MODEL                            *)
(*                                                                       *)
(*  [EchoLinks]'s [wr_pro] / [wr_blk] / [wr_open] / [wr_sp] / [wr_owed] / *)
(*  [wr_ban] and [EchoLinksLine]'s [wr_tail] / [wr_blk_t] / [wr_sp_t] /   *)
(*  [wr_open_t] / [blkcs] at [pro_pin_p], [proc_before_p],                *)
(*  [proc_stream_p] and [pro_idx_p].  Where echo tested                   *)
(*  [cs !!! (nlines I - 1) = 3] the pipeline tests                        *)
(*  [palt_panic (palt_at cs (nlines I - 1))] -- which is the SAME test    *)
(*  at either line shape, because [PEcho 3] is the only panicking         *)
(*  alternative and both shapes admit it.                                 *)
(* ===================================================================== *)

Definition wr_pro_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true)
  /\ ~ pro_done (pro_from (pro_idx_p cs (nlines I)) ps)
  /\ P = length (proc_stream_p ps cs I).

Definition wr_blk_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_p ps cs I).

Definition wr_open_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (pro_idx_p cs (nlines I) < pro_rounds ps)%nat
  /\ P = length (proc_stream_p ps cs I).

Definition wr_owed_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_pro_p ps cs I P \/ wr_blk_p ps cs I P.

Definition wr_sp_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_open_p ps cs I (S P)
  /\ proc_stream_p ps cs I !! P = Some (u_prompt !!! 1%nat).

Definition wr_pre_p (cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then [] else alt_panic.

Definition wr_ban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j
        /\ P = (length (proc_before_p ps cs I) + length (wr_pre_p cs I)
                + pro_round * j)%nat).

Definition wr_banp_p (ps cs : list nat) (I : list (bv 8)) (P i : nat) : Prop :=
  match i with
  | O => wr_ban_p ps cs I P
  | S _ => exists ps' : list nat, ps = ps' ++ [3%nat] /\ wr_ban_p ps' cs I P
  end.

(* the round this block is in is the LAST one resolved *)
Definition wr_tail_p (ps cs : list nat) : Prop :=
  pro_from (S (pro_idx_p cs (length cs))) ps = [].

Definition wr_blk_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_blk_p ps cs I P /\ wr_tail_p ps cs.

Definition wr_sp_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_sp_p ps cs I P /\ wr_tail_p ps cs.

Definition wr_open_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_open_p ps cs I P /\ wr_tail_p ps cs.

Definition blkcs_p (cs : list nat) (a i : nat) : list nat :=
  match i with O => cs | S _ => cs ++ [a] end.

(* ---- the writer's stages are [LineModel]'s, by the stream equations ---- *)
Lemma wr_pro_p_lm ps cs I P : wr_pro_p ps cs I P = lm_wr_pro pipe_lm ps cs tt I P.
Proof using. rewrite /wr_pro_p /lm_wr_pro ?proc_stream_p_lm ?proc_before_p_lm pro_idx_p_lm. reflexivity. Qed.
Lemma wr_blk_p_lm ps cs I P : wr_blk_p ps cs I P = lm_wr_blk pipe_lm ps cs tt I P.
Proof using. rewrite /wr_blk_p /lm_wr_blk ?proc_stream_p_lm ?proc_before_p_lm. reflexivity. Qed.
Lemma wr_open_p_lm ps cs I P : wr_open_p ps cs I P = lm_wr_open pipe_lm ps cs tt I P.
Proof using. rewrite /wr_open_p /lm_wr_open ?proc_stream_p_lm ?proc_before_p_lm pro_idx_p_lm. reflexivity. Qed.
Lemma wr_owed_p_lm ps cs I P : wr_owed_p ps cs I P = lm_wr_owed pipe_lm ps cs tt I P.
Proof using. rewrite /wr_owed_p /lm_wr_owed wr_pro_p_lm wr_blk_p_lm. reflexivity. Qed.
Lemma wr_sp_p_lm ps cs I P : wr_sp_p ps cs I P = lm_wr_sp pipe_lm ps cs tt I P.
Proof using. rewrite /wr_sp_p /lm_wr_sp wr_open_p_lm proc_stream_p_lm. reflexivity. Qed.
Lemma wr_ban_p_lm ps cs I P : wr_ban_p ps cs I P = lm_wr_ban pipe_lm ps cs tt I P.
Proof using. rewrite /wr_ban_p /lm_wr_ban ?proc_stream_p_lm ?proc_before_p_lm pro_idx_p_lm. reflexivity. Qed.
Lemma wr_banp_p_lm ps cs I P i : wr_banp_p ps cs I P i = lm_wr_banp pipe_lm ps cs tt I P i.
Proof using.
  rewrite /wr_banp_p /lm_wr_banp. destruct i; [apply wr_ban_p_lm |].
  f_equal. apply functional_extensionality. intros ps'. by rewrite wr_ban_p_lm.
Qed.
Lemma wr_tail_p_lm ps cs : wr_tail_p ps cs = lm_wr_tail pipe_lm ps cs.
Proof using. rewrite /wr_tail_p /lm_wr_tail pro_idx_p_lm. reflexivity. Qed.
Lemma wr_blk_t_p_lm ps cs I P : wr_blk_t_p ps cs I P = lm_wr_blk_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_blk_t_p /lm_wr_blk_t wr_blk_p_lm wr_tail_p_lm. reflexivity. Qed.
Lemma wr_sp_t_p_lm ps cs I P : wr_sp_t_p ps cs I P = lm_wr_sp_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_sp_t_p /lm_wr_sp_t wr_sp_p_lm wr_tail_p_lm. reflexivity. Qed.
Lemma wr_open_t_p_lm ps cs I P : wr_open_t_p ps cs I P = lm_wr_open_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_open_t_p /lm_wr_open_t wr_open_p_lm wr_tail_p_lm. reflexivity. Qed.

(* ---- what the shapes say about the input's parse ---- *)
Lemma wr_blk_nonnil_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> I <> [].
Proof using.
  rewrite wr_blk_p_lm. apply (lm_wr_blk_nonnil pipe_lm).
Qed.

Lemma wr_blk_lines_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> nlines I = S (length cs).
Proof using.
  rewrite wr_blk_p_lm. apply (lm_wr_blk_lines pipe_lm).
Qed.

Lemma wr_blk_started_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> nstarted I = S (length cs).
Proof using.
  rewrite wr_blk_p_lm. apply (lm_wr_blk_started pipe_lm).
Qed.

Lemma wr_blk_t_stage_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_t_p ps cs I P ->
  rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_p ps cs I)
  /\ pro_pin_p ps cs I
  /\ wr_tail_p ps cs.
Proof using.
  rewrite wr_blk_t_p_lm proc_before_p_lm wr_tail_p_lm. intros Hw.
  destruct (lm_wr_blk_t_stage pipe_lm ps cs tt I P Hw) as (H1 & H2 & H3 & H4 & H5).
  split_and!; [exact H1 | exact H2 | exact H3 | by apply pro_pin_p_lm | exact H5].
Qed.

(* ---- the round pointer under a filed alternative ---- *)
Lemma pro_idx_p_snoc_ne (cs : list nat) (a : nat) :
  palt_panic (palt_of a) = false ->
  pro_idx_p (cs ++ [a]) (S (length cs)) = pro_idx_p cs (length cs).
Proof using.
  rewrite !pro_idx_p_lm. apply (lm_pro_idx_snoc_ne pipe_lm).
Qed.

Lemma pro_idx_p_snoc_3 (cs : list nat) :
  pro_idx_p (cs ++ [3%nat]) (S (length cs)) = S (pro_idx_p cs (length cs)).
Proof using.
  rewrite !pro_idx_p_lm. apply (lm_pro_idx_snoc_pan pipe_lm). exact ppan_panic.
Qed.

Lemma wr_tail_snoc_p (ps cs : list nat) (a : nat) :
  palt_panic (palt_of a) = false -> wr_tail_p ps cs -> wr_tail_p ps (cs ++ [a]).
Proof using.
  rewrite !wr_tail_p_lm. apply (lm_wr_tail_snoc pipe_lm).
Qed.

(* ---- filing an alternative reads no block below the boundary ---- *)
Lemma wr_blk_pin_snoc_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> pro_pin_p ps (cs ++ [a]) I.
Proof using.
  rewrite wr_blk_p_lm. intros Hw. apply pro_pin_p_lm.
  exact (lm_wr_blk_pin_snoc pipe_lm ps cs tt I P a Hw).
Qed.

Lemma wr_blk_low_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> proc_before_p ps (cs ++ [a]) I = proc_before_p ps cs I.
Proof using.
  rewrite wr_blk_p_lm !proc_before_p_lm. apply (lm_wr_blk_low pipe_lm).
Qed.

(* ---- the block a [wr_blk_p] owes, once alternative [a] is filed ---- *)
Lemma wr_blk_pending_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P ->
  pending_at_p ps (cs ++ [a]) I
  = alt_cont_p ps (cs ++ [a]) (bodies_of I) (length cs).
Proof using.
  intros Hw. pose proof (wr_blk_nonnil_p ps cs I P Hw) as Hne.
  destruct Hw as (_ & Hr & Hn & _).
  rewrite /pending_at_p decide_False; [| exact Hne].
  rewrite decide_True; [| exact Hr].
  replace (nlines I - 1)%nat with (length cs) by lia.
  reflexivity.
Qed.

Lemma wr_blk_line_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> pline_of (bodies_of I !!! length cs) = pline_at I.
Proof using.
  intros Hw. pose proof (wr_blk_lines_p ps cs I P Hw) as Hn.
  rewrite /pline_at Hn.
  replace (S (length cs) - 1)%nat with (length cs) by lia. reflexivity.
Qed.

Lemma wr_blk_cont_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> palt_panic (palt_of a) = false ->
  pending_at_p ps (cs ++ [a]) I = pcont (pline_at I) (palt_of a).
Proof using.
  rewrite wr_blk_p_lm pending_at_p_lm pline_at_lm. apply (lm_wr_blk_pending_s pipe_lm).
Qed.

Lemma wr_blk_cont3_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> palt_panic (palt_of a) = true ->
  pending_at_p ps (cs ++ [a]) I
  = pcont (pline_at I) (palt_of a)
    ++ pro_of (pro_from (S (pro_idx_p cs (length cs))) ps).
Proof using.
  intros Hw Ha.
  rewrite (wr_blk_pending_p ps cs I P a Hw) /alt_cont_p /palt_at
          (EchoLinksLine.snoc_lookup_total cs a) Ha
          (pro_idx_p_app_le cs [a] (length cs) ltac:(lia))
          (wr_blk_line_p ps cs I P Hw).
  reflexivity.
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR *)
Lemma wr_blk_byte_p (ps cs : list nat) (I : list (bv 8)) (P a j : nat)
      (b : bv 8) :
  wr_blk_p ps cs I P -> pab I a !! j = Some b ->
  proc_stream_p ps (cs ++ [a]) I !! (P + j)%nat = Some b.
Proof using.
  intros Hw Hb. pose proof (pab_ok I a j b Hb) as Hok.
  pose proof (pab_nofork I a j b Hb) as Hfk.
  rewrite (pab_is I a (conj Hok Hfk)) in Hb.
  pose proof Hw as (_ & _ & _ & HP).
  rewrite /proc_stream_p (wr_blk_low_p ps cs I P a Hw) lookup_app_r; [| lia].
  replace (P + j - length (proc_before_p ps cs I))%nat with j by lia.
  destruct (palt_panic (palt_of a)) eqn:Ha.
  - rewrite (wr_blk_cont3_p ps cs I P a Hw Ha) lookup_app_l; [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  - by rewrite (wr_blk_cont_p ps cs I P a Hw Ha).
Qed.

(* ---- the prologue grows by exactly its alternative ---- *)
Lemma pending_at_p_round_snoc (ps cs : list nat) (I : list (bv 8)) (a : nat) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true) ->
  ~ pro_done (pro_from (pro_idx_p cs (nlines I)) ps) ->
  (pro_idx_p cs (nlines I) <= pro_rounds ps)%nat ->
  pending_at_p (ps ++ [a]) cs I = pending_at_p ps cs I ++ pro_alts !!! a.
Proof using.
  rewrite !pending_at_p_lm !pro_idx_p_lm.
  apply (lm_pending_at_round_snoc pipe_lm pipe_lm_laws).
Qed.

(* ---- THE ROUND'S BANNER, STILL OWED ---- *)
Lemma wr_ban_pro_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P -> wr_pro_p ps cs I P.
Proof using.
  rewrite wr_ban_p_lm wr_pro_p_lm. apply (lm_wr_ban_pro pipe_lm pipe_lm_laws).
Qed.

Lemma wr_ban_low_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P ->
  proc_before_p (ps ++ [3%nat]) cs I = proc_before_p ps cs I.
Proof using.
  rewrite wr_ban_p_lm !proc_before_p_lm. apply (lm_wr_ban_low pipe_lm).
Qed.

Lemma wr_ban_filed_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P ->
  exists j : nat,
    pro_from (pro_idx_p cs (nlines I)) (ps ++ [3%nat]) = pro_fail j ++ [3%nat]
    /\ P = (length (proc_before_p (ps ++ [3%nat]) cs I) + length (wr_pre_p cs I)
            + pro_round * j)%nat.
Proof using.
  rewrite wr_ban_p_lm proc_before_p_lm pro_idx_p_lm. intros Hw.
  destruct (lm_wr_ban_filed pipe_lm ps cs tt I P Hw) as (j & H1 & H2).
  exists j. exact (conj H1 H2).
Qed.

Lemma wr_ban_byte_p (ps cs : list nat) (I : list (bv 8)) (P i : nat)
      (b : bv 8) :
  wr_ban_p ps cs I P -> u_banner !! i = Some b ->
  proc_stream_p (ps ++ [3%nat]) cs I !! (P + i)%nat = Some b.
Proof using.
  rewrite wr_ban_p_lm proc_stream_p_lm. apply (lm_wr_ban_byte pipe_lm pipe_lm_laws).
Qed.

Lemma wr_ban_done_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P -> wr_pro_p (ps ++ [3%nat]) cs I (P + length u_banner)%nat.
Proof using.
  rewrite wr_ban_p_lm wr_pro_p_lm. apply (lm_wr_ban_done pipe_lm pipe_lm_laws).
Qed.

Lemma wr_ban_round0_p : wr_ban_p [] [] [] 0%nat.
Proof using.
  rewrite wr_ban_p_lm. apply (lm_wr_ban_round0 pipe_lm).
Qed.

(* ---- a run of inputs that owe nothing leaves the stream alone ---- *)
Lemma proc_before_from_p_gap (ps cs : list nat) (pre k : list (bv 8)) :
  (forall J : list (bv 8), J `prefix_of` k -> J <> k ->
     pending_at_p ps cs (pre ++ J) = []) ->
  proc_before_from_p ps cs pre k = [].
Proof using.
  rewrite proc_before_from_p_lm. intros Hj.
  apply (lm_proc_before_from_gap pipe_lm). intros J HJ Hne.
  rewrite -pending_at_p_lm. exact (Hj J HJ Hne).
Qed.

Lemma proc_before_p_line (ps cs : list nat) (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l ->
  proc_before_p ps cs (I ++ l ++ [wl_nl]) = proc_stream_p ps cs I.
Proof using.
  rewrite proc_before_p_lm proc_stream_p_lm. apply (lm_proc_before_line pipe_lm).
Qed.

(* ===================================================================== *)
(*  S2  THE STEPS, PURE                                                   *)
(* ===================================================================== *)

(* (1) THE ROUND'S CHOICE BYTE, at an open prologue *)
Lemma wr_pro_dollar_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro_p ps cs I P -> wr_sp_p (ps ++ [0%nat]) cs I (S P).
Proof using.
  rewrite wr_pro_p_lm wr_sp_p_lm. apply (lm_wr_pro_dollar pipe_lm pipe_lm_laws).
Qed.

(* (2) THE LINE'S CHOICE BYTE, at a settled round whose last line still
       owes its block: filing an alternative whose whole output IS the
       prompt makes the block the prompt itself, whatever the line was.
       Which code that is depends on the line ([PEcho 2] at an echo line,
       [PSilent] at a pipeline one), which is why the step is stated at an
       arbitrary such [c] and [wr_blk_dollar_p] is it at [pnoc_of]. *)
Lemma wr_blk_dollar_c_p (ps cs : list nat) (I : list (bv 8)) (P c : nat) :
  wr_blk_p ps cs I P -> palt_panic (palt_of c) = false ->
  pcont (pline_at I) (palt_of c) = u_prompt ->
  wr_sp_p ps (cs ++ [c]) I (S P).
Proof using.
  intros Hw Hnp Hpc. pose proof Hw as (Hpin & Hm & Hdv & HP).
  pose proof (wr_blk_started_p ps cs I P Hw) as Hst.
  assert (Hpend : pending_at_p ps (cs ++ [c]) I = u_prompt)
    by (rewrite (wr_blk_cont_p ps cs I P c Hw Hnp); exact Hpc).
  assert (Hup : proc_stream_p ps (cs ++ [c]) I
                = proc_before_p ps cs I ++ u_prompt)
    by (rewrite /proc_stream_p (wr_blk_low_p ps cs I P c Hw) Hpend; reflexivity).
  assert (Hlen : length (proc_stream_p ps (cs ++ [c]) I) = S (S P)).
  { rewrite Hup (length_app (proc_before_p ps cs I) u_prompt) wr_prompt_len.
    lia. }
  split.
  - rewrite /wr_open_p. split_and!.
    + exact (wr_blk_pin_snoc_p ps cs I P c Hw).
    + exact Hm.
    + rewrite (length_app cs [c]) Hdv. cbn [length]. lia.
    + rewrite Hdv (pro_idx_p_snoc_ne cs c Hnp). apply Hpin. lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (proc_before_p ps cs I))%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.

Lemma wr_blk_dollar_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P ->
  wr_sp_p ps (cs ++ [pnoc_of (pline_at I)]) I (S P).
Proof using.
  rewrite wr_blk_p_lm wr_sp_p_lm. apply (lm_wr_blk_dollar pipe_lm pipe_hooks).
Qed.

(* (3) THE SPACE *)
Lemma wr_sp_open_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_sp_p ps cs I P -> wr_open_p ps cs I (S P).
Proof using.
  rewrite wr_sp_p_lm wr_open_p_lm. apply (lm_wr_sp_open pipe_lm).
Qed.

(* (4) THE READ *)
Lemma wr_open_read_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
      (l : list (bv 8)) :
  wr_open_p ps cs I P -> wl_nl ∉ l -> wr_blk_p ps cs (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_p_lm wr_blk_p_lm. apply (lm_wr_open_read pipe_lm).
Qed.

(* ---- the tight shapes' steps ---- *)
Lemma wr_blk_open_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_t_p ps cs I P -> papr I a ->
  wr_open_t_p ps (cs ++ [a]) I (P + length (pab I a))%nat.
Proof using.
  rewrite wr_blk_t_p_lm wr_open_t_p_lm pab_lm. intros Hw Hpr.
  exact (lm_wr_blk_open pipe_lm pipe_hooks ps cs tt I P a Hw (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma wr_blk_sp_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_t_p ps cs I P -> papr I a ->
  wr_sp_t_p ps (cs ++ [a]) I (P + (length (pab I a) - 1))%nat.
Proof using.
  rewrite wr_blk_t_p_lm wr_sp_t_p_lm pab_lm. intros Hw Hpr.
  exact (lm_wr_blk_sp pipe_lm pipe_hooks ps cs tt I P a Hw (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma wr_sp_open_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_sp_t_p ps cs I P -> wr_open_t_p ps cs I (S P).
Proof using.
  rewrite wr_sp_t_p_lm wr_open_t_p_lm. apply (lm_wr_sp_open_t pipe_lm).
Qed.

Lemma wr_open_read_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
      (l : list (bv 8)) :
  wr_open_t_p ps cs I P -> wl_nl ∉ l ->
  wr_blk_t_p ps cs (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_t_p_lm wr_blk_t_p_lm. apply (lm_wr_open_read_t pipe_lm).
Qed.

Lemma wr_pro_tail_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro_p ps cs I P -> wr_tail_p (ps ++ [0%nat]) cs.
Proof using.
  rewrite wr_pro_p_lm wr_tail_p_lm. apply (lm_wr_pro_tail pipe_lm).
Qed.

Lemma wr_pro_dollar_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro_p ps cs I P -> wr_sp_t_p (ps ++ [0%nat]) cs I (S P).
Proof using.
  rewrite wr_pro_p_lm wr_sp_t_p_lm. apply (lm_wr_pro_dollar_t pipe_lm pipe_lm_laws).
Qed.

(* (5) THE PANIC LINE OPENS A FRESH ROUND AT THE SAME INPUT *)
Lemma wr_blk_ban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_t_p ps cs I P ->
  wr_ban_p ps (cs ++ [3%nat]) I (P + length (pab I 3%nat))%nat.
Proof using.
  rewrite wr_blk_t_p_lm wr_ban_p_lm pab_lm.
  apply (lm_wr_blk_ban pipe_lm pipe_lm_laws pipe_hooks).
Qed.


(* ===================================================================== *)
(*  S3  THE DISCIPLINE LEMMA: an untainted input past a boundary means    *)
(*  the boundary's prompt was written ([EchoLinks.wr_owed_read_refute]    *)
(*  at the pipeline stage; the block's nonemptiness comes from            *)
(*  [PipeOutPure.pending_at_p_nonnil_pre], which is the reading of        *)
(*  [alts_pre_p] a WRITER's lower bound admits).                          *)
(* ===================================================================== *)
Lemma wr_owed_read_refute_p (ps cs ps0 cs0 : list nat) (I I0 : list (bv 8))
      (P : nat) :
  wr_owed_p ps cs I P ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage_p ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
  (length (proc_before_p ps0 cs0 I0) <= P)%nat -> False.
Proof using.
  rewrite wr_owed_p_lm proc_before_p_lm. intros Hw HI Hne Hrs.
  exact (lm_wr_owed_read_refute pipe_lm pipe_lm_laws pipe_hooks ps cs ps0 cs0 tt I I0 P
           Hw HI Hne (proj1 (rd_stage_p_lm _ _ _) Hrs)).
Qed.


(* ===================================================================== *)
(*  S4  /INIT'S PROLOGUE DIAGNOSTICS, PURE ([EchoLinksPro] at the         *)
(*  pipeline stage).  Nothing here reads a line: the prologue's           *)
(*  alternatives are [EchoDisc.pro_alts] at either application.           *)
(* ===================================================================== *)
Lemma pending_at_p_round_wr_pre (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true) ->
  pending_at_p ps cs I
  = wr_pre_p cs I ++ pro_of (pro_from (pro_idx_p cs (nlines I)) ps).
Proof using.
  rewrite pending_at_p_lm pro_idx_p_lm.
  apply (lm_pending_at_round_pre pipe_lm pipe_lm_laws).
Qed.

Definition wr_pban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_pro_p ps cs I P
  /\ (exists j : nat,
        pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j ++ [3%nat]).
Lemma wr_pban_p_lm ps cs I P : wr_pban_p ps cs I P = lm_wr_pban pipe_lm ps cs tt I P.
Proof using. rewrite /wr_pban_p /lm_wr_pban wr_pro_p_lm pro_idx_p_lm. reflexivity. Qed.

Lemma wr_pban_of_ban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P ->
  wr_pban_p (ps ++ [3%nat]) cs I (P + length u_banner)%nat.
Proof using.
  rewrite wr_ban_p_lm wr_pban_p_lm. apply (lm_wr_pban_of_ban pipe_lm pipe_lm_laws).
Qed.

Definition wr_pdiag_p (ps cs : list nat) (I : list (bv 8)) (P a i : nat)
  : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j ++ [3%nat; a]
        /\ P = (length (proc_before_p ps cs I) + length (wr_pre_p cs I)
                + pro_round * j + length u_banner + i)%nat).
Lemma wr_pdiag_p_lm ps cs I P a i : wr_pdiag_p ps cs I P a i = lm_wr_pdiag pipe_lm ps cs tt I P a i.
Proof using. rewrite /wr_pdiag_p /lm_wr_pdiag proc_before_p_lm !pro_idx_p_lm. reflexivity. Qed.

Lemma wr_pdiag_byte_p (ps cs : list nat) (I : list (bv 8)) (P a i : nat)
      (b : bv 8) :
  wr_pdiag_p ps cs I P a i -> pro_alts !!! a !! i = Some b ->
  proc_stream_p ps cs I !! P = Some b.
Proof using.
  intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)) Hb.
  rewrite /proc_stream_p (pending_at_p_round_wr_pre ps cs I Hm Hr) Hj
          EchoLinksPro.pro_of_fail_snoc HP.
  replace (length (proc_before_p ps cs I) + length (wr_pre_p cs I)
           + pro_round * j + length u_banner + i)%nat
    with (length (proc_before_p ps cs I)
          + (length (wr_pre_p cs I)
             + (length (pro_of (pro_fail j)) + (length u_banner + i))))%nat
    by (rewrite pro_of_fail_length; lia).
  rewrite (lookup_app_shift (proc_before_p ps cs I))
          (lookup_app_shift (wr_pre_p cs I))
          (lookup_app_shift (pro_of (pro_fail j))) (lookup_app_shift u_banner).
  exact Hb.
Qed.

Lemma wr_pdiag_1_of_pro_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_pban_p ps cs I P -> wr_pdiag_p (ps ++ [a]) cs I (S P) a 1%nat.
Proof using.
  intros ((Hpin & Hm & Hdv & Hr & Hnd & HP) & (j & Hj)).
  assert (Hle : (pro_idx_p cs (nlines I) <= pro_rounds ps)%nat)
    by exact (pro_pin_p_round_le ps cs I Hm Hr Hpin).
  assert (Hpre : ps `prefix_of` (ps ++ [a])) by by eexists.
  assert (Hlow : proc_before_p (ps ++ [a]) cs I = proc_before_p ps cs I).
  { symmetry. apply proc_before_p_ext. intros J HJ Hne.
    apply (pending_at_p_ps_ext ps (ps ++ [a]) cs J Hpre).
    exact (Hpin (nlines J) (nstarted_strict J I HJ Hne)). }
  assert (H3 : length (pro_of (pro_fail j ++ [3%nat]))
               = (pro_round * j + length u_banner)%nat).
  { rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
    rewrite length_app pro_of_fail_length. reflexivity. }
  rewrite /wr_pdiag_p. split_and!.
  - exact (pro_pin_p_mono ps (ps ++ [a]) cs I Hpre Hpin).
  - exact Hm.
  - exact Hdv.
  - exact Hr.
  - exists j. split.
    + rewrite (pro_from_snoc_le _ ps a Hle) Hj. by rewrite -app_assoc.
    + rewrite Hlow HP /proc_stream_p (length_app (proc_before_p ps cs I))
              (pending_at_p_round_wr_pre ps cs I Hm Hr)
              (length_app (wr_pre_p cs I)) Hj H3. lia.
Qed.

Lemma wr_pdiag_S_p (ps cs : list nat) (I : list (bv 8)) (P a i : nat) :
  wr_pdiag_p ps cs I P a i -> wr_pdiag_p ps cs I (S P) a (S i).
Proof using.
  rewrite !wr_pdiag_p_lm. apply (lm_wr_pdiag_S pipe_lm).
Qed.

Lemma wr_pdiag_done_1_p (ps cs : list nat) (I : list (bv 8)) (P i : nat) :
  i = length (pro_alts !!! 1%nat) ->
  wr_pdiag_p ps cs I P 1%nat i -> wr_ban_p ps cs I P.
Proof using.
  intros Hi (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
  assert (Hb : length u_banner = 18%nat) by (vm_compute; reflexivity).
  assert (Ha : length (pro_alts !!! 1%nat) = 21%nat)
    by (vm_compute; reflexivity).
  assert (Hrd : pro_round = 39%nat) by (vm_compute; reflexivity).
  rewrite /wr_ban_p. split_and!; try assumption.
  exists (S j). split.
  - rewrite Hj. by rewrite pro_fail_S.
  - rewrite HP Hi Hb Ha Hrd. lia.
Qed.


(* ===================================================================== *)
(*  S5  THE CREDENTIAL FAMILIES AS RESOURCES                              *)
(*                                                                       *)
(*  Every family takes the ERA INDEX [k] first, so that it fills a        *)
(*  [LinkRec] field by name; none of them READS it (the pipeline era has  *)
(*  no per-index state -- the era's pin carries the index already).       *)
(* ===================================================================== *)
Section pipe_links_line.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).

  Definition pwc_pro (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pro_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_blk (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_blk_t_p ps cs I P⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v (blkcs_p cs a i) ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_owed (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_owed_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_sp (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_sp_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_open (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_open_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_sp_t (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_sp_t_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_open_t (k : nat) (v : era_pins) (I : list (bv 8))
    : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_open_t_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_ban (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
    : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_banp_p ps cs I P i⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  (* the block written up to its prompt *)
  Definition pwc_post (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat)
    : iProp Σ := pwc_blk k v I a (length (pab I a) - 2)%nat.

  (* THE LOOP'S BOUNDARY CREDENTIAL, WIDENED *)
  Definition pwc_line (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (pwc_pro k v I ∨ (∃ a : nat, ⌜papr I a⌝ ∗ pwc_post k v I a))%I.

  (* WHAT sh's FORK HANDS ITS CHILD: [pwc_blk _ _ _ _ 0] opened *)
  Definition pwc_lend (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_blk_t_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_pr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => pwc_owed k v I
    | S O => pwc_sp k v I
    | _ => pwc_open k v I
    end.

  Definition pwc_lpr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => pwc_line k v I
    | S O => pwc_sp_t k v I
    | S (S O) => pwc_open_t k v I
    | _ => pwc_blk k v I 0%nat 0%nat
    end.

  (* THE READER'S RESIDUE ([UShLine.rd_res] at the pipeline stage) *)
  Definition pwc_rres (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage_p ps0 cs0 I⌝ ∗ turn_lb v (length (proc_before_p ps0 cs0 I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0)%I.

  (* THE ERA'S TURN: [PipeOut.pturn], which is [EchoOut.eturn] verbatim *)
  Definition pturn_pre (k : nat) : iProp Σ := PipeOut.pturn g k.

  (* ---- structure ----

     THE DISPATCH, NOT [apply _] (upstream's leaf-instance pass, 2026-09-18:
     the tree carries 455 [Timeless] instances under mostly transparent
     definitions, so the hint net cannot discriminate and one search at
     this altitude tries nearly all of them).  Descend through the
     CONNECTIVES and name the leaf, SYNTACTICALLY -- a [first [...]]
     spelling unifies up to delta and peels through a name that has its
     own instance. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (echo_taint _) => apply echo_taint_timeless
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (era_pin _ _ _) => apply era_pin_timeless
    | |- _ => apply _
    end.

  Local Ltac ps_leaf :=
    lazymatch goal with
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; ps_leaf
    | |- Persistent (bi_sep _ _) =>
        apply bi.sep_persistent; [ps_leaf | ps_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- _ => apply _
    end.

  Global Instance pwc_pro_timeless k v I : Timeless (pwc_pro k v I).
  Proof using . rewrite /pwc_pro. tl_leaf. Qed.
  Global Instance pwc_blk_timeless k v I a i : Timeless (pwc_blk k v I a i).
  Proof using . rewrite /pwc_blk. tl_leaf. Qed.
  Global Instance pwc_owed_timeless k v I : Timeless (pwc_owed k v I).
  Proof using . rewrite /pwc_owed. tl_leaf. Qed.
  Global Instance pwc_sp_timeless k v I : Timeless (pwc_sp k v I).
  Proof using . rewrite /pwc_sp. tl_leaf. Qed.
  Global Instance pwc_open_timeless k v I : Timeless (pwc_open k v I).
  Proof using . rewrite /pwc_open. tl_leaf. Qed.
  Global Instance pwc_sp_t_timeless k v I : Timeless (pwc_sp_t k v I).
  Proof using . rewrite /pwc_sp_t. tl_leaf. Qed.
  Global Instance pwc_open_t_timeless k v I : Timeless (pwc_open_t k v I).
  Proof using . rewrite /pwc_open_t. tl_leaf. Qed.
  Global Instance pwc_ban_timeless k v I i : Timeless (pwc_ban k v I i).
  Proof using . rewrite /pwc_ban. tl_leaf. Qed.
  Global Instance pwc_post_timeless k v I a : Timeless (pwc_post k v I a).
  Proof using . rewrite /pwc_post. apply pwc_blk_timeless. Qed.
  Global Instance pwc_line_timeless k v I : Timeless (pwc_line k v I).
  Proof using .
    rewrite /pwc_line.
    apply bi.or_timeless; [apply pwc_pro_timeless |].
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply pwc_post_timeless].
  Qed.
  Global Instance pwc_lend_timeless k v I : Timeless (pwc_lend k v I).
  Proof using . rewrite /pwc_lend. tl_leaf. Qed.
  Global Instance pwc_pr_timeless k v I p : Timeless (pwc_pr k v I p).
  Proof using .
    rewrite /pwc_pr. destruct p as [| [| p]];
      [apply pwc_owed_timeless | apply pwc_sp_timeless
      | apply pwc_open_timeless].
  Qed.
  Global Instance pwc_lpr_timeless k v I p : Timeless (pwc_lpr k v I p).
  Proof using .
    rewrite /pwc_lpr. destruct p as [| [| [| p]]];
      [apply pwc_line_timeless | apply pwc_sp_t_timeless
      | apply pwc_open_t_timeless | apply pwc_blk_timeless].
  Qed.
  Global Instance pwc_rres_persistent v I : Persistent (pwc_rres v I).
  Proof using . rewrite /pwc_rres. ps_leaf. Qed.
  Global Instance pwc_rres_timeless v I : Timeless (pwc_rres v I).
  Proof using . rewrite /pwc_rres. tl_leaf. Qed.

  (* ---- the taint inhabits every shape ---- *)
  Lemma pwc_pro_taint k v I : PT -∗ pwc_pro k v I.
  Proof using . iIntros "HT". rewrite /pwc_pro. by iRight. Qed.
  Lemma pwc_blk_taint k v I a i : PT -∗ pwc_blk k v I a i.
  Proof using . iIntros "HT". rewrite /pwc_blk. by iRight. Qed.
  Lemma pwc_owed_taint k v I : PT -∗ pwc_owed k v I.
  Proof using . iIntros "HT". rewrite /pwc_owed. by iRight. Qed.
  Lemma pwc_sp_taint k v I : PT -∗ pwc_sp k v I.
  Proof using . iIntros "HT". rewrite /pwc_sp. by iRight. Qed.
  Lemma pwc_open_taint k v I : PT -∗ pwc_open k v I.
  Proof using . iIntros "HT". rewrite /pwc_open. by iRight. Qed.
  Lemma pwc_sp_t_taint k v I : PT -∗ pwc_sp_t k v I.
  Proof using . iIntros "HT". rewrite /pwc_sp_t. by iRight. Qed.
  Lemma pwc_open_t_taint k v I : PT -∗ pwc_open_t k v I.
  Proof using . iIntros "HT". rewrite /pwc_open_t. by iRight. Qed.
  Lemma pwc_ban_taint k v I i : PT -∗ pwc_ban k v I i.
  Proof using . iIntros "HT". rewrite /pwc_ban. by iRight. Qed.
  Lemma pwc_lend_taint k v I : PT -∗ pwc_lend k v I.
  Proof using . iIntros "HT". rewrite /pwc_lend. by iRight. Qed.
  Lemma pwc_line_taint k v I : PT -∗ pwc_line k v I.
  Proof using .
    iIntros "HT". rewrite /pwc_line. iLeft. by iApply pwc_pro_taint.
  Qed.

  (* ---- the loose shapes and the tight ones ---- *)
  Lemma pwc_pro_owed k v I : pwc_pro k v I -∗ pwc_owed k v I.
  Proof using .
    rewrite /pwc_pro /pwc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. by left.
  Qed.

  Lemma pwc_blk_owed k v I a : pwc_blk k v I a 0%nat -∗ pwc_owed k v I.
  Proof using .
    rewrite /pwc_blk /pwc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    cbn [blkcs_p]. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. right.
    exact (proj1 Hw).
  Qed.

  Lemma pwc_sp_t_sp k v I : pwc_sp_t k v I -∗ pwc_sp k v I.
  Proof using .
    rewrite /pwc_sp_t /pwc_sp. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (proj1 Hw).
  Qed.

  Lemma pwc_open_t_open k v I : pwc_open_t k v I -∗ pwc_open k v I.
  Proof using .
    rewrite /pwc_open_t /pwc_open. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (proj1 Hw).
  Qed.

  Lemma pwc_blk_0 k v I a a' :
    pwc_blk k v I a 0%nat -∗ pwc_blk k v I a' 0%nat.
  Proof using . rewrite /pwc_blk. cbn [blkcs_p]. iIntros "H". iExact "H". Qed.

  Lemma pwc_line_of_post k v I a :
    papr I a -> pwc_post k v I a -∗ pwc_line k v I.
  Proof using .
    intros Ha. iIntros "Hc". rewrite /pwc_line. iRight. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma pwc_line_of_pro k v I : pwc_pro k v I -∗ pwc_line k v I.
  Proof using . iIntros "Hc". rewrite /pwc_line. by iLeft. Qed.

  Lemma pwc_line_of_blk0 k v I a : pwc_blk k v I a 0%nat -∗ pwc_line k v I.
  Proof using .
    iIntros "Hc".
    iApply (pwc_line_of_post k v I (pnoc_of (pline_at I)) (papr_noc I)).
    rewrite /pwc_post (pab_noc_len I). iApply (pwc_blk_0 with "Hc").
  Qed.

  Lemma pwc_lend_of_blk0 k v I a : pwc_blk k v I a 0%nat -∗ pwc_lend k v I.
  Proof using .
    rewrite /pwc_blk /pwc_lend. cbn [blkcs_p]. iIntros "[Hl | #HT]";
      last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    rewrite Nat.add_0_r. iLeft. iExists ps, cs, P.
    iFrame "Htn Hps Hcs HE". by iPureIntro.
  Qed.

  (* ---- the banner's conversions ---- *)
  Lemma pwc_ban_pro k v I : pwc_ban k v I 0%nat -∗ pwc_pro k v I.
  Proof using .
    rewrite /pwc_ban /pwc_pro. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    cbn [wr_banp_p] in Hw. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (wr_ban_pro_p ps cs I P Hw).
  Qed.

  Lemma pwc_ban_owed k v I : pwc_ban k v I 0%nat -∗ pwc_owed k v I.
  Proof using .
    iIntros "Hc". iApply pwc_pro_owed. iApply (pwc_ban_pro with "Hc").
  Qed.

  Lemma pwc_ban_done k v I :
    pwc_ban k v I (length u_banner) -∗ pwc_owed k v I.
  Proof using .
    rewrite /pwc_ban /pwc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18 in Hw. cbn [wr_banp_p] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. left.
    exact (wr_ban_done_p ps' cs I P Hw).
  Qed.

  Lemma pwc_ban_done_line k v I :
    pwc_ban k v I (length u_banner) -∗ pwc_line k v I.
  Proof using .
    rewrite /pwc_ban. iIntros "[Hl | #HT]"; last by iApply pwc_line_taint.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18 in Hw. cbn [wr_banp_p] in Hw. destruct Hw as (ps' & -> & Hw).
    iApply pwc_line_of_pro. rewrite /pwc_pro.
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_ban_done_p ps' cs I P Hw).
  Qed.

  Lemma pwc_ban_inp k v I :
    pwc_ban k v I 0%nat -∗
    pwc_ban k v I 0%nat ∗ ((inp_lb v I ∗ ⌜rest_of I = []⌝) ∨ PT).
  Proof using .
    rewrite /pwc_ban. iIntros "[Hl | #HT]"; last first.
    { iSplit; [by iRight | iRight; iExact "HT"]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    cbn [wr_banp_p] in Hw. iSplitL "Htn".
    - iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". by iPureIntro.
    - iLeft. iFrame "HE". iPureIntro. exact (proj1 (proj2 Hw)).
  Qed.

  (* =================================================================== *)
  (*  S6  THE STEPS, THROUGH THE ERA'S LINKS                              *)
  (* =================================================================== *)
  Lemma pban_step (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    u_banner !! i = Some b ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_ban k v I i -∗
    (pwc_ban k v I (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (pipe_links_w with "Hlk") as "#Hw".
    iDestruct (pipe_links_pro with "Hlk") as "#Hpro".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /pwc_ban. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct i as [| i].
    - cbn [wr_banp_p] in Hw.
      pose proof (wr_ban_pro_p ps cs I P Hw) as Hpr.
      pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
      destruct Hpr as (_ & _ & _ & _ & Hnd & HP).
      rewrite Nat.add_0_r.
      iApply ("Hpro" $! k v P 3%nat b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [3%nat]), cs, P.
      replace (P + 1)%nat with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE'". iPureIntro. cbn [wr_banp_p]. by exists ps.
    - cbn [wr_banp_p] in Hw. destruct Hw as (ps' & -> & Hw).
      pose proof (wr_ban_byte_p ps' cs I P (S i) b Hw Hb) as Hby.
      pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v (P + S i)%nat b (ps' ++ [3%nat]) cs I Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { lia. }
      { exact (pro_pin_p_mono ps' (ps' ++ [3%nat]) cs I ltac:(by eexists)
                 Hpin). }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps' ++ [3%nat]), cs, P.
      replace (P + S (S i))%nat with (S (P + S i))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". iPureIntro. cbn [wr_banp_p]. by exists ps'.
  Qed.

  (* ONE BYTE OF THE BLOCK: the first FILES the alternative, the rest are
     ordinary bytes of the block the choice fixed.  No admissibility
     premise: [pab I a !! i = Some b] carries it ([pab_ok]). *)
  Lemma pblk_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    pab I a !! i = Some b ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_blk k v I a i -∗
    (pwc_blk k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (pipe_links_w with "Hlk") as "#Hw".
    iDestruct (pipe_links_blk with "Hlk") as "#Hblk".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    pose proof (pab_ok I a i b Hb) as Hok.
    pose proof (pab_nofork I a i b Hb) as Hfk.
    rewrite /pwc_blk. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (proj1 Hw) as Hwb. pose proof Hwb as (Hpin & Hr & Hn & HP).
    pose proof (wr_blk_nonnil_p ps cs I P Hwb) as Hne.
    destruct i as [| i'].
    - (* THE BLOCK-FIRST BYTE files the alternative *)
      cbn [blkcs_p]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v P a b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hne. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact HP. }
      { exact Hok. }
      { exact Hfk. }
      { rewrite (pab_is I a (conj Hok Hfk)) in Hb. exact Hb. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs_p]. rewrite Nat.add_1_r.
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
    - (* every byte after it, at the choice list the first one extended *)
      cbn [blkcs_p].
      iApply ("Hw" $! k v (P + S i')%nat b ps (cs ++ [a]) I Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { rewrite (length_app cs [a]) Hn. cbn [length]. lia. }
      { exact (wr_blk_pin_snoc_p ps cs I P a Hwb). }
      { exact (wr_blk_byte_p ps cs I P a (S i') b Hwb Hb). }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs_p].
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
  Qed.

  Lemma pwc_blk_sp k v I a :
    papr I a ->
    pwc_blk k v I a (length (pab I a) - 1)%nat -∗ pwc_sp_t k v I.
  Proof using .
    intros Ha. rewrite /pwc_blk /pwc_sp_t. iIntros "[Hl | #HT]";
      last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (pab_len_ge2 I a Ha) as Hlen.
    assert (Hbc : blkcs_p cs a (length (pab I a) - 1) = cs ++ [a]).
    { destruct (length (pab I a) - 1)%nat as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]), (P + (length (pab I a) - 1))%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_blk_sp_p ps cs I P a Hw Ha).
  Qed.

  (* ---- the shell's prompt, at the loose shapes ---- *)
  Lemma pprompt_dollar (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_owed k v I -∗
    (pwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (pipe_links_blk with "Hlk") as "#Hblk".
    iDestruct (pipe_links_pro with "Hlk") as "#Hpro".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /pwc_owed. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /pwc_sp. by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hhd : pro_alts !!! 0%nat !! 0%nat = Some b)
      by (rewrite EchoLinks.wr_pro_alts_0 Hb; exact wr_prompt_head).
    assert (Hhd2 : pcont (pline_at I) (palt_of (pnoc_of (pline_at I)))
                     !! 0%nat = Some b)
      by (rewrite (pcont_pnoc (pline_at I)) Hb; exact wr_prompt_head).
    destruct Hw as [Hw | Hw].
    - (* the round's prologue is open: the '$' files alternative 0 *)
      pose proof (wr_pro_dollar_p ps cs I P Hw) as Hsp.
      destruct Hw as (Hpin & Hm & Hdv & Hr & Hnd & HP).
      iApply ("Hpro" $! k v P 0%nat b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { rewrite pro_alts_length. lia. }
      { exact Hhd. }
      iIntros "Hres". iApply "HΦ". rewrite /pwc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [0%nat]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
    - (* the round is settled: the '$' is the line's block, nobody chose *)
      pose proof (wr_blk_dollar_p ps cs I P Hw) as Hsp.
      pose proof (wr_blk_nonnil_p ps cs I P Hw) as Hne.
      destruct Hw as (Hpin & Hm & Hdv & HP).
      iApply ("Hblk" $! k v P (pnoc_of (pline_at I)) b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hne. }
      { exact Hm. }
      { lia. }
      { exact Hpin. }
      { exact HP. }
      { exact (pnoc_of_ok (pline_at I)). }
      { exact (pnoc_of_nofork (pline_at I)). }
      { exact Hhd2. }
      iIntros "Hres". iApply "HΦ". rewrite /pwc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, (cs ++ [pnoc_of (pline_at I)]), (S P).
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
  Qed.

  Lemma pprompt_space (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_sp k v I -∗
    (pwc_open k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (pipe_links_w with "Hlk") as "#Hw".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /pwc_sp. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /pwc_open. by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [Hop Hby].
    pose proof Hop as (Hpin & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v P b ps cs I Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /pwc_open.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    by iPureIntro.
  Qed.

  Lemma pprompt_dollar_ban (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_ban k v I 0%nat -∗
    (pwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (pprompt_dollar k v I b Φ Hb with "Hpin Hlk [Hc] HΦ").
    by iApply pwc_ban_owed.
  Qed.

  (* ---- the read ---- *)
  Lemma pwc_read k v I l :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ pwc_open k v I -∗
    pwc_owed k v (I ++ l ++ [wl_nl]).
  Proof using .
    intros Hl. iIntros "#HE' Hc". rewrite /pwc_open /pwc_owed.
    iDestruct "Hc" as "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE'".
    iPureIntro. right. exact (wr_open_read_p ps cs I P l Hw Hl).
  Qed.

  Lemma pwc_read_t k v I a l :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ pwc_open_t k v I -∗
    pwc_blk k v (I ++ l ++ [wl_nl]) a 0%nat.
  Proof using .
    intros Hl. iIntros "#HE' Hc". rewrite /pwc_open_t /pwc_blk.
    iDestruct "Hc" as "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. cbn [blkcs_p]. rewrite Nat.add_0_r.
    iFrame "Htn Hps Hcs HE'". iPureIntro.
    exact (wr_open_read_t_p ps cs I P l Hw Hl).
  Qed.

  (* ---- the shell's prompt, at the tight shapes ---- *)
  Lemma pprompt_dollar_post (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) (b : bv 8) (Φ : iProp Σ) :
    papr I a -> b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_post k v I a -∗
    (pwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Ha Hb. iIntros "#Hpin #Hlk Hc HΦ".
    pose proof (pab_len_ge2 I a Ha) as Hlen.
    assert (Hby : pab I a !! (length (pab I a) - 2)%nat = Some b)
      by (rewrite Hb; exact (pab_dollar I a Ha)).
    iApply (pblk_step k v I a (length (pab I a) - 2)%nat b Φ Hby
              with "Hpin Hlk Hc [HΦ]").
    iIntros "Hc". iApply "HΦ".
    replace (S (length (pab I a) - 2))%nat
      with (length (pab I a) - 1)%nat by lia.
    iApply (pwc_blk_sp k v I a Ha with "Hc").
  Qed.

  Lemma pprompt_space_t (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_sp_t k v I -∗
    (pwc_open_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (pipe_links_w with "Hlk") as "#Hw".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /pwc_sp_t. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_open_t_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [[Hop Hby] Ht].
    pose proof Hop as (Hpin & Hr & Hn & Hrd & HP).
    iApply ("Hw" $! k v P b ps cs I Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /pwc_open_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    iPureIntro. exact (wr_sp_open_t_p ps cs I P (conj (conj Hop Hby) Ht)).
  Qed.

  Lemma pprompt_dollar_line (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_line k v I -∗
    (pwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    rewrite /pwc_line. iDestruct "Hc" as "[Hc | Hc]"; last first.
    { iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (pprompt_dollar_post k v I a b Φ Ha Hb with "Hpin Hlk Hc HΦ"). }
    iDestruct (pipe_links_pro with "Hlk") as "#Hpro".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /pwc_pro. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_sp_t_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hhd : pro_alts !!! 0%nat !! 0%nat = Some b)
      by (rewrite EchoLinks.wr_pro_alts_0 Hb; exact wr_prompt_head).
    pose proof (wr_pro_dollar_t_p ps cs I P Hw) as Hsp.
    destruct Hw as (Hpin & Hr & Hn & Hopen & Hnd & HP).
    iApply ("Hpro" $! k v P 0%nat b ps cs I Φ
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { exact Hr. }
    { exact Hopen. }
    { lia. }
    { exact Hpin. }
    { exact Hnd. }
    { exact HP. }
    { rewrite pro_alts_length. lia. }
    { exact Hhd. }
    iIntros "Hres". iApply "HΦ". rewrite /pwc_sp_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists (ps ++ [0%nat]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    by iPureIntro.
  Qed.

  (* ---- the panic's end: the next round's banner is owed ---- *)
  Lemma pwc_panic_done k v I :
    pwc_blk k v I 3%nat (length (pab I 3%nat)) -∗ pwc_ban k v I 0%nat.
  Proof using .
    rewrite /pwc_blk /pwc_ban. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hbc : blkcs_p cs 3%nat (length (pab I 3%nat)) = cs ++ [3%nat]).
    { destruct (length (pab I 3%nat)) as [| kk] eqn:Hk; [| reflexivity].
      exfalso. rewrite pab_pan lb_panic_len in Hk. discriminate. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [3%nat]), (P + length (pab I 3%nat))%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (wr_blk_ban_p ps cs I P Hw).
  Qed.

  (* ---- the discipline lemma, as the shell spends it ---- *)
  Lemma powed_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    pwc_owed k v I -∗ pread_ret g k v n ws -∗ PT.
  Proof using .
    intros HIn Hws. iIntros "Hc Hr".
    rewrite /pwc_owed. iDestruct "Hc" as "[Hl | #HT]"; last by iExact "HT".
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    rewrite /pread_ret. iDestruct "Hr" as "[[#HT Hdl] | [Hdlr Hfacts]]";
      [by iExact "HT" |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0) "(#Hcs0 & #Hps0 & %Hbd & #Htlb & %Hrs)".
    iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
    iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
    iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
    iDestruct (inp_lb_cmp with "HE Hinp") as %Hic.
    iExFalso. iPureIntro.
    assert (Hlen : length (snd <$> (dl ++ ws)) = (n + length ws)%nat).
    { by rewrite length_fmap length_app Hdl. }
    assert (HI : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hic as [Hc | Hc]; [exact Hc |].
      exfalso. apply prefix_length in Hc. lia. }
    assert (Hne : I <> (snd <$> (dl ++ ws)))
      by (intros Hq; rewrite Hq Hlen in HIn; lia).
    exact (wr_owed_read_refute_p ps cs ps0 cs0 I (snd <$> (dl ++ ws)) P Hw
             HI Hne Hrs Hpsc Hcsc Hle).
  Qed.

  Lemma pban_read_taint (k : nat) (v : era_pins) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    pwc_ban k v I 0%nat -∗ pwc_rres v (I ++ l ++ [wl_nl]) -∗ PT.
  Proof using .
    intro Hnl. iIntros "Hb #Hres".
    rewrite /pwc_ban. iDestruct "Hb" as "[Hl | #HT]"; [| iExact "HT"].
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & _)".
    cbn [wr_banp_p] in Hw. rewrite Nat.add_0_r.
    rewrite /pwc_rres.
    iDestruct "Hres" as (ps0 cs0) "(%Hrd & #Htlb & #Hps0 & #Hcs0)".
    iDestruct (turn_lb_le v P _ with "Htn Htlb") as %Hle.
    iDestruct (ps_lb_cmp v ps ps0 with "Hps Hps0") as %Hpsc.
    iDestruct (cs_lb_cmp v cs cs0 with "Hcs Hcs0") as %Hcsc.
    iExFalso. iPureIntro.
    assert (Hpre : I `prefix_of` (I ++ l ++ [wl_nl])) by (by eexists).
    assert (Hne : I <> I ++ l ++ [wl_nl]).
    { intro Heq. apply (f_equal length) in Heq.
      rewrite !length_app length_cons in Heq. lia. }
    exact (wr_owed_read_refute_p ps cs ps0 cs0 I (I ++ l ++ [wl_nl]) P
             (or_introl (wr_ban_pro_p ps cs I P Hw))
             Hpre Hne Hrd Hpsc Hcsc Hle).
  Qed.

  (* ---- the era's turn comes apart ---- *)
  Lemma pturn0 (k : nat) :
    pturn_pre k -∗
    (∃ v : era_pins, era_pin γ k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, era_pin γ k v ∗ pwc_ban k v [] 0%nat).
  Proof using .
    rewrite /pturn_pre /PipeOut.pturn /eturn. iIntros "Hturn".
    iDestruct "Hturn" as (v) "(#Hpin & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" | ].
    iExists v. iFrame "Hpin".
    rewrite /pwc_ban. iLeft. iExists [], [], 0%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iPureIntro. exact wr_ban_round0_p.
  Qed.

  Lemma pi_pin_epin (k : nat) (v : era_pins) :
    era_pin γ k v -∗ era_pin γ k v.
  Proof using . by iIntros "$". Qed.

  (* =================================================================== *)
  (*  S7  /INIT'S PROLOGUE DIAGNOSTICS ([EchoLinksPro] at this stage)      *)
  (* =================================================================== *)
  Definition pwc_pban (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pban_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_pdg (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
    : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pdiag_p ps cs I P a i⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.

  Definition pwc_pdiag (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
    : iProp Σ :=
    match i with
    | O => pwc_pban k v I
    | S _ => pwc_pdg k v I a i
    end.

  Global Instance pwc_pban_timeless k v I : Timeless (pwc_pban k v I).
  Proof using . rewrite /pwc_pban. tl_leaf. Qed.
  Global Instance pwc_pdg_timeless k v I a i : Timeless (pwc_pdg k v I a i).
  Proof using . rewrite /pwc_pdg. tl_leaf. Qed.
  Global Instance pwc_pdiag_timeless k v I a i :
    Timeless (pwc_pdiag k v I a i).
  Proof using .
    rewrite /pwc_pdiag. destruct i;
      [apply pwc_pban_timeless | apply pwc_pdg_timeless].
  Qed.

  Lemma pwc_pban_taint k v I : PT -∗ pwc_pban k v I.
  Proof using . iIntros "HT". rewrite /pwc_pban. by iRight. Qed.

  Lemma pwc_pdiag_taint k v I a i : PT -∗ pwc_pdiag k v I a i.
  Proof using .
    iIntros "HT". rewrite /pwc_pdiag. destruct i.
    - by iApply pwc_pban_taint.
    - rewrite /pwc_pdg. by iRight.
  Qed.

  Lemma pwc_pdiag_0 k v I a : pwc_pban k v I -∗ pwc_pdiag k v I a 0%nat.
  Proof using . by iIntros "$". Qed.

  Lemma pwc_pban_of_ban_done k v I :
    pwc_ban k v I (length u_banner) -∗ pwc_pban k v I.
  Proof using .
    rewrite /pwc_ban /pwc_pban. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18 in Hw. cbn [wr_banp_p] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_pban_of_ban_p ps' cs I P Hw).
  Qed.

  Lemma pwc_pro_of_pban k v I : pwc_pban k v I -∗ pwc_pro k v I.
  Proof using .
    rewrite /pwc_pban /pwc_pro. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (proj1 Hw).
  Qed.

  Lemma ppdiag_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    pro_alts !!! a !! i = Some b ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_pdiag k v I a i -∗
    (pwc_pdiag k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (pipe_links_w with "Hlk") as "#Hw".
    iDestruct (pipe_links_pro with "Hlk") as "#Hpro".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    pose proof (EchoLinksPro.pro_alts_lt_of_lookup a i b Hb) as Ha.
    destruct i as [| i].
    - rewrite /pwc_pdiag /pwc_pban /pwc_pdg.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k b Φ with "HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iRight. }
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
      pose proof (wr_pdiag_1_of_pro_p ps cs I P a Hw) as Hw'.
      destruct Hw as ((Hpin & Hm & Hdv & Hr & Hnd & HP) & _).
      iApply ("Hpro" $! k v P a b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { exact Ha. }
      { exact Hb. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [a]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
    - rewrite /pwc_pdiag /pwc_pdg.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k b Φ with "HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iRight. }
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
      pose proof (wr_pdiag_byte_p ps cs I P a (S i) b Hw Hb) as Hby.
      pose proof (wr_pdiag_S_p ps cs I P a (S i) Hw) as Hw'.
      destruct Hw as (Hpin & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v P b ps cs I Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { lia. }
      { exact Hpin. }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
  Qed.

  Lemma pwc_pdiag_done_1 (k : nat) (v : era_pins) (I : list (bv 8))
      (i : nat) :
    i = length (pro_alts !!! 1%nat) ->
    pwc_pdiag k v I 1%nat i -∗ pwc_ban k v I 0%nat.
  Proof using .
    intros Hi. rewrite Hi EchoLinksPro.pro_alts_1_length.
    rewrite /pwc_pdiag /pwc_pdg /pwc_ban.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iPureIntro. cbn [wr_banp_p].
    exact (wr_pdiag_done_1_p ps cs I P 21%nat
             (eq_sym EchoLinksPro.pro_alts_1_length) Hw).
  Qed.

End pipe_links_line.
