(* ===================================================================== *)
(*  LineModelInst.v -- THE THREE APPLICATIONS AS LINE MODELS (M1's exit). *)
(*                                                                       *)
(*  [FileDisc.sessf], [PipeDisc.sessp] and [EchoDisc.sess] are            *)
(*  [LineModel.lm_sess] at the instance, by the three equations below.   *)
(*  The instances are DEFINITIONS over the landed pieces ([FileDisc.cont],*)
(*  [fsm], [ralt_dec]; [PipeDisc.pcont], [palt_of]; [EchoDisc.            *)
(*  line_alts_of]), so nothing in the three model files moves; the        *)
(*  equations are by induction on the round count, since the landed       *)
(*  fixpoints ([fstate_upto], [pro_idx_f], ...) and the generic ones are  *)
(*  structurally equal but not convertible at an open index.             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import PipeDisc.
Require Import FileOutPure.
Require Import PipeOutPure.
Require Import LineModel.
From stdpp Require Import ssreflect.

Local Open Scope nat_scope.

(* ====================================================================== *)
(*  1.  THE FILE APPLICATION                                               *)
(* ====================================================================== *)
Definition file_lm : lmodel :=
  MkLM fstate uline uline_of ralt ralt_dec ralt_panic cont fsm
       ralt_ok fbody_ok fbody_byte.

Lemma pro_idx_f_lm cs i : pro_idx_f cs i = lm_pro_idx file_lm cs i.
Proof using. induction i as [| i IH]; [reflexivity |]. cbn. by rewrite IH. Qed.

Lemma fstate_upto_lm cs s bs q :
  fstate_upto cs s bs q = lm_upto file_lm cs s bs q.
Proof using. induction q as [| q IH]; [reflexivity |]. cbn. by rewrite IH. Qed.

Lemma alt_cont_f_lm ps cs s bs i :
  alt_cont_f ps cs s bs i = lm_cont_at file_lm ps cs s bs i.
Proof using.
  rewrite /alt_cont_f /lm_cont_at fstate_upto_lm pro_idx_f_lm. reflexivity.
Qed.

Lemma alt_seq_f_lm ps cs s bs q :
  alt_seq_f ps cs s bs q = lm_seq file_lm ps cs s bs q.
Proof using. reflexivity. Qed.

Lemma sessf_lm ps cs s I : sessf ps cs s I = lm_sess file_lm ps cs s I.
Proof using. rewrite /sessf /lm_sess. by rewrite alt_seq_f_lm. Qed.

(* the stream fold takes the state as a fixpoint PARAMETER (at [option
   fstate] on the stage side), so these two are inductions, not conversions *)
Lemma pending_at_f_lm ps cs s0 I :
  pending_at_f ps cs (Some s0) I = lm_pending_at file_lm ps cs s0 I.
Proof using. reflexivity. Qed.

Lemma proc_before_from_f_lm ps cs s0 pre I :
  proc_before_from_f ps cs (Some s0) pre I
  = lm_proc_before_from file_lm ps cs s0 pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre; [reflexivity |].
  cbn. by rewrite IH pending_at_f_lm.
Qed.

Lemma proc_before_f_lm ps cs s0 I :
  proc_before_f ps cs (Some s0) I = lm_proc_before file_lm ps cs s0 I.
Proof using. apply proc_before_from_f_lm. Qed.

Lemma proc_stream_f_lm ps cs s0 I :
  proc_stream_f ps cs (Some s0) I = lm_proc_stream file_lm ps cs s0 I.
Proof using.
  rewrite /proc_stream_f /lm_proc_stream. by rewrite proc_before_f_lm pending_at_f_lm.
Qed.
Lemma alts_ok_lm I cs : alts_ok I cs = lm_alts_ok file_lm I cs.
Proof using. reflexivity. Qed.
Lemma disc_input_f_lm I : disc_input_f I = lm_disc_input file_lm I.
Proof using. reflexivity. Qed.

Lemma fstate_after_lm cs s I : fstate_after cs s I = lm_after file_lm cs s I.
Proof using. rewrite /fstate_after /lm_after. apply fstate_upto_lm. Qed.

Lemma pro_ok_f_lm ps cs q : pro_ok_f ps cs q <-> lm_pro_ok file_lm ps cs q.
Proof using. rewrite /pro_ok_f /lm_pro_ok pro_idx_f_lm. reflexivity. Qed.

Lemma pro_pin_f_lm ps cs I : pro_pin_f ps cs I <-> lm_pro_pin file_lm ps cs I.
Proof using.
  rewrite /pro_pin_f /lm_pro_pin. split; intros H q Hq; specialize (H q Hq);
    by rewrite -?pro_idx_f_lm ?pro_idx_f_lm in H |- *.
Qed.

(* ====================================================================== *)
(*  2.  THE PIPELINE APPLICATION -- no state                               *)
(* ====================================================================== *)
Definition pipe_lm : lmodel :=
  MkLM unit pline pline_of palt palt_of palt_panic (fun _ => pcont)
       (fun _ _ _ => tt) palt_ok pbody_ok pbody_byte.

Lemma pro_idx_p_lm cs i : pro_idx_p cs i = lm_pro_idx pipe_lm cs i.
Proof using. induction i as [| i IH]; [reflexivity |]. cbn. by rewrite IH. Qed.

Lemma alt_cont_p_lm ps cs bs i :
  alt_cont_p ps cs bs i = lm_cont_at pipe_lm ps cs tt bs i.
Proof using. rewrite /alt_cont_p /lm_cont_at pro_idx_p_lm. reflexivity. Qed.

Lemma alt_seq_p_lm ps cs bs q :
  alt_seq_p ps cs bs q = lm_seq pipe_lm ps cs tt bs q.
Proof using. reflexivity. Qed.

Lemma sessp_lm ps cs I : sessp ps cs I = lm_sess pipe_lm ps cs tt I.
Proof using. rewrite /sessp /lm_sess. by rewrite alt_seq_p_lm. Qed.

Lemma pending_at_p_lm ps cs I :
  pending_at_p ps cs I = lm_pending_at pipe_lm ps cs tt I.
Proof using. reflexivity. Qed.

Lemma proc_before_from_p_lm ps cs pre I :
  proc_before_from_p ps cs pre I = lm_proc_before_from pipe_lm ps cs tt pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre; [reflexivity |].
  cbn. by rewrite IH pending_at_p_lm.
Qed.

Lemma proc_before_p_lm ps cs I :
  proc_before_p ps cs I = lm_proc_before pipe_lm ps cs tt I.
Proof using. apply proc_before_from_p_lm. Qed.

Lemma proc_stream_p_lm ps cs I :
  proc_stream_p ps cs I = lm_proc_stream pipe_lm ps cs tt I.
Proof using.
  rewrite /proc_stream_p /lm_proc_stream. by rewrite proc_before_p_lm pending_at_p_lm.
Qed.
Lemma alts_ok_p_lm I cs : alts_ok_p I cs = lm_alts_ok pipe_lm I cs.
Proof using. reflexivity. Qed.
Lemma disc_input_p_lm I : disc_input_p I = lm_disc_input pipe_lm I.
Proof using. reflexivity. Qed.

Lemma pro_ok_p_lm ps cs q : pro_ok_p ps cs q <-> lm_pro_ok pipe_lm ps cs q.
Proof using. rewrite /pro_ok_p /lm_pro_ok pro_idx_p_lm. reflexivity. Qed.

(* ====================================================================== *)
(*  3.  THE ECHO APPLICATION -- the four alternatives are their own code   *)
(* ====================================================================== *)
Definition echo_lm : lmodel :=
  MkLM unit (list (list (bv 8))) wl_words nat (fun k => k)
       (fun k => bool_decide (k = 3))
       (fun _ ws k => line_alts_of ws !!! k)
       (fun _ _ _ => tt) (fun _ k => k < 4) body_ok wl_body_byte.

Lemma pro_idx_lm cs i : pro_idx cs i = lm_pro_idx echo_lm cs i.
Proof using.
  induction i as [| i IH]; [reflexivity |]. cbn. rewrite IH.
  rewrite /lm_at /=. by case_bool_decide; case_decide; lia.
Qed.

Lemma alt_cont_lm ps cs bs i :
  alt_cont ps cs bs i = lm_cont_at echo_lm ps cs tt bs i.
Proof using.
  rewrite /alt_cont /lm_cont_at /lm_at /= pro_idx_lm.
  by case_bool_decide; case_decide; try lia.
Qed.

Lemma alt_seq_lm ps cs bs q : alt_seq ps cs bs q = lm_seq echo_lm ps cs tt bs q.
Proof using.
  rewrite /alt_seq /lm_seq. f_equal. apply list_fmap_ext. intros i x _.
  rewrite /alt_blk /lm_blk. by rewrite alt_cont_lm.
Qed.

Lemma sess_lm ps cs I : sess ps cs I = lm_sess echo_lm ps cs tt I.
Proof using. rewrite /sess /lm_sess. by rewrite alt_seq_lm. Qed.

Lemma pro_ok_lm ps cs q : pro_ok ps cs q <-> lm_pro_ok echo_lm ps cs q.
Proof using. rewrite /pro_ok /lm_pro_ok pro_idx_lm. reflexivity. Qed.
