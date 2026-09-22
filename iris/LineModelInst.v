(* ===================================================================== *)
(*  LineModelInst.v -- THE STREAM FOLDS AT THE INSTANCES, AND THE ECHO    *)
(*  MODEL (app-both milestone M1).                                       *)
(*                                                                       *)
(*  The file's and the pipe's line models live with their models         *)
(*  ([FileDisc.file_lm], [PipeDisc.pipe_lm], with the session equations  *)
(*  and the determinacy corollaries).  What is left here is what needs   *)
(*  the stage files: the stream folds ([FileOutPure.proc_stream_f],       *)
(*  [PipeOutPure.proc_stream_p]) as [LineModel]'s, by induction -- the   *)
(*  state is a fixpoint PARAMETER there (at [option fstate] on the file   *)
(*  side, absent on the pipe side), so those fixes do not convert -- and *)
(*  the echo model, whose session is [EchoDisc.sess] by an equation      *)
(*  (its panic test is [decide], the model's [bool_decide]).             *)
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
(*  1.  THE FILE APPLICATION'S STREAM                                      *)
(* ====================================================================== *)
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

(* ====================================================================== *)
(*  2.  THE PIPELINE APPLICATION'S STREAM                                  *)
(* ====================================================================== *)
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

(* ====================================================================== *)
(*  3.  THE ECHO APPLICATION -- the four alternatives are their own code   *)
(*                                                                        *)
(*  No byte-shape laws are stated: [EchoOutPure.sess_prefix_det] is       *)
(*  stated at [cs_ok] (every code below 4, at every index), not at the    *)
(*  model's range condition, and echo is the pipeline's corollary in the  *)
(*  landed tree ([PipeDisc.disc_disc_p]).                                 *)
(* ====================================================================== *)
Definition echo_lm : lmodel :=
  MkLM unit (list (list (bv 8))) wl_words nat (fun k => k)
       (fun k => bool_decide (k = 3))
       (fun _ ws k => line_alts_of ws !!! k)
       (fun _ _ _ => tt) (fun _ k => k < 4) body_ok wl_body_byte
       line_ok (fun _ => True) (fun _ => false) (fun _ => False).

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
