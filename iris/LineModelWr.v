(* ===================================================================== *)
(*  LineModelWr.v -- THE WRITER'S STAGES AT THE THREE MODELS (M1's exit,  *)
(*  the half that lives beside the console families).  The file's and the *)
(*  pipe's [wr_*] predicates are [LineModel.lm_wr_*] BY CONVERSION.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import PipeDisc.
Require Import FileOutPure FileLinksLine.
Require Import PipeOutPure PipeLinksLine.
Require Import LineModel.
Require Import LineModelInst.
From stdpp Require Import ssreflect.

Local Open Scope nat_scope.

(* ---- the writer's stages, by conversion ---- *)
Lemma wr_pro_f_lm ps cs s0 I P : wr_pro_f ps cs s0 I P = lm_wr_pro file_lm ps cs s0 I P.
Proof using. rewrite /wr_pro_f /lm_wr_pro ?proc_stream_f_lm ?proc_before_f_lm. reflexivity. Qed.
Lemma wr_blk_f_lm ps cs s0 I P : wr_blk_f ps cs s0 I P = lm_wr_blk file_lm ps cs s0 I P.
Proof using. rewrite /wr_blk_f /lm_wr_blk ?proc_stream_f_lm ?proc_before_f_lm. reflexivity. Qed.
Lemma wr_open_f_lm ps cs s0 I P : wr_open_f ps cs s0 I P = lm_wr_open file_lm ps cs s0 I P.
Proof using. rewrite /wr_open_f /lm_wr_open ?proc_stream_f_lm ?proc_before_f_lm. reflexivity. Qed.
Lemma wr_owed_f_lm ps cs s0 I P : wr_owed_f ps cs s0 I P = lm_wr_owed file_lm ps cs s0 I P.
Proof using. rewrite /wr_owed_f /lm_wr_owed wr_pro_f_lm wr_blk_f_lm. reflexivity. Qed.
Lemma wr_sp_f_lm ps cs s0 I P : wr_sp_f ps cs s0 I P = lm_wr_sp file_lm ps cs s0 I P.
Proof using. rewrite /wr_sp_f /lm_wr_sp wr_open_f_lm proc_stream_f_lm. reflexivity. Qed.
Lemma wr_ban_f_lm ps cs s0 I P : wr_ban_f ps cs s0 I P = lm_wr_ban file_lm ps cs s0 I P.
Proof using. rewrite /wr_ban_f /lm_wr_ban ?proc_stream_f_lm ?proc_before_f_lm. reflexivity. Qed.
Lemma wr_banp_f_lm ps cs s0 I P i : wr_banp_f ps cs s0 I P i = lm_wr_banp file_lm ps cs s0 I P i.
Proof using. rewrite /wr_banp_f /lm_wr_banp. destruct i; [ apply wr_ban_f_lm | ]. f_equal. apply functional_extensionality. intros ps'. by rewrite wr_ban_f_lm. Qed.
Lemma wr_blk_t_f_lm ps cs s0 I P : wr_blk_t_f ps cs s0 I P = lm_wr_blk_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_blk_t_f /lm_wr_blk_t wr_blk_f_lm. reflexivity. Qed.

Lemma wr_pro_p_lm ps cs I P : wr_pro_p ps cs I P = lm_wr_pro pipe_lm ps cs tt I P.
Proof using. rewrite /wr_pro_p /lm_wr_pro ?proc_stream_p_lm ?proc_before_p_lm. reflexivity. Qed.
Lemma wr_blk_p_lm ps cs I P : wr_blk_p ps cs I P = lm_wr_blk pipe_lm ps cs tt I P.
Proof using. rewrite /wr_blk_p /lm_wr_blk ?proc_stream_p_lm ?proc_before_p_lm. reflexivity. Qed.
Lemma wr_open_p_lm ps cs I P : wr_open_p ps cs I P = lm_wr_open pipe_lm ps cs tt I P.
Proof using. rewrite /wr_open_p /lm_wr_open ?proc_stream_p_lm ?proc_before_p_lm. reflexivity. Qed.
Lemma wr_owed_p_lm ps cs I P : wr_owed_p ps cs I P = lm_wr_owed pipe_lm ps cs tt I P.
Proof using. rewrite /wr_owed_p /lm_wr_owed wr_pro_p_lm wr_blk_p_lm. reflexivity. Qed.
Lemma wr_sp_p_lm ps cs I P : wr_sp_p ps cs I P = lm_wr_sp pipe_lm ps cs tt I P.
Proof using. rewrite /wr_sp_p /lm_wr_sp wr_open_p_lm proc_stream_p_lm. reflexivity. Qed.
Lemma wr_ban_p_lm ps cs I P : wr_ban_p ps cs I P = lm_wr_ban pipe_lm ps cs tt I P.
Proof using. rewrite /wr_ban_p /lm_wr_ban ?proc_stream_p_lm ?proc_before_p_lm. reflexivity. Qed.
Lemma wr_blk_t_p_lm ps cs I P : wr_blk_t_p ps cs I P = lm_wr_blk_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_blk_t_p /lm_wr_blk_t wr_blk_p_lm. reflexivity. Qed.
