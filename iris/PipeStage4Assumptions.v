(* ===================================================================== *)
(*  PipeStage4Assumptions.v -- lane PIPE-STAGE-4's report file.           *)
(*  NOT a [_CoqProject] row: compiled by hand on the mirror.              *)
(* ===================================================================== *)
Require Import PipeOut.

(* the claim's side of design SS4.3m: the flag, the freeze, the guard *)
Print Assumptions pcs_freeze.
Print Assumptions cs_frozen_at_lb_absurd.
Print Assumptions pecl_blk2_open.
Print Assumptions pecl_blk2_byte.
Print Assumptions pecl_blk2_open_t.
Print Assumptions pecl_blk2_byte_t.
Print Assumptions pecl_blk2_file.
Print Assumptions pecl_step_write_blk.

Require Import PipeBoth.

(* the family at the flag *)
Print Assumptions pblk2_ecl_holds.
Print Assumptions pblk2_ecl_t_holds.
Print Assumptions blk2_inv_alloc.
Print Assumptions blk2_mode_fire.
Print Assumptions blk2_inv_close.
Print Assumptions blk2_inv_close_nt.
Print Assumptions pblk2_cstep_L.
Print Assumptions pblk2_cstep_R.
Print Assumptions pblk2_cstep_R_t.
Print Assumptions pblk2_exit.
Print Assumptions pblk2_exit_lk.
Print Assumptions pwc_fork_exit.
Print Assumptions pprompt_dollar_fork.
Print Assumptions pprompt_space_fork.
Print Assumptions pblk2_cterm_chain_fz.
Print Assumptions pblk2_fork1_chain.

(* THE READ AFTER A TERMINAL PROMPT *)
Print Assumptions pterm_read_absurd.
Print Assumptions pterm_fork_exit_read.

(* the tests *)
Print Assumptions pterm_round_test.
Print Assumptions pterm_round_read_test.

Require Import UShPipeExit.
Print Assumptions pecl_open_cs_len.
Print Assumptions pipe_blk2_not_line.

Require Import UShPipeRound2.
Print Assumptions pipe_round_entry.
Print Assumptions pipe_round_exit.
Print Assumptions pipe_round_unwind.
Print Assumptions pipe_fork_exit_not_lpr.
