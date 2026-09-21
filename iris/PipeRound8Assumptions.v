(* ===================================================================== *)
(*  PipeRound8Assumptions.v -- lane SH-PIPE-ROUND-8's report file.        *)
(*  NOT a [_CoqProject] row: compiled by hand on the mirror.              *)
(* ===================================================================== *)
Require Import UShPipeChild.
Print Assumptions wp_kshm_child_pipe_paid_at.
Print Assumptions wp_kshm_child_pipe_paid_line_at.
Print Assumptions wp_kshm_child_pipe_paid.
Print Assumptions wp_kshm_child_pipe_paid_line.

Require Import UShPipeAssembly.
Print Assumptions ksh_w1_acc.
Print Assumptions exf_law_fupd.
Print Assumptions ksh_w1_of_step.
Print Assumptions out_chain_of_step.
Print Assumptions wp_kshr_exit0_paid.
Print Assumptions pipe_names_alloc.
Print Assumptions pipe_inv_alloc_at.
Print Assumptions pipe_fork_panic_law.
