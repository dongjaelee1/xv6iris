(* ===================================================================== *)
(*  PipeRound7Assumptions.v -- lane SH-PIPE-ROUND-7's report file.       *)
(*  NOT a [_CoqProject] row: compiled by hand on the mirror, its output  *)
(*  quoted in the lane's report.                                        *)
(* ===================================================================== *)
Require Import UkRunLeaf.
Require Import UkShLoop.
Require Import UkShPipeWait.
Require Import UkShPipeFork.

Print Assumptions UkRunLeaf.wp_uk_cmv_later.
Print Assumptions UkRunLeaf.wp_uk_cjr_later.
Print Assumptions UkShPipeWait.wp_kshr_wait_pid_later.
Print Assumptions UkShLoop.ushl_head_of_later.
Print Assumptions UkShPipeFork.pterm_wc_inp_of.
