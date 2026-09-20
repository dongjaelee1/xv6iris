(* ===================================================================== *)
(*  PipeRound5Assumptions.v -- lane SH-PIPE-ROUND-5's report file.        *)
(*  NOT a [_CoqProject] row: compiled by hand on the mirror.              *)
(* ===================================================================== *)
Require Import UShPipeRound2.

Print Assumptions pround_code.
Print Assumptions pipe_round_entry.
Print Assumptions pipe_round_exit.
Print Assumptions pipe_round_unwind.
Print Assumptions pwc_blk2_zero_to_blk.
Print Assumptions pwc_lpr2_turn.
Print Assumptions pround_turn_three.
Print Assumptions pipe_half_not_lpr.
Print Assumptions pipe_fork_exit_not_lpr.
Print Assumptions ep_pay_frame.

(* part 2 *)
Require Import UkShPipeFork.
Print Assumptions pterm_shape_pin.
Print Assumptions pterm_pay_taint.
Print Assumptions pterm_wc_3.
Print Assumptions pterm_wb_wc.
Print Assumptions pterm_wc_blk_line.
Print Assumptions pterm_wcp_3.
Print Assumptions pterm_wcp_of.
Print Assumptions pterm_posw_3.
Print Assumptions pterm_posb_of.
Print Assumptions pterm_posb_of_shape.
Print Assumptions pterm_wc_read_of.
