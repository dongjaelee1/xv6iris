(* ===================================================================== *)
(*  PipeStage3Assumptions.v -- [Print Assumptions] for lane              *)
(*  PIPE-STAGE-3's headline results (the terminal fork-failure round at  *)
(*  the STAGE).                                                          *)
(*                                                                       *)
(*  NOT A ROW IN [iris/_CoqProject], for [SystemAssumptions.v]'s reason: *)
(*  it is a report, not a proof, and it is compiled by hand against the  *)
(*  same load paths the build uses.                                      *)
(* ===================================================================== *)
Require Import PipeOut.
Require Import PipeBoth.

(* the claim's TERMINAL byte steps (item 1) *)
Print Assumptions PipeOut.pecl_blk2_open_t.
Print Assumptions PipeOut.pecl_blk2_byte_t.
(* ...and the landed two, unmoved, through the generalised proof *)
Print Assumptions PipeOut.pecl_blk2_open.
Print Assumptions PipeOut.pecl_blk2_byte.

(* the family's THIRD MODE (item 2) *)
Print Assumptions PipeBoth.pblk2_wit_t_forkc.
Print Assumptions PipeBoth.blk2_mode_fire.
Print Assumptions PipeBoth.pblk2_ecl_t_holds.
Print Assumptions PipeBoth.pblk2_cstep_R_t.
Print Assumptions PipeBoth.pblk2_cstep_L.
Print Assumptions PipeBoth.blk2_inv_close.

(* the SECOND SHAPE and the main loop's two right steps (item 3) *)
Print Assumptions PipeBoth.pprompt_dollar_fork.
Print Assumptions PipeBoth.pprompt_space_fork.

(* the FORK-#1 corollary (item 4) and the end-to-end TEST (item 5) *)
Print Assumptions PipeBoth.pblk2_fork1_chain.
Print Assumptions PipeBoth.pblk2_cstray_chain.
Print Assumptions PipeBoth.pterm_round_test.
Print Assumptions PipeBoth.pcont_sel_term.
Print Assumptions PipeBoth.palt_ok_sel_term.
