(* ===================================================================== *)
(*  PipeRound4Assumptions.v -- [Print Assumptions] for lane              *)
(*  SH-PIPE-ROUND-4's headline results.                                  *)
(*                                                                       *)
(*  NOT A ROW IN [iris/_CoqProject], for [SystemAssumptions.v]'s reason: *)
(*  it is a report, not a proof, and it is compiled by hand against the  *)
(*  same load paths the build uses.                                      *)
(* ===================================================================== *)
Require Import PipeLinkInst.
Require Import PipeBoth.
Require Import UCatPipe.
Require Import PipeForkGap.

(* R1: the widened boundary credential, the record it fills, and the
   prompt step that consumes it *)
Print Assumptions PipeBoth.pwc_line2.
Print Assumptions PipeBoth.pprompt_dollar_line2.
Print Assumptions PipeBoth.pblk2_exit_lk.
Print Assumptions PipeLinkInst.pipe_link_inst_at.

(* R2: the recoverable family *)
Print Assumptions PipeBoth.blk2_inv_alloc.
Print Assumptions PipeBoth.blk2_mode_fire.
Print Assumptions PipeBoth.pblk2_cstep_L.
Print Assumptions PipeBoth.pblk2_cstep_R.
Print Assumptions PipeBoth.blk2_inv_close.

(* R3: cat's round, generic and at its landed instance *)
Print Assumptions UCatPipe.pcat_round_at_g.
Print Assumptions UCatPipe.pcat_round_at.

(* H4: the model's gap at the second fork's panic *)
Print Assumptions PipeForkGap.pfork_execL_gap.
Print Assumptions PipeForkGap.gap_mixed_no_wit.
