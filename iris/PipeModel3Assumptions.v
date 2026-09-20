(* ===================================================================== *)
(*  PipeModel3Assumptions.v -- [Print Assumptions] for lane              *)
(*  PIPE-MODEL-3's headline results.                                     *)
(*                                                                       *)
(*  NOT A ROW IN [iris/_CoqProject], for [SystemAssumptions.v]'s reason: *)
(*  it is a report, not a proof, and it is compiled by hand against the  *)
(*  same load paths the build uses.                                      *)
(* ===================================================================== *)
Require Import PipeDisc.
Require Import PipeDiscDec.
Require Import PipeOutPure.
Require Import PipeForkGap.

(* the pure model: the terminal round, the shuffle test, D4 *)
Print Assumptions PipeDisc.palt_of_code.
Print Assumptions PipeDisc.pcont_forkS_old.
Print Assumptions PipeDisc.pmergeable_forkS.
Print Assumptions PipeDisc.pmergeable_prefix.
Print Assumptions PipeDisc.d4_ambiguous.

(* determinacy, at the two premises D4 supplies *)
Print Assumptions PipeDisc.pcont_pair_det.
Print Assumptions PipeDisc.sessp_prefix_det.

(* the decision procedure, with the new alternative *)
Print Assumptions PipeDiscDec.elem_of_forkS_sels.
Print Assumptions PipeDiscDec.disc_p_dec.

(* the stage's readings *)
Print Assumptions PipeOutPure.d4_p_nomerge_snoc.
Print Assumptions PipeOutPure.good_out_p_of_stage.
Print Assumptions PipeOutPure.D2_next_input_p.

(* the demos and the retired gap *)
Print Assumptions PipeDisc.demo_p_fork.
Print Assumptions PipeDisc.demo_p_fork_disc.
Print Assumptions PipeDisc.demo_p_bad.
Print Assumptions PipeForkGap.pfork_execL_admitted.
Print Assumptions PipeForkGap.pfork_execL_only_forkS.
Print Assumptions PipeForkGap.gap_mixed_no_wit.
