(* ===================================================================== *)
(*  PipeStage5Assumptions.v -- the REPORT file for lane PIPE-STAGE-5.     *)
(*  NOT a row of iris/_CoqProject: it is compiled by hand                 *)
(*  (coqc <_CoqProject flags> -noglob PipeStage5Assumptions.v) and its    *)
(*  only content is [Print Assumptions] on this lane's results.          *)
(*                                                                       *)
(*  WHAT THE LANE LANDED is design SS4.3n's FOURTH bullet -- the /cat pin *)
(*  on the round law, and its supply at the era equation.  The other      *)
(*  three bullets are REFUTED at the statement; see the lane's Findings   *)
(*  block in claude-notes/projects/app-pipe.md.                           *)
(* ===================================================================== *)
Require Import UShPipeRound.
Require Import UShPipeCatSlot.
Require Import UInitPipe.
Require Import UInitPipeAdequacy.

(* the round law, at its new premise list *)
Goal True. idtac "---- UShPipeRound.sh_round_holds_pipe". Abort.
Print Assumptions UShPipeRound.sh_round_holds_pipe.

(* the pin's producer (landed by SH-PIPE-ROUND-6, now WIRED) *)
Goal True. idtac "---- UShPipeCatSlot.pipe_sh_cat_slot". Abort.
Print Assumptions UShPipeCatSlot.pipe_sh_cat_slot.

(* the boot that supplies it *)
Goal True. idtac "---- UInitPipe.pipe_Hinit_boot". Abort.
Print Assumptions UInitPipe.pipe_Hinit_boot.

(* ...and the theorem the pipeline audit walks, unmoved *)
Goal True. idtac "---- UInitPipeAdequacy.pipe_adequacy_pipeSigma_of_child". Abort.
Print Assumptions UInitPipeAdequacy.pipe_adequacy_pipeΣ_of_child.
