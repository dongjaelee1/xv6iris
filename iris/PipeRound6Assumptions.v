(* ===================================================================== *)
(*  PipeRound6Assumptions.v -- the REPORT file for lane SH-PIPE-ROUND-6.  *)
(*  NOT a row of iris/_CoqProject: it is compiled by hand                 *)
(*  (coqc <_CoqProject flags> -noglob PipeRound6Assumptions.v) and its    *)
(*  only content is [Print Assumptions] on this lane's results.          *)
(* ===================================================================== *)
Require Import UkShPipeFork.
Require Import UShPipeCatSlot.

(* obligation (A): the two prompt bytes at the terminal arm *)
Print Assumptions UkShPipeFork.pterm_prompt_step.
Print Assumptions UkShPipeFork.pterm_prompt_arm.
Print Assumptions UkShPipeFork.pterm_prompt_law.

(* the Timeless obstruction's GREEN half, and the timeless core *)
Print Assumptions UkShPipeFork.pterm_cursors_timeless.
Print Assumptions UkShPipeFork.pterm_tcore_read.
Print Assumptions UkShPipeFork.pterm_shape_tcore.

(* the /cat slot the pipeline era's boot is missing *)
Print Assumptions UShPipeCatSlot.pipe_sh_cat_slot.
