(* ===================================================================== *)
(*  PipeRound6Assumptions.v -- the REPORT file for lane SH-PIPE-ROUND-6.  *)
(*  NOT a row of iris/_CoqProject: it is compiled by hand                 *)
(*  (coqc <_CoqProject flags> -noglob PipeRound6Assumptions.v) and its    *)
(*  only content is [Print Assumptions] on this lane's results.          *)
(* ===================================================================== *)
Require Import UkShPipeFork.
Require Import UShPipeCatSlot.

(* obligation (A): the two prompt bytes at the terminal arm *)
Goal True. idtac "---- UkShPipeFork.pterm_wq_pay". Abort.
Print Assumptions UkShPipeFork.pterm_wq_pay.
Goal True. idtac "---- UkShPipeFork.pterm_prompt_step". Abort.
Print Assumptions UkShPipeFork.pterm_prompt_step.
Goal True. idtac "---- UkShPipeFork.pterm_prompt_arm". Abort.
Print Assumptions UkShPipeFork.pterm_prompt_arm.
Goal True. idtac "---- UkShPipeFork.pterm_prompt_law". Abort.
Print Assumptions UkShPipeFork.pterm_prompt_law.

(* the Timeless obstruction's GREEN half, and the timeless core *)
Goal True. idtac "---- UkShPipeFork.pterm_cursors_timeless". Abort.
Print Assumptions UkShPipeFork.pterm_cursors_timeless.
Goal True. idtac "---- UkShPipeFork.pterm_tcore_read". Abort.
Print Assumptions UkShPipeFork.pterm_tcore_read.
Goal True. idtac "---- UkShPipeFork.pterm_shape_tcore". Abort.
Print Assumptions UkShPipeFork.pterm_shape_tcore.

(* the /cat slot the pipeline era's boot is missing *)
Goal True. idtac "---- UShPipeCatSlot.pipe_sh_cat_slot". Abort.
Print Assumptions UShPipeCatSlot.pipe_sh_cat_slot.
