(* ===================================================================== *)
(*  PipeExecEchoAssumptions.v -- [Print Assumptions] for lane            *)
(*  PIPE-EXEC-ECHO's headline results (design                            *)
(*  claude-notes/design/app-pipe.md SS4.3g, holes H1 and H3 and the      *)
(*  round's third owed item).                                            *)
(*                                                                       *)
(*  NOT A ROW IN [iris/_CoqProject], for [PipeRound4Assumptions.v]'s     *)
(*  reason: it is a report, not a proof, and it is compiled by hand      *)
(*  against the same load paths the build uses.                          *)
(* ===================================================================== *)
Require Import PipeProto.
Require Import UShPipeCall.
Require Import UShEchoPipePay.

(* THE READER-SIDE LOWER BOUND and the round's exclusion, plus the pure
   witness that says why the body needed (P5) first *)
Print Assumptions PipeProto.pws_lb_of_rcur.
Print Assumptions PipeProto.pipe_excl_wtok_lb.
Print Assumptions PipeProto.pipe_excl_wtok_lb_pipeN.
Print Assumptions PipeProto.pipe_body_needs_P5.
Print Assumptions PipeProto.pipe_body_P5.

(* H1: sh's pipe(2) stub at a REAL registrar, and its instance at echo's *)
Print Assumptions UShPipeCall.ush_pipe_call_paid.
Print Assumptions UShEchoPipePay.ep_registrar_of_wq.
Print Assumptions UShEchoPipePay.ush_pipe_call_echo_pay.

(* H3: sh's exec of /echo with fd 1 = a pipe's write end *)
Print Assumptions UShEchoPipePay.sh_exec_sup_echo_pipe_at.
Print Assumptions UShEchoPipePay.image_entry_pay_mono.
