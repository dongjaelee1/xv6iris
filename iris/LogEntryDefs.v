(* ====================================================================== *)
(* LogEntryDefs.v -- THE CONSOLE INPUT LOG'S ENTRY TYPE.                   *)
(*                                                                        *)
(* [log_entry] and its three projections, over nothing but [mobs] and a    *)
(* byte.  The TSO points-to layer ([RiscvPtsto.v]) names this type to      *)
(* state the console log's resource and wants nothing else from the log's  *)
(* theory; parked in [ConsLog.v] it put that whole theory -- the echo      *)
(* shapes, the erase arms, the history lemmas -- in front of it.           *)
(*                                                                        *)
(* [ConsLog.v] RE-EXPORTS this file, so every existing importer sees these *)
(* four names exactly where it saw them before.                           *)
(* ====================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)

Definition log_entry : Type := (list mobs * bv 8 * list (bv 8))%type.
Definition le_hist (e : log_entry) : list mobs := e.1.1.
Definition le_byte (e : log_entry) : bv 8 := e.1.2.
Definition le_echo (e : log_entry) : list (bv 8) := e.2.
