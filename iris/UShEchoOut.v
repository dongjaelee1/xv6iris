(* ===================================================================== *)
(*  UShEchoOut.v -- WHAT SH OWES ECHO'S OUTPUT                            *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane IO-LEAF, M3.)       *)
(*                                                                       *)
(*  [UEchoOut.echo_uexec_slot_at] -- echo's entry at the era's stage --   *)
(*  carries premises echo itself cannot know, because they are facts      *)
(*  about the process that EXEC'd it.  One of them is its argument        *)
(*  vector: [UEchoOut.echo_out_argv] says argc is three and that          *)
(*  [argv[1]] and [argv[2]] are the two tokens of the completed line,     *)
(*  spelled against the ERA's alternative ([EchoDisc.line_alts !!! 0],    *)
(*  "hello world\n$ ") rather than against the shell's lexer -- so that   *)
(*  nothing in [UEchoOut] depends on which parser produced the vector.    *)
(*                                                                       *)
(*  THIS FILE IS THE OTHER HALF OF THAT SENTENCE.  sh's parser pins the   *)
(*  three arguments to [EchoDisc.echo_line] ([UShEcho.echo_key_args], off *)
(*  the exec channel's [SpecKexec.kexec_image_ok]), and the era's         *)
(*  alternative is the SAME BYTES one offset on: [echo_line] is           *)
(*  "echo hello world\n" and the line's continuation after the command    *)
(*  name is "hello world\n".  So the bridge is two closed computations    *)
(*  and nothing else, and it is a file of its own because it is the ONE   *)
(*  place where the shell's reading of the line and the claim's reading   *)
(*  of the transcript are the same bytes -- [UShEcho.v] sits below        *)
(*  [UEchoOut.v] and cannot name it.                                      *)
(*                                                                       *)
(*  WHAT IS STILL OWED at [echo_uexec_slot_at]: the child's fd 1 is the   *)
(*  console ([take NSTD (uvis_fd W) !! 1]).  The exec channel carries the *)
(*  table verbatim ([kexec_image_ok]'s [uvis_fd W' = sts]), so that one   *)
(*  is a fact about SH's table and travels with the entry lend -- lane    *)
(*  IO-LEAF, M3b, which is blocked (see the lane note).                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import FdSlots.
Require Import UserHeap.          (* [uarg] / [ua_len] / [ua_bytes] *)
Require Import UexecSlot.         (* [uvis] and its fields *)
Require Import SpecKexec.         (* [kexec_image_ok] *)
Require Import ElfUser.           (* [echo_elf] *)
Require Import EchoDisc.          (* [echo_line] / [line_alts] *)
Require Import UEchoKernel.       (* [echo_arg] / [echo_args] *)
Require Import UkShEcho.          (* [echo_off] / [echo_alen] *)
Require Import UShEcho.           (* [echo_key_args] *)
Require Import UEchoOut.          (* [echo_out_argv] *)
(* as in EchoDisc / UEchoOut: the Sail imports leave string_scope on top *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1  THE TWO CLOSED COMPUTATIONS                                       *)
(*                                                                       *)
(*  [echo_line]      = "echo hello world\n"   (17 bytes)                  *)
(*  [line_alts !!! 0] = "hello world\n$ "     (14 bytes)                  *)
(*                                                                       *)
(*  sh's token [i] starts at [echo_off i] of the LINE; echo prints tokens *)
(*  1 and 2, which are the alternative's bytes 0..4 and 6..10.  (Byte 5   *)
(*  of the alternative is echo's own separator, out of .rodata, and bytes *)
(*  12..13 are the prompt sh writes after it reaps -- neither is argv's.) *)
(* ===================================================================== *)
Lemma echo_alt0_tok1 (j : nat) :
  (j < UkShEcho.echo_alen 1%nat)%nat ->
  line_alts !!! 0%nat !! j
  = Some (echo_line !!! (UkShEcho.echo_off 1%nat + j)%nat).
Proof.
  rewrite UkShEcho.echo_alen_1 UkShEcho.echo_off_1. intro Hj.
  do 5 (destruct j as [| j]; [ vm_compute; reflexivity | ]).
  exfalso. lia.
Qed.

Lemma echo_alt0_tok2 (j : nat) :
  (j < UkShEcho.echo_alen 2%nat)%nat ->
  line_alts !!! 0%nat !! (6 + j)%nat
  = Some (echo_line !!! (UkShEcho.echo_off 2%nat + j)%nat).
Proof.
  rewrite UkShEcho.echo_alen_2 UkShEcho.echo_off_2. intro Hj.
  do 5 (destruct j as [| j]; [ vm_compute; reflexivity | ]).
  exfalso. lia.
Qed.

(* ===================================================================== *)
(*  S2  THE BRIDGE                                                        *)
(* ===================================================================== *)
Lemma echo_out_argv_of_key_args (M : gmap Z (bv 8)) (av : Z) (argcn : nat) :
  argcn = 3%nat ->
  (forall i : nat, (i < 3)%nat ->
     ua_len (echo_arg M av i) = UkShEcho.echo_alen i
     /\ forall j : nat, (j < UkShEcho.echo_alen i)%nat ->
          ua_bytes (echo_arg M av i) j
          = echo_line !!! (UkShEcho.echo_off i + j)%nat) ->
  UEchoOut.echo_out_argv (echo_args M av argcn).
Proof.
  intros -> Hk. rewrite /UEchoOut.echo_out_argv.
  split_and!.
  - exact (echo_args_length M av 3%nat).
  - intros g Hg.
    rewrite (echo_args_lookup M av 3%nat 1%nat ltac:(lia)) in Hg.
    injection Hg as <-.
    destruct (Hk 1%nat ltac:(lia)) as [Hlen Hb].
    split; [ rewrite Hlen; reflexivity | ].
    intros j Hj. rewrite (Hb j ltac:(rewrite UkShEcho.echo_alen_1; lia)).
    exact (echo_alt0_tok1 j ltac:(rewrite UkShEcho.echo_alen_1; lia)).
  - intros g Hg.
    rewrite (echo_args_lookup M av 3%nat 2%nat ltac:(lia)) in Hg.
    injection Hg as <-.
    destruct (Hk 2%nat ltac:(lia)) as [Hlen Hb].
    split; [ rewrite Hlen; reflexivity | ].
    intros j Hj. rewrite (Hb j ltac:(rewrite UkShEcho.echo_alen_2; lia)).
    exact (echo_alt0_tok2 j ltac:(rewrite UkShEcho.echo_alen_2; lia)).
Qed.

(* ...AND OFF THE EXEC CHANNEL, which is the form the entry constructor
   will take it at: what sh hands the kernel is the node its parser built
   ([UkShEcho.echo_argv_bytes]), what the kernel hands back is the image
   ([SpecKexec.kexec_image_ok]), and [UShEcho.echo_key_args_holds] is the
   step between them. *)
Lemma echo_out_argv_of_image (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W ->
  na = 3%nat ->
  (forall i : nat, (i < 3)%nat -> alen i = UkShEcho.echo_alen i) ->
  (forall i j : nat, (i < 3)%nat -> (j < UkShEcho.echo_alen i)%nat ->
     afun i j = echo_line !!! (UkShEcho.echo_off i + j)%nat) ->
  UEchoOut.echo_out_argv
    (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))).
Proof.
  intros Hok Hna Halen Hafun.
  destruct (UShEcho.echo_key_args_holds na alen afun sts W Hok Hna Halen Hafun)
    as [Hargc Hk].
  exact (echo_out_argv_of_key_args (uvis_M W) (uvis_av W)
           (Z.to_nat (uvis_argc W)) Hargc Hk).
Qed.
