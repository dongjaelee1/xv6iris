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
Require Import UmodeAbi.          (* [ubyte0] *)
Require Import UserHeap.          (* [uarg] / [ua_len] / [ua_bytes] *)
Require Import UexecSlot.         (* [uvis] and its fields *)
Require Import SpecKexec.         (* [kexec_image_ok] *)
Require Import ElfUser.           (* [echo_elf] *)
Require Import LineWords.         (* [wl_line] / [wl_off] / [wl_line_word] *)
Require Import EchoDisc.          (* [echo_line] / [echo_line_out] / [line_alts] *)
Require Import UEchoKernel.       (* [echo_arg] / [echo_args] *)
Require Import UkShEcho.          (* [echo_off] / [echo_alen] *)
Require Import UShEcho.           (* [echo_key_args] *)
Require Import UEchoOut.          (* [echo_out_argv] *)
(* as in EchoDisc / UEchoOut: the Sail imports leave string_scope on top *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1  THE BRIDGE, IN ONE SENTENCE                                       *)
(*                                                                       *)
(*  [EchoDisc.echo_line_out] IS [wl_line] of the line's TAIL, so the      *)
(*  alternative's byte where the OUTPUT puts word [i] and the line's byte *)
(*  where the INPUT puts it are the same byte of the same word -- twice   *)
(*  [LineWords.wl_line_word] and nothing else.  This used to be two       *)
(*  five-way case analyses over the literal's offsets.                    *)
(*                                                                       *)
(*  (The alternative continues past the output with the prompt sh writes  *)
(*  once it has reaped, which is why the lookup needs the bound.)         *)
(* ===================================================================== *)
Lemma echo_alt0_word (i j : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> echo_ws !! i = Some w -> (j < length w)%nat ->
  line_alts !!! 0%nat !! (echo_ocur i + j)%nat
  = Some (echo_line !!! (UkShEcho.echo_off i + j)%nat).
Proof.
  intros Hi Hw Hj.
  assert (Hd : drop 1 echo_ws !! (i - 1)%nat = Some w)
    by (rewrite echo_ws_drop; [exact Hw | exact Hi]).
  rewrite (echo_alt0_out (echo_ocur i + j)%nat
             (echo_ocur_lt i w j Hi Hw (Nat.lt_le_incl _ _ Hj))).
  rewrite /echo_line_out /echo_ocur.
  destruct (lookup_lt_is_Some_2 (wl_line (drop 1 echo_ws))
              (wl_off 0%nat (drop 1 echo_ws) (i - 1)%nat + j)%nat
              ltac:(exact (wl_off_lt_line (drop 1 echo_ws) (i - 1)%nat w j
                             Hd (Nat.lt_le_incl _ _ Hj)))) as [b Hb].
  rewrite Hb. f_equal.
  rewrite <- (list_lookup_total_correct _ _ _ Hb).
  rewrite (wl_line_word (drop 1 echo_ws) (i - 1)%nat w j Hd Hj).
  rewrite /UkShEcho.echo_off echo_line_words.
  by rewrite (wl_line_word echo_ws i w j Hw Hj).
Qed.

(* ===================================================================== *)
(*  S2  THE BRIDGE                                                        *)
(* ===================================================================== *)
Lemma echo_out_argv_of_key_args (M : gmap Z (bv 8)) (av : Z) (argcn : nat) :
  argcn = length echo_ws ->
  (forall i : nat, (i < length echo_ws)%nat ->
     ua_len (echo_arg M av i) = length (echo_ws !!! i)
     /\ forall j : nat, (j < length (echo_ws !!! i))%nat ->
          ua_bytes (echo_arg M av i) j
          = echo_line !!! (UkShEcho.echo_off i + j)%nat) ->
  UEchoOut.echo_out_argv (echo_args M av argcn).
Proof.
  intros -> Hk. rewrite /UEchoOut.echo_out_argv.
  split; [ exact (echo_args_length M av (length echo_ws)) | ].
  intros i g Hi1 Hg.
  assert (Hilt : (i < length echo_ws)%nat)
    by (apply lookup_lt_Some in Hg; rewrite echo_args_length in Hg; lia).
  rewrite (echo_args_lookup M av (length echo_ws) i Hilt) in Hg.
  injection Hg as <-.
  destruct (Hk i Hilt) as [Hlen Hb].
  split; [ exact Hlen | ].
  intros j Hj. rewrite Hlen in Hj.
  rewrite (Hb j Hj).
  exact (echo_alt0_word i j (echo_ws !!! i) Hi1 (echo_ws_at i Hilt) Hj).
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
  intros Hok Hna Halen Hafun. subst na.
  (* the general reading's ONE side condition, at this line: no byte exec
     pushed is a NUL, because every one of them is the line's own *)
  assert (Hno : forall i j : nat, (i < 3)%nat -> (j < alen i)%nat ->
            afun i j <> ubyte0).
  { intros i j Hi Hj. rewrite (Halen i Hi) in Hj.
    rewrite (Hafun i j Hi Hj).
    exact (UShEcho.echo_line_nonul _
             (UkShEcho.echo_off_lt i j Hi (Nat.lt_le_incl _ _ Hj))). }
  destruct (UShEcho.echo_key_args_holds 3%nat alen afun sts W Hok Hno)
    as [Hargc Hk].
  apply (echo_out_argv_of_key_args (uvis_M W) (uvis_av W)
           (Z.to_nat (uvis_argc W)) Hargc).
  intros i Hi. destruct (Hk i Hi) as [Hl Hb].
  split; [ rewrite Hl; exact (Halen i Hi) | ].
  intros j Hj. rewrite (Hb j ltac:(rewrite (Halen i Hi); exact Hj)).
  exact (Hafun i j Hi Hj).
Qed.
