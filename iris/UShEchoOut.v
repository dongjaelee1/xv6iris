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
(*  alternative's byte at word [k] of that tail and the line's byte at    *)
(*  word [S k] are the same byte of the same word -- twice                *)
(*  [LineWords.wl_line_word] and nothing else.  This used to be two       *)
(*  five-way case analyses over the literal's offsets.                    *)
(*                                                                       *)
(*  (The alternative continues past the tail with the prompt sh writes    *)
(*  once it has reaped, which is why the lookup needs the bound.)         *)
(* ===================================================================== *)
Lemma echo_alt0_word (k j : nat) (w : list (bv 8)) :
  echo_ws !! S k = Some w -> (j < length w)%nat ->
  line_alts !!! 0%nat !! (wl_off 0%nat (drop 1 echo_ws) k + j)%nat
  = Some (echo_line !!! (UkShEcho.echo_off (S k) + j)%nat).
Proof.
  intros Hw Hj.
  assert (Hd : drop 1 echo_ws !! k = Some w)
    by (rewrite lookup_drop; exact Hw).
  pose proof (wl_off_lt_line (drop 1 echo_ws) k w j Hd
                (Nat.lt_le_incl _ _ Hj)) as Hlt.
  rewrite line_alts_0 /echo_line_out.
  rewrite (lookup_app_l (wl_line (drop 1 echo_ws)) _ _ Hlt).
  destruct (lookup_lt_is_Some_2 (wl_line (drop 1 echo_ws))
              (wl_off 0%nat (drop 1 echo_ws) k + j)%nat Hlt) as [b Hb].
  rewrite Hb. f_equal.
  rewrite <- (list_lookup_total_correct _ _ _ Hb).
  rewrite (wl_line_word (drop 1 echo_ws) k w j Hd Hj).
  rewrite /UkShEcho.echo_off echo_line_words.
  by rewrite (wl_line_word echo_ws (S k) w j Hw Hj).
Qed.

(* ...at the two words echo prints.  The [6] is [UEchoOut.echo_out_argv]'s
   own reading of the alternative and is the last number here. *)
Lemma echo_alt0_tok1 (j : nat) :
  (j < UkShEcho.echo_alen 1%nat)%nat ->
  line_alts !!! 0%nat !! j
  = Some (echo_line !!! (UkShEcho.echo_off 1%nat + j)%nat).
Proof.
  intro Hj.
  pose proof (echo_alt0_word 0%nat j (echo_ws !!! 1%nat)
                (UkShEcho.echo_ws_at 1%nat ltac:(lia)) Hj) as H.
  rewrite wl_off_0 in H. exact H.
Qed.

Lemma echo_alt0_tok2 (j : nat) :
  (j < UkShEcho.echo_alen 2%nat)%nat ->
  line_alts !!! 0%nat !! (6 + j)%nat
  = Some (echo_line !!! (UkShEcho.echo_off 2%nat + j)%nat).
Proof.
  intro Hj.
  pose proof (echo_alt0_word 1%nat j (echo_ws !!! 2%nat)
                (UkShEcho.echo_ws_at 2%nat ltac:(lia)) Hj) as H.
  rewrite (_ : wl_off 0%nat (drop 1 echo_ws) 1%nat = 6%nat) in H;
    [exact H | by vm_compute].
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
