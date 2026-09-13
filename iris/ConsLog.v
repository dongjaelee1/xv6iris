(* ConsLog: the console UART's accepted-input log, the pure vocabulary of
   E5's boundary contract (claude-notes/projects/app-echo.md, "E5 -- THE
   CONSOLE I/O CLAIM").  An entry is (h, c, cs): the history the byte was
   received at (obs_ends_in Uart0 h c), the byte, and what the kernel put on
   the wire for it.  Nothing of the kernel's ring is here. *)

(* ---------------------------------------------------------------------- *)
(*  THE DEFINITIONS BELOW ARE THE COORDINATOR'S CANONICAL TEXT (names,     *)
(*  argument order, clause order) and are shared with lane CONS-IO, which  *)
(*  writes this same file in another checkout; the coordinator merges.     *)
(*  ANY LEMMA GOES BELOW THEM.  [echo_of] and [cons_erase] MOVE here from  *)
(*  SpecConsoleintr.v (CONS-IO makes that file import this one and deletes  *)
(*  its copies); this file never mentions SpecConsoleintr.                 *)
(* ---------------------------------------------------------------------- *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
(* the Sail machine-word vocabulary [echo_of]/[cons_erase] are spelled in
   ([mword], [eq_vec], [mword_of_int]); the same four lines ConsoleInv.v
   takes for [cons_xlate]. *)
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.        (* [mobs], [Uart0] (via DevModel) *)
Require Import ObsTrace.         (* [obs_ends_in], [hist_ext] *)
(* after the imports, before any definition -- the Sail imports leave
   string_scope on top and `++` would elaborate as String.append (CONS-IO, F1) *)
Local Open Scope list_scope.

Definition echo_of (c : bv 8) : bv 8 :=
  if eq_vec (c : mword 8) (mword_of_int 13 : mword 8)
  then (mword_of_int 10 : mword 8) else c.

Definition cons_erase (c : bv 8) : bool :=
  eq_vec (c : mword 8) (mword_of_int 21 : mword 8)
  || eq_vec (c : mword 8) (mword_of_int 8 : mword 8)
  || eq_vec (c : mword 8) (mword_of_int 127 : mword 8).

(* MOVED here from SpecConsputc.v:118 (CONS-IO makes SpecConsputc import
   ConsLog and deletes its copy): the BACKSPACE arm's three bytes *)
Definition consputc_bs : list (bv 8) :=
  [(mword_of_int 8 : mword 8); (mword_of_int 32 : mword 8);
   (mword_of_int 8 : mword 8)].

(* MOVED here from SpecConsoleintr.v:169 (ruling on CONS-IO's F10): the
   shape of what one consoleintr call echoes for [c], per arm *)
Definition cons_echo (c : bv 8) (cs : list (bv 8)) : Prop :=
  cs = [] \/ cs = [echo_of c]
  \/ (cons_erase c = true /\ exists n : nat, cs = mjoin (replicate n consputc_bs)).

Definition log_entry : Type := (list mobs * bv 8 * list (bv 8))%type.
Definition le_hist (e : log_entry) : list mobs := e.1.1.
Definition le_byte (e : log_entry) : bv 8 := e.1.2.
Definition le_echo (e : log_entry) : list (bv 8) := e.2.

(* the entries a read hands out: the echoed ones *)
Definition log_echoed (e : log_entry) : Prop := le_echo e = [echo_of (le_byte e)].

(* consecutive histories strictly increase *)
Definition hist_chain (l : list (list mobs * bv 8)) : Prop :=
  forall i h1 c1 h2 c2,
    l !! i = Some (h1, c1) -> l !! S i = Some (h2, c2) -> hist_ext h1 h2.

(* THE GAP CLAUSE: between two consecutive delivered inputs, every logged
   input either got no echo, or an erase character was logged in (h1, h2]. *)
Definition gap_ok (pops : list log_entry) (h1 h2 : list mobs) : Prop :=
  (forall e, e ∈ pops -> hist_ext h1 (le_hist e) -> hist_ext (le_hist e) h2 ->
             le_echo e = [])
  \/ (exists e, e ∈ pops /\ hist_ext h1 (le_hist e)
                /\ (le_hist e = h2 \/ hist_ext (le_hist e) h2)
                /\ cons_erase (le_byte e) = true).

(* the kernel's pure fact at a read: [ws] delivered after [dl] *)
Definition read_ok (pops : list log_entry) (dl ws : list (list mobs * bv 8)) : Prop :=
  (forall p, p ∈ ws -> exists e, e ∈ pops /\ (le_hist e, le_byte e) = p /\ log_echoed e)
  /\ hist_chain (dl ++ ws)
  /\ (forall h c, (dl ++ ws) !! 0%nat = Some (h, c) -> gap_ok pops [] h)
  /\ (forall i h1 c1 h2 c2,
        (dl ++ ws) !! i = Some (h1, c1) -> (dl ++ ws) !! S i = Some (h2, c2) ->
        gap_ok pops h1 h2).

(* the log is in arrival order and every entry is an input *)
Definition log_ok (pops : list log_entry) : Prop :=
  (forall e, e ∈ pops -> obs_ends_in Uart0 (le_hist e) (le_byte e)
                         /\ cons_echo (le_byte e) (le_echo e))
  /\ (forall i e1 e2, pops !! i = Some e1 -> pops !! S i = Some e2 ->
                     hist_ext (le_hist e1) (le_hist e2)).

(* ====================================================================== *)
(*  LEMMAS (below the canonical definitions, as the merge protocol asks)   *)
(* ====================================================================== *)

(* [log_echoed] is a list equality, so a filter may be taken over it *)
Global Instance log_echoed_dec (e : log_entry) : Decision (log_echoed e).
Proof. unfold log_echoed. apply _. Defined.

(* an echoed entry has a nonempty echo -- the one step that turns the gap
   clause's left disjunct into "not an echoed entry" *)
Lemma log_echoed_nonnil (e : log_entry) : log_echoed e -> le_echo e <> [].
Proof. unfold log_echoed. intros ->. discriminate. Qed.

(* the log's order is transitive, not merely consecutive *)
Lemma log_ok_lt (pops : list log_entry) (i j : nat) (e1 e2 : log_entry) :
  log_ok pops -> (i < j)%nat ->
  pops !! i = Some e1 -> pops !! j = Some e2 -> hist_ext (le_hist e1) (le_hist e2).
Proof.
  intros [_ Hstep] Hij. revert e2. induction Hij as [|j Hij IH]; intros e2 H1 H2.
  - by eapply Hstep.
  - destruct (pops !! j) as [e|] eqn:Hj.
    + eapply hist_ext_trans; [by apply IH | by eapply Hstep].
    + exfalso. apply lookup_ge_None_1 in Hj.
      apply lookup_lt_Some in H2. lia.
Qed.

(* ...and so is a read window's, which is the same fact at [hist_chain]'s
   pair shape *)
Lemma hist_chain_lt (l : list (list mobs * bv 8)) (i j : nat)
      (h1 : list mobs) (c1 : bv 8) (h2 : list mobs) (c2 : bv 8) :
  hist_chain l -> (i < j)%nat ->
  l !! i = Some (h1, c1) -> l !! j = Some (h2, c2) -> hist_ext h1 h2.
Proof.
  intros Hchain Hij. revert h2 c2. induction Hij as [|j Hij IH]; intros h2 c2 H1 H2.
  - by eapply Hchain.
  - destruct (l !! j) as [[hm cm]|] eqn:Hj.
    + eapply hist_ext_trans; [by apply (IH hm cm) | by eapply Hchain].
    + exfalso. apply lookup_ge_None_1 in Hj.
      apply lookup_lt_Some in H2. lia.
Qed.
