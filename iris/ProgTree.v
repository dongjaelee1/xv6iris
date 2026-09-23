(* ===================================================================== *)
(* ProgTree.v -- a user program's EXTERNALLY VISIBLE behaviour as an       *)
(* INTERACTION TREE, and a pure interpreter that runs such trees against   *)
(* a console, files and pipes.                                            *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md (PROPOSAL).  This file is  *)
(* the pure half of that proposal, built first so that the specs can be    *)
(* READ and RUN before anything in the logic depends on them:             *)
(*                                                                        *)
(*   - [ev] is the vocabulary of what a process does that the world can    *)
(*     see: open, close, read, write, exit.  A syscall the world cannot    *)
(*     see (sbrk, the argument copies of exec, ...) is not an event.       *)
(*   - [itree R] is the ordinary interaction tree (Xia et al., POPL 2020), *)
(*     defined here in twenty lines because the switch has no itree        *)
(*     library and nothing below needs bisimulation: a program is a tree   *)
(*     that never returns ([proc := itree Empty_set]), and the theorems     *)
(*     about it are about its INTERPRETATIONS.                            *)
(*   - [echo_tree] and [cat_tree] are the two programs' specs: a function   *)
(*     from argv to the tree.  Each is at SYSCALL GRANULARITY -- one        *)
(*     [EWrite] per [write] the C makes, so xv6's [fprintf] (one write per  *)
(*     byte, user/printf.c [putc]) is a run of one-byte writes -- because   *)
(*     the granularity is observable when two processes share the console. *)
(*   - [run] interprets ONE process against a world under a deterministic  *)
(*     schedule, with fuel; [run_pipe] runs a two-process pipeline left     *)
(*     child first.  Both exist for the demos at the end (every line shape  *)
(*     the union application states, computed by [vm_compute]) and as the  *)
(*     pure reading the line model's continuations should be derived from. *)
(*     The general statement quantifies over schedules; the sequential one  *)
(*     is a valid schedule for every pipeline whose left output fits the    *)
(*     pipe (PIPESIZE = 512), which the line discipline guarantees.         *)
(*                                                                        *)
(* NOTHING IMPORTS THIS FILE.  It sits beside [LineWords] and above         *)
(* [StringBytes] only.                                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import StringBytes LineWords.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition bytes := list (bv 8).
Definition sb (s : string) : bytes := string_bytes s.

(* ===================================================================== *)
(*  1.  EVENTS                                                            *)
(* ===================================================================== *)

(* what a read answers: the kernel's -1, or the bytes it delivered ([] is
   end of file) *)
Inductive rd_ans := RdErr | RdBytes (bs : bytes).

Inductive ev : Type -> Type :=
  | EOpen  (path : bytes) (omode : Z) : ev Z      (* the descriptor, or -1 *)
  | EClose (fd : Z) : ev Z
  | ERead  (fd : Z) (n : nat) : ev rd_ans           (* at most [n] bytes *)
  | EWrite (fd : Z) (bs : bytes) : ev Z             (* the count written, or -1 *)
  | EExit  (status : Z) : ev Empty_set.

(* ===================================================================== *)
(*  2.  THE TREE                                                          *)
(* ===================================================================== *)

CoInductive itree (R : Type) : Type :=
  | Ret (r : R)
  | Tau (t : itree R)
  | Vis {X : Type} (e : ev X) (k : X -> itree R).
Arguments Ret {R}.
Arguments Tau {R}.
Arguments Vis {R X}.

Definition trigger {X : Type} (e : ev X) : itree X := Vis e (fun x => Ret x).

CoFixpoint bind {R S : Type} (t : itree R) (f : R -> itree S) : itree S :=
  match t with
  | Ret r => f r
  | Tau t' => Tau (bind t' f)
  | Vis e k => Vis e (fun x => bind (k x) f)
  end.

Notation "x <- t ;; f" := (bind t (fun x => f))
  (at level 62, t at next level, right associativity).
Notation "t ;;; f" := (bind t (fun _ => f))
  (at level 62, right associativity).

(* the loop: [step] answers [inl] (again, at this state) or [inr] (done) *)
CoFixpoint iter_ {I R : Type} (step : I -> itree (I + R)) (t : itree (I + R))
    : itree R :=
  match t with
  | Ret (inl i) => Tau (iter_ step (step i))
  | Ret (inr r) => Ret r
  | Tau t' => Tau (iter_ step t')
  | Vis e k => Vis e (fun x => iter_ step (k x))
  end.
Definition iter {I R : Type} (step : I -> itree (I + R)) (i : I) : itree R :=
  iter_ step (step i).

(* a process never returns: its tree ends only in [EExit] *)
Definition proc := itree Empty_set.
Definition exit_ {R : Type} (status : Z) : itree R :=
  Vis (EExit status) (fun v => match v with end).

(* the [observe] of the itree library: forces one step of a cofixpoint *)
Definition force {R : Type} (t : itree R) : itree R :=
  match t with Ret r => Ret r | Tau t' => Tau t' | Vis e k => Vis e k end.
Lemma force_eq {R : Type} (t : itree R) : t = force t.
Proof. destruct t; reflexivity. Qed.

(* ===================================================================== *)
(*  3.  THE PROGRAMS                                                      *)
(* ===================================================================== *)

(* [fprintf]: one write per byte (user/printf.c, [putc]) *)
Fixpoint write_bytes (fd : Z) (bs : bytes) : itree unit :=
  match bs with
  | [] => Ret tt
  | b :: r => trigger (EWrite fd [b]) ;;; write_bytes fd r
  end.

(* --- echo -------------------------------------------------------------
     for (i = 1; i < argc; i++) {
       write(1, argv[i], strlen(argv[i]));
       write(1, i + 1 < argc ? SPACE : NEWLINE, 1);
     }
     exit(0);
   The return of [write] is ignored. *)
Fixpoint echo_words (ws : list bytes) : itree unit :=
  match ws with
  | [] => Ret tt
  | [w] => trigger (EWrite 1 w) ;;; trigger (EWrite 1 [wl_nl]) ;;; Ret tt
  | w :: r => trigger (EWrite 1 w) ;;; trigger (EWrite 1 [wl_sp]) ;;; echo_words r
  end.

Definition echo_tree (argv : list bytes) : proc :=
  echo_words (drop 1 argv) ;;; exit_ 0.

(* --- cat --------------------------------------------------------------
     cat(fd):  while ((n = read(fd, buf, 512)) > 0)
                 if (write(1, buf, n) != n) { fprintf(2, cat: write error); exit(1); }
               if (n < 0) { fprintf(2, cat: read error); exit(1); }
     main:     if (argc <= 1) { cat(0); exit(0); }
               for (i = 1; i < argc; i++) {
                 if ((fd = open(argv[i], O_RDONLY)) < 0) {
                   fprintf(2, cat: cannot open %s, argv[i]); exit(1); }
                 cat(fd); close(fd); }
               exit(0);                                                   *)
Definition cat_bufsz : nat := 512.

Definition cat_fd (fd : Z) : itree unit :=
  iter (fun (_ : unit) =>
          a <- trigger (ERead fd cat_bufsz) ;;
          match a with
          | RdErr => write_bytes 2 (sb "cat: read error" ++ [wl_nl]) ;;; exit_ 1
          | RdBytes [] => Ret (inr tt)
          | RdBytes bs =>
              r <- trigger (EWrite 1 bs) ;;
              if decide (r = Z.of_nat (length bs)) then Ret (inl tt)
              else write_bytes 2 (sb "cat: write error" ++ [wl_nl]) ;;; exit_ 1
          end) tt.

Fixpoint cat_files (paths : list bytes) : itree unit :=
  match paths with
  | [] => Ret tt
  | p :: r =>
      fd <- trigger (EOpen p 0) ;;
      if decide (fd < 0)
      then write_bytes 2 (sb "cat: cannot open " ++ p ++ [wl_nl]) ;;; exit_ 1
      else cat_fd fd ;;; trigger (EClose fd) ;;; cat_files r
  end.

Definition cat_tree (argv : list bytes) : proc :=
  match drop 1 argv with
  | [] => cat_fd 0 ;;; exit_ 0
  | paths => cat_files paths ;;; exit_ 0
  end.

(* ===================================================================== *)
(*  4.  A WORLD, AND ONE PROCESS RUN AGAINST IT                           *)
(*                                                                        *)
(*  The endpoints a descriptor can name.  The shell's job at a line is to  *)
(*  build the table ([fdt]) -- that IS a line shape -- and nothing in a    *)
(*  program's tree depends on which endpoint a number names.               *)
(* ===================================================================== *)

Record pipe_st := MkPipe {
  p_buf : bytes;        (* written, not yet read *)
  p_wopen : bool;       (* a writer still holds the write end *)
}.

Inductive endpoint :=
  | EpCons
  | EpFile (name : bytes) (off : nat)
  | EpPipeW (p : nat)
  | EpPipeR (p : nat).

Record world := MkW {
  w_cin : bytes;                       (* what the console has to deliver *)
  w_cons : bytes;                      (* what the console has shown *)
  w_files : list (bytes * bytes);      (* name, content *)
  w_pipes : list (nat * pipe_st);
}.

Definition fdt := list (Z * endpoint).

Definition assoc_get {K V : Type} `{EqDecision K} (l : list (K * V)) (k : K)
    : option V :=
  match list_find (fun kv => kv.1 = k) l with
  | Some (_, kv) => Some kv.2
  | None => None
  end.
Definition assoc_set {K V : Type} `{EqDecision K} (l : list (K * V)) (k : K)
    (v : V) : list (K * V) :=
  (k, v) :: filter (fun kv => kv.1 <> k) l.
Definition assoc_del {K V : Type} `{EqDecision K} (l : list (K * V)) (k : K)
    : list (K * V) :=
  filter (fun kv => kv.1 <> k) l.

Definition file_get (w : world) (n : bytes) : option bytes := assoc_get (w_files w) n.
Definition file_set (w : world) (n : bytes) (c : bytes) : world :=
  MkW (w_cin w) (w_cons w) (assoc_set (w_files w) n c) (w_pipes w).
Definition pipe_get (w : world) (p : nat) : option pipe_st := assoc_get (w_pipes w) p.
Definition pipe_set (w : world) (p : nat) (s : pipe_st) : world :=
  MkW (w_cin w) (w_cons w) (w_files w) (assoc_set (w_pipes w) p s).
Definition cons_put (w : world) (bs : bytes) : world :=
  MkW (w_cin w) (w_cons w ++ bs) (w_files w) (w_pipes w).
Definition cons_take (w : world) (n : nat) : world * bytes :=
  (MkW (drop n (w_cin w)) (w_cons w) (w_files w) (w_pipes w), take n (w_cin w)).

(* the lowest descriptor not in the table (xv6's [fdalloc]) *)
Fixpoint lowest_free (t : fdt) (fd : Z) (fuel : nat) : Z :=
  match fuel with
  | O => fd
  | S f => match assoc_get t fd with None => fd | Some _ => lowest_free t (fd + 1) f end
  end.

(* O_CREATE = 0x200, O_TRUNC = 0x400 (kernel/fcntl.h) *)
Definition om_create (m : Z) : bool := bool_decide (Z.land m 0x200 <> 0).
Definition om_trunc  (m : Z) : bool := bool_decide (Z.land m 0x400 <> 0).

(* THE KERNEL'S ANSWER TO ONE EVENT, deterministically: the GOOD
   answers.  Where the kernel may answer otherwise (a present file whose
   [filealloc] fails, a pipe write whose reader has gone), the real
   theorem quantifies over the answer; the interpreter picks one. *)
Definition step_open (w : world) (t : fdt) (path : bytes) (m : Z)
    : world * fdt * Z :=
  match file_get w path, om_create m with
  | None, false => (w, t, -1)
  | None, true =>
      let fd := lowest_free t 0 16 in
      (file_set w path [], assoc_set t fd (EpFile path 0), fd)
  | Some c, _ =>
      let fd := lowest_free t 0 16 in
      let w' := if om_trunc m then file_set w path [] else w in
      (w', assoc_set t fd (EpFile path 0), fd)
  end.

Definition step_close (w : world) (t : fdt) (fd : Z) : world * fdt * Z :=
  match assoc_get t fd with
  | None => (w, t, -1)
  | Some (EpPipeW p) =>
      (* the last writer closing is what makes the reader's EOF; one writer
         per pipe end in every line here *)
      let w' := match pipe_get w p with
                | Some s => pipe_set w p (MkPipe (p_buf s) false)
                | None => w
                end in
      (w', assoc_del t fd, 0)
  | Some _ => (w, assoc_del t fd, 0)
  end.

(* what a process's exit does to the world: its descriptors close *)
Fixpoint close_all (w : world) (t : fdt) (fds : list Z) : world :=
  match fds with
  | [] => w
  | fd :: r => close_all (step_close w t fd).1.1 t r
  end.
Definition step_exit (w : world) (t : fdt) : world :=
  close_all w t (map fst t).

Definition step_read (w : world) (t : fdt) (fd : Z) (n : nat)
    : world * fdt * rd_ans :=
  match assoc_get t fd with
  | None => (w, t, RdErr)
  | Some EpCons => let '(w', bs) := cons_take w n in (w', t, RdBytes bs)
  | Some (EpFile name off) =>
      match file_get w name with
      | None => (w, t, RdErr)
      | Some c =>
          let bs := take n (drop off c) in
          (w, assoc_set t fd (EpFile name (off + length bs)), RdBytes bs)
      end
  | Some (EpPipeW _) => (w, t, RdErr)
  | Some (EpPipeR p) =>
      match pipe_get w p with
      | None => (w, t, RdErr)
      | Some s =>
          let bs := take n (p_buf s) in
          (pipe_set w p (MkPipe (drop n (p_buf s)) (p_wopen s)), t, RdBytes bs)
          (* an empty buffer with the writer open would BLOCK; under the
             left-first schedule it never happens *)
      end
  end.

Definition step_write (w : world) (t : fdt) (fd : Z) (bs : bytes)
    : world * fdt * Z :=
  match assoc_get t fd with
  | None => (w, t, -1)
  | Some EpCons => (cons_put w bs, t, Z.of_nat (length bs))
  | Some (EpFile name off) =>
      match file_get w name with
      | None => (w, t, -1)
      | Some c =>
          (* xv6 has no O_APPEND: the write lands at the descriptor's offset *)
          let c' := take off c ++ bs ++ drop (off + length bs) c in
          (file_set w name c', assoc_set t fd (EpFile name (off + length bs)),
           Z.of_nat (length bs))
      end
  | Some (EpPipeW p) =>
      match pipe_get w p with
      | None => (w, t, -1)
      | Some s => (pipe_set w p (MkPipe (p_buf s ++ bs) (p_wopen s)), t,
                   Z.of_nat (length bs))
      end
  | Some (EpPipeR _) => (w, t, -1)
  end.

Inductive outcome := Exited (status : Z) | OutOfFuel.

(* ONE PROCESS, to its exit *)
Fixpoint run (fuel : nat) (w : world) (t : fdt) (p : proc) : world * outcome :=
  match fuel with
  | O => (w, OutOfFuel)
  | S fuel' =>
      match force p with
      | Ret v => match v with end
      | Tau p' => run fuel' w t p'
      | Vis e k =>
          match e in ev X return (X -> proc) -> world * outcome with
          | EOpen path m => fun k =>
              let '(w', t', r) := step_open w t path m in run fuel' w' t' (k r)
          | EClose fd => fun k =>
              let '(w', t', r) := step_close w t fd in run fuel' w' t' (k r)
          | ERead fd n => fun k =>
              let '(w', t', a) := step_read w t fd n in run fuel' w' t' (k a)
          | EWrite fd bs => fun k =>
              let '(w', t', r) := step_write w t fd bs in run fuel' w' t' (k r)
          | EExit s => fun _ => (step_exit w t, Exited s)
          end k
      end
  end.

(* ===================================================================== *)
(*  5.  THE LINE SHAPES, as the shell provisions them                     *)
(* ===================================================================== *)

(* enough steps for every demo; a [nat] literal above 5000 warns *)
Definition fuel : nat := 100 * 100.

Definition std_console : fdt := [(0, EpCons); (1, EpCons); (2, EpCons)].

(* `cmd args`: the console on 0, 1, 2 *)
Definition line_plain (w : world) (p : proc) : world * outcome :=
  run fuel w std_console p.

(* `cmd args > f`: sh does close(1); open(f, O_WRONLY|O_CREATE|O_TRUNC) *)
Definition line_redirect (w : world) (f : bytes) (p : proc) : world * outcome :=
  let '(w', t', _) := step_open w (assoc_del std_console 1) f (0x1 + 0x200 + 0x400) in
  run fuel w' t' p.

(* `l | r`: sh does pipe(); the left child close(1); dup(w); the right
   close(0); dup(r); each closes both pipe ends it did not dup.  The left
   child runs first -- a valid schedule when its output fits the pipe. *)
Definition line_pipe (w : world) (l r : proc) : world * outcome :=
  let pid := 0%nat in
  let w0 := pipe_set w pid (MkPipe [] true) in
  let tl := assoc_set std_console 1 (EpPipeW pid) in
  let tr := assoc_set std_console 0 (EpPipeR pid) in
  let '(w1, _) := run fuel w0 tl l in
  run fuel w1 tr r.

(* ===================================================================== *)
(*  6.  DEMOS: what each line shows on the console, by computation        *)
(* ===================================================================== *)

Definition w0 : world := MkW [] [] [] [].
Definition argv_echo (ws : list string) : list bytes := sb "echo" :: map sb ws.
Definition argv_cat (ws : list string) : list bytes := sb "cat" :: map sb ws.

(* echo foo bar *)
Example demo_echo :
  (line_plain w0 (echo_tree (argv_echo ["foo"; "bar"]))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* ...and it is exactly the line model's block for the good alternative *)
Example demo_echo_is_wl_line :
  (line_plain w0 (echo_tree (argv_echo ["foo"; "bar"]))).1.(w_cons)
  = wl_line (drop 1 (argv_echo ["foo"; "bar"])).
Proof. vm_compute. reflexivity. Qed.

(* echo foo bar > f : nothing on the console; f holds the line *)
Definition after_redirect : world :=
  (line_redirect w0 (sb "f") (echo_tree (argv_echo ["foo"; "bar"]))).1.
Example demo_redirect_cons : w_cons after_redirect = [].
Proof. vm_compute. reflexivity. Qed.
Example demo_redirect_file : file_get after_redirect (sb "f") = Some (sb "foo bar" ++ [wl_nl]).
Proof. vm_compute. reflexivity. Qed.

(* cat f, after the redirect: the line comes back *)
Example demo_cat_f :
  (line_plain after_redirect (cat_tree (argv_cat ["f"]))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* cat g, absent: the diagnostic on fd 2 = the console, status 1 *)
Example demo_cat_absent :
  let '(w, o) := line_plain after_redirect (cat_tree (argv_cat ["g"])) in
  w_cons w = sb "cat: cannot open g" ++ [wl_nl] /\ o = Exited 1.
Proof. vm_compute. split; reflexivity. Qed.

(* cat f g: the content, THEN the diagnostic -- the order across fd 1 and
   fd 2 is the tree's, which a per-descriptor stream spec cannot say *)
Example demo_cat_f_then_absent :
  (line_plain after_redirect (cat_tree (argv_cat ["f"; "g"]))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl] ++ sb "cat: cannot open g" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* echo foo | cat *)
Example demo_pipe :
  (line_pipe w0 (echo_tree (argv_echo ["foo"])) (cat_tree (argv_cat []))).1.(w_cons)
  = sb "foo" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* cat f | cat *)
Example demo_cat_pipe_cat :
  (line_pipe after_redirect (cat_tree (argv_cat ["f"])) (cat_tree (argv_cat []))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* cat f > g, then cat g: the file copied through the held offset *)
Example demo_cat_redirect :
  let w1 := (line_redirect after_redirect (sb "g") (cat_tree (argv_cat ["f"]))).1 in
  w_cons w1 = [] /\ file_get w1 (sb "g") = Some (sb "foo bar" ++ [wl_nl]).
Proof. vm_compute. split; reflexivity. Qed.

(* chunking: a file longer than cat's buffer is copied in two reads and
   two writes, and the stream is still the content *)
Definition long_content : bytes := replicate 700 (Z_to_bv 8 97).
Definition w_long : world := file_set w0 (sb "big") long_content.
Example demo_cat_long :
  (line_plain w_long (cat_tree (argv_cat ["big"]))).1.(w_cons) = long_content.
Proof. vm_compute. reflexivity. Qed.

(* cat with no argument reads the console's input to end of file *)
Example demo_cat_stdin :
  let w := MkW (sb "typed" ++ [wl_nl]) [] [] [] in
  (line_plain w (cat_tree (argv_cat []))).1.(w_cons) = sb "typed" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* A NEGATIVE ONE: the interpreter is not a constant function of its input *)
Example demo_negative :
  (line_plain w0 (echo_tree (argv_echo ["foo"]))).1.(w_cons)
  <> (line_plain w0 (echo_tree (argv_echo ["bar"]))).1.(w_cons).
Proof. vm_compute. discriminate. Qed.
