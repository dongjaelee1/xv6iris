(* ===================================================================== *)
(*  LineModel.v -- THE LINE MODEL, once (app-both milestone M1).           *)
(*                                                                       *)
(*  The three applications' expected-session transcripts                  *)
(*  ([EchoDisc.sess], [FileDisc.sessf], [PipeDisc.sessp]) are ONE fold:   *)
(*                                                                       *)
(*     prologue(ps) ++ concat (block i, i < nlines I) ++ rest_of I         *)
(*     block i := body_i ++ "\n" ++ cont (state_i) (line_i) (alt_i)       *)
(*               ++ (the next prologue round, at a MAIN-loop fork panic)  *)
(*                                                                       *)
(*  where the STATE is threaded through the blocks by the model's step    *)
(*  ([FileDisc.fsm] at the file; the identity at echo and at the          *)
(*  pipeline, whose state is [unit]).  What an application supplies is    *)
(*  the record below -- its lines, its alternatives with their code and   *)
(*  their panic bit, its continuation bytes at a state, its step -- and   *)
(*  everything the discipline, the claim families and the determinacy    *)
(*  argument read off the transcript is stated here over the record.      *)
(*                                                                       *)
(*  M1's exit: the three landed sessions are this fold at their instance *)
(*  ([LineModelInst.v]: [sessf_lm], [sessp_lm], [sess_lm]), so that the   *)
(*  generic families (M2) can be stated at [lm_sess] and every landed     *)
(*  statement recovered by rewriting with the equation.                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.        (* [bodies_of], [rest_of], [nlines], [nstarted], [wl_nl] *)
Require Import EchoDisc.         (* [pro_of], [pro_from], [pro_rounds], [pro_alts] *)
From stdpp Require Import ssreflect.

Local Open Scope nat_scope.

(* ====================================================================== *)
(*  1.  THE RECORD                                                         *)
(* ====================================================================== *)
Record lmodel := MkLM {
  (* the state a round leaves for the next: the file's content at the file
     application, [unit] where no line touches the file system *)
  lm_st : Type;
  (* the line, as a complete body parses to it -- total, at a default the
     discipline never lets happen ([FileDisc.uline_of]'s shape) *)
  lm_line : Type;
  lm_of : list (bv 8) -> lm_line;
  (* the alternatives that decide a round, DECODED from the stage's code
     ([cs !!! i]); the code is what the era's [cs_auth]/[cs_lb] carry *)
  lm_alt : Type;
  lm_dec : nat -> lm_alt;
  (* the MAIN-loop fork panic: the shell died, init restarts it, and the
     next prologue round follows the panic's bytes *)
  lm_panic : lm_alt -> bool;
  (* the continuation the console shows for the round, at the state the
     round starts in; and the state it leaves *)
  lm_cont : lm_st -> lm_line -> lm_alt -> list (bv 8);
  lm_step : lm_st -> lm_line -> lm_alt -> lm_st;
  (* which alternatives a line admits (the range condition the stage's
     choice list is checked against) *)
  lm_ok : lm_line -> lm_alt -> Prop;
  (* THE INPUT DISCIPLINE's two readings of a body: a complete body parses
     to an admissible line; a partial one is body bytes *)
  lm_body_ok : list (bv 8) -> Prop;
  lm_body_byte : bv 8 -> Prop;
}.

Section line_model.
  Context (M : lmodel).

  (* the round's alternative, read off the stage *)
  Definition lm_at (cs : list nat) (i : nat) : lm_alt M := lm_dec M (cs !!! i).

  (* THE ROUND POINTER: how many shells have died on their own main-loop
     fork panic before line [i] -- one prologue round each *)
  Fixpoint lm_pro_idx (cs : list nat) (i : nat) : nat :=
    match i with
    | 0 => 0
    | S i' => lm_pro_idx cs i' + if lm_panic M (lm_at cs i') then 1 else 0
    end.

  (* THE STATE BEFORE ROUND [q]: the boot state, moved by every round
     before it *)
  Fixpoint lm_upto (cs : list nat) (s : lm_st M) (bs : list (list (bv 8)))
      (q : nat) : lm_st M :=
    match q with
    | 0 => s
    | S q' => lm_step M (lm_upto cs s bs q') (lm_of M (bs !!! q')) (lm_at cs q')
    end.

  (* the console continuation of round [i], with the next prologue round
     after a panic *)
  Definition lm_cont_at (ps cs : list nat) (s : lm_st M)
      (bs : list (list (bv 8))) (i : nat) : list (bv 8) :=
    lm_cont M (lm_upto cs s bs i) (lm_of M (bs !!! i)) (lm_at cs i)
    ++ (if lm_panic M (lm_at cs i)
        then pro_of (pro_from (S (lm_pro_idx cs i)) ps) else []).

  (* the round's block: the echoed line, its newline, its continuation *)
  Definition lm_blk (ps cs : list nat) (s : lm_st M)
      (bs : list (list (bv 8))) (i : nat) : list (bv 8) :=
    bs !!! i ++ wl_nl :: lm_cont_at ps cs s bs i.

  Definition lm_seq (ps cs : list nat) (s : lm_st M)
      (bs : list (list (bv 8))) (q : nat) : list (bv 8) :=
    concat (lm_blk ps cs s bs <$> List.seq 0 q).

  (* THE EXPECTED SESSION TRANSCRIPT for the era's input [I] at boot
     state [s] *)
  Definition lm_sess (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) :=
    pro_of ps ++ lm_seq ps cs s (bodies_of I) (nlines I) ++ rest_of I.

  (* the state after the last COMPLETE line of [I] *)
  Definition lm_after (cs : list nat) (s : lm_st M) (I : list (bv 8))
    : lm_st M :=
    lm_upto cs s (bodies_of I) (nlines I).

  (* ---- the prologue's range and pin, as every instance states them ---- *)
  Definition lm_pro_ok (ps cs : list nat) (q : nat) : Prop :=
    Forall (fun a => a < length pro_alts) ps
    /\ lm_pro_idx cs q < pro_rounds ps.

  Definition lm_pro_pin (ps cs : list nat) (I : list (bv 8)) : Prop :=
    forall q, q < nstarted I -> lm_pro_idx cs q < pro_rounds ps.

  (* ---- the stage's range condition and the input discipline ---- *)
  Definition lm_alts_ok (I : list (bv 8)) (cs : list nat) : Prop :=
    Forall2 (fun l c => lm_ok M l (lm_dec M c)) (lm_of M <$> bodies_of I) cs.

  Definition lm_disc_input (I : list (bv 8)) : Prop :=
    Forall (lm_body_ok M) (bodies_of I)
    /\ Forall (lm_body_byte M) (rest_of I)
    /\ S (length (rest_of I)) < line_max.

  (* ---- THE STREAM the writer walks: what is pending after the input so
          far, and what was due before each byte of it ---- *)
  Definition lm_pending_at (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) :=
    if decide (I = []) then pro_of ps
    else if decide (rest_of I = [])
         then lm_cont_at ps cs s (bodies_of I) (nlines I - 1) else [].

  Fixpoint lm_proc_before_from (ps cs : list nat) (s : lm_st M)
      (pre I : list (bv 8)) : list (bv 8) :=
    match I with
    | [] => []
    | b :: I' => lm_pending_at ps cs s pre
                 ++ lm_proc_before_from ps cs s (pre ++ [b]) I'
    end.

  Definition lm_proc_before (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) := lm_proc_before_from ps cs s [] I.

  Definition lm_proc_stream (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) :=
    lm_proc_before ps cs s I ++ lm_pending_at ps cs s I.

  (* ---- THE WRITER'S STAGES, as every console family names them ---- *)
  Definition lm_wr_pro (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ (I = [] \/ lm_panic M (lm_at cs (nlines I - 1)) = true)
    /\ ~ pro_done (pro_from (lm_pro_idx cs (nlines I)) ps)
    /\ P = length (lm_proc_stream ps cs s I).

  Definition lm_wr_blk (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = S (length cs)
    /\ P = length (lm_proc_before ps cs s I).

  Definition lm_wr_open (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ lm_pro_idx cs (nlines I) < pro_rounds ps
    /\ P = length (lm_proc_stream ps cs s I).

  Definition lm_wr_owed (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_wr_pro ps cs s I P \/ lm_wr_blk ps cs s I P.

  Definition lm_wr_sp (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_wr_open ps cs s I (S P)
    /\ lm_proc_stream ps cs s I !! P = Some (u_prompt !!! 1).

  (* the banner-owed cursor stands after the OPEN round's [j] failed
     sub-rounds; the pre-bytes are the panic's when a line was typed *)
  Definition lm_wr_pre (I : list (bv 8)) : list (bv 8) :=
    if decide (I = []) then [] else alt_panic.

  Definition lm_wr_ban (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ (I = [] \/ lm_panic M (lm_at cs (nlines I - 1)) = true)
    /\ (exists j : nat,
          pro_from (lm_pro_idx cs (nlines I)) ps = pro_fail j
          /\ P = length (lm_proc_before ps cs s I) + length (lm_wr_pre I)
                 + pro_round * j).

  Definition lm_wr_tail (ps cs : list nat) : Prop :=
    pro_from (S (lm_pro_idx cs (length cs))) ps = [].

  Definition lm_wr_blk_t ps cs s I P : Prop := lm_wr_blk ps cs s I P /\ lm_wr_tail ps cs.
  Definition lm_wr_sp_t ps cs s I P : Prop := lm_wr_sp ps cs s I P /\ lm_wr_tail ps cs.
  Definition lm_wr_open_t ps cs s I P : Prop := lm_wr_open ps cs s I P /\ lm_wr_tail ps cs.

  Definition lm_wr_banp (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P i : nat) : Prop :=
    match i with
    | O => lm_wr_ban ps cs s I P
    | S _ => exists ps' : list nat, ps = ps' ++ [3] /\ lm_wr_ban ps' cs s I P
    end.

  (* the choice list of a block with [i] bytes out: the first byte files it *)
  Definition lm_blkcs (cs : list nat) (a i : nat) : list nat :=
    match i with O => cs | S _ => cs ++ [a] end.

  (* ---- structure ---- *)
  Lemma lm_seq_0 ps cs s bs : lm_seq ps cs s bs 0 = [].
  Proof using. reflexivity. Qed.

  Lemma lm_seq_S ps cs s bs q :
    lm_seq ps cs s bs (S q) = lm_seq ps cs s bs q ++ lm_blk ps cs s bs q.
  Proof using.
    rewrite /lm_seq seq_S fmap_app concat_app /=. by rewrite app_nil_r.
  Qed.

  Lemma lm_sess_nil ps cs s : lm_sess ps cs s [] = pro_of ps.
  Proof using.
    rewrite /lm_sess rest_of_nil nlines_nil lm_seq_0. by rewrite !app_nil_r.
  Qed.

  Lemma lm_pro_pin_of_ok ps cs I :
    lm_pro_ok ps cs (nlines I) -> lm_pro_pin ps cs I.
  Proof using.
    intros [_ Hlt] q Hq. rewrite /nstarted in Hq.
    (* the pointer is monotone in the index *)
    assert (Hmono : forall i j, i <= j -> lm_pro_idx cs i <= lm_pro_idx cs j).
    { intros i j Hij. induction Hij as [| j Hij IH]; [lia |].
      cbn [lm_pro_idx]. destruct (lm_panic M (lm_at cs j)); lia. }
    case_decide as Hr.
    - pose proof (Hmono q (nlines I) ltac:(lia)). lia.
    - destruct (decide (q < nlines I)) as [Hlt' | Hge].
      + pose proof (Hmono q (nlines I) ltac:(lia)). lia.
      + assert (q = nlines I) as -> by lia. exact Hlt.
  Qed.

End line_model.
