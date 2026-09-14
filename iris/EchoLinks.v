(* ===================================================================== *)
(*  EchoLinks.v -- THE CONSOLE LINKS AS ONE PERSISTENT LAW                *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM: DESIGN OF RECORD";        *)
(*   lane IO-LEAF, decision D1.)                                          *)
(*                                                                       *)
(*  [EchoOut]'s five links are stated under the boot record's four        *)
(*  equations ([riscv_out_res = eout] and its three siblings), which the  *)
(*  top theorem fixes and no PROGRAM file may name: the U tier sits below *)
(*  the record and knows nothing about which application it is running.   *)
(*  So the links travel to the programs the way the write DEPOSIT does    *)
(*  today ([UkSh.sh_deps], [UkInit.init_deps]) -- as ONE PERSISTENT       *)
(*  RESOURCE a program takes as a premise and spends per byte:            *)
(*                                                                       *)
(*    [echo_links T γ] -- the six links as closed [□] wands, mentioning   *)
(*      the era's ghosts ([era_pin], [turn], [ps_lb], [cs_lb], [E_lb],    *)
(*      [dl_cnt], [read_ret]) and the kernel's own console contracts      *)
(*      ([WpUart.out_link] / [read_link]) and NOTHING of the record;      *)
(*    [echo_links_holds] -- the entailment, proved where the equations    *)
(*      are in scope, i.e. exactly where [UInitBoot.echo_Hinit_boot]      *)
(*      already has them.                                                *)
(*                                                                       *)
(*  WHY A FILE OF ITS OWN and not a section of [EchoOut.v]: the law is a  *)
(*  PROGRAM-side interface and it changes with the programs, while        *)
(*  [EchoOut.v] is the claim.  A sibling file also keeps the two lanes    *)
(*  that touch them apart.                                               *)
(*                                                                       *)
(*  THE BUNDLE IS NOT CLOSED, and the six PROJECTIONS below are what      *)
(*  every consumer goes through, so a seventh link costs the consumers    *)
(*  nothing -- the fifth, [echo_link_pro] (PROLOGUE-ALTS-2's choice       *)
(*  byte), and the sixth, [echo_link_rd_taint] (lane IO-LEAF, M5),        *)
(*  arrived exactly that way.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import TsoCtx.
Require Import EchoOut.
(* as in EchoDisc / EchoOutPure / EchoOut: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.


(* ===================================================================== *)
(*  THE WRITER'S PLACE AT A LINE BOUNDARY (lane IO-LEAF, M6a)            *)
(*                                                                       *)
(*  The era's write credential ([EchoOut.turn] and the two lower bounds) *)
(*  travels on the console lease, and the lease is handed on at a LINE   *)
(*  BOUNDARY -- a delivered count [n] that is a multiple of the line's   *)
(*  seventeen bytes.  What a holder of it may do there is not a function *)
(*  of [n]: the stage [P] the writer stands at depends on which          *)
(*  alternatives the transcript has taken, and the prologue rounds [ps]  *)
(*  are free.  So the credential quantifies [ps], [cs] and [P] and pins  *)
(*  them with ONE of the three PURE shapes below.                        *)
(*                                                                       *)
(*    [wr_pro]   the round's PROLOGUE alternative is still open: the     *)
(*               next byte out is the round's choice byte, and for the   *)
(*               shell that byte is the '$' of its prompt                *)
(*               ([EchoDisc.pro_alts !!! 0]).  Round 0 at [n = 0] is     *)
(*               this shape, with [ps = []], [cs = []] and [P = 18].     *)
(*    [wr_blk]   the round is settled and the LINE just echoed still     *)
(*               owes its block: the next byte out is that block's       *)
(*               first ([EchoDisc.line_alts !!! a]), and a shell whose   *)
(*               child recorded no choice writes its prompt there        *)
(*               ([line_alts !!! 2]).                                    *)
(*    [wr_open]  both are written: the writer stands at the start of the *)
(*               block the NEXT line will owe and can write nothing      *)
(*               until the count moves ([E_lb] is what forbids it).      *)
(*                                                                       *)
(*  The two prompt shapes are [wr_owed]; the shell's "$ " takes either   *)
(*  of them to [wr_open], and the read takes [wr_open] at [n] back to    *)
(*  [wr_blk] at [n + 17].  Those three steps are all the arithmetic the  *)
(*  shell's command loop needs.                                         *)
(* ===================================================================== *)

Definition wr_pro (ps cs : list nat) (n P : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat)
  /\ ~ pro_done (pro_from (pro_idx cs (n `div` length echo_line)) ps)
  /\ P = length (proc_upto ps cs (S n)).

Definition wr_blk (ps cs : list nat) (n P : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = S (length cs)
  /\ P = length (proc_upto ps cs n).

Definition wr_open (ps cs : list nat) (n P : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (pro_idx cs (n `div` length echo_line) < pro_rounds ps)%nat
  /\ P = length (proc_upto ps cs (S n)).

Definition wr_owed (ps cs : list nat) (n P : nat) : Prop :=
  wr_pro ps cs n P \/ wr_blk ps cs n P.

(* ...AND THE HALF-WRITTEN PROMPT: the choice byte is out, the space is
   not, and what says so is that the round's stream is exactly one byte
   longer than the writer's cursor and that that byte is the space. *)
Definition wr_sp (ps cs : list nat) (n P : nat) : Prop :=
  wr_open ps cs n (S P)
  /\ proc_upto ps cs (S n) !! P = Some (u_prompt !!! 1%nat).

(* ---- the literals, by computation ---- *)
Lemma wr_prompt_len : length u_prompt = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wr_pro_alts_0 : pro_alts !!! 0%nat = u_prompt.
Proof. reflexivity. Qed.

Lemma wr_line_alts_2 : line_alts !!! 2%nat = u_prompt.
Proof. reflexivity. Qed.

Lemma wr_prompt_head : u_prompt !! 0%nat = Some (u_prompt !!! 0%nat).
Proof. vm_compute. reflexivity. Qed.

Lemma wr_prompt_tail : u_prompt !! 1%nat = Some (u_prompt !!! 1%nat).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  THE PROLOGUE GROWS BY EXACTLY ITS ALTERNATIVE.  [pro_of_snoc_head]   *)
(*  gives the prefix; the shell needs the LENGTH, because that is what   *)
(*  pins the stage its second prompt byte is written at.                 *)
(* ===================================================================== *)
Lemma pro_of_open_snoc_eq (ps : list nat) (a : nat) :
  ~ pro_done ps -> a <> 1%nat ->
  pro_of (ps ++ [a]) = pro_of ps ++ pro_alts !!! a.
Proof.
  intros Hnd Ha. induction ps as [| c ps IH]; cbn [pro_of app].
  - rewrite (pro_more_ne a (pro_of [])); [| exact Ha].
    by rewrite app_nil_r.
  - assert (Hc1 : c = 1%nat).
    { destruct (decide (c = 1%nat)) as [? | Hne]; [done |].
      exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left. }
    subst c. rewrite !pro_more_1.
    rewrite IH; last first.
    { intros H. apply Hnd. rewrite /pro_done Exists_cons. by right. }
    by rewrite !app_assoc.
Qed.

(* ...AND THE BLOCK AT A ROUND'S HEAD ENDS IN THAT PROLOGUE, whether the
   round is the transcript's first ([n = 0], the block IS the prologue) or
   one a shell's fork panic opened ([cs !!! (q-1) = 3], the block is that
   alternative and then the prologue).  The PREFIX does not read [ps] at
   all, which is what makes the choice byte's effect a pure append. *)
Lemma pending_n_round_shape (ps cs : list nat) (n : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  exists pre : list (bv 8),
    forall ps' : list nat,
      pending_n ps' cs n
      = pre ++ pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps').
Proof.
  intros Hm Hr. pose proof echo_line_length as HL.
  destruct (decide (n = 0%nat)) as [Hz | Hn0].
  - exists []. intros ps'. rewrite /pending_n. case_decide as H0; [| done].
    rewrite Hz Nat.Div0.div_0_l. by cbn [pro_idx pro_from app].
  - assert (Hq : (1 <= n `div` length echo_line)%nat).
    { destruct (decide (n `div` length echo_line = 0)%nat) as [Hd | Hd];
        [| lia].
      exfalso. pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
      rewrite Hd Hm in Hdm. lia. }
    destruct Hr as [Hr | Hr]; [done |].
    assert (Hs : pro_idx cs (n `div` length echo_line)
                 = S (pro_idx cs (n `div` length echo_line - 1)%nat)).
    { rewrite <- (pro_idx_S3 cs (n `div` length echo_line - 1)%nat Hr).
      f_equal. lia. }
    exists (line_alts !!! 3%nat). intros ps'.
    rewrite /pending_n. case_decide as H0; [done |].
    case_decide as Hm2; [| done].
    rewrite /alt_cont Hr. case_decide as H3; [| done].
    by rewrite Hs.
Qed.

(* THE CHOICE BYTE'S EFFECT ON THE ROUND'S BLOCK, as a pure append. *)
Lemma pending_n_round_snoc (ps cs : list nat) (n a : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  ~ pro_done (pro_from (pro_idx cs (n `div` length echo_line)) ps) ->
  a <> 1%nat ->
  (pro_idx cs (n `div` length echo_line) <= pro_rounds ps)%nat ->
  pending_n (ps ++ [a]) cs n = pending_n ps cs n ++ pro_alts !!! a.
Proof.
  intros Hm Hr Hnd Ha Hle.
  destruct (pending_n_round_shape ps cs n Hm Hr) as [pre Hpre].
  rewrite !Hpre.
  rewrite (pro_from_snoc_le (pro_idx cs (n `div` length echo_line)) ps a Hle).
  rewrite (pro_of_open_snoc_eq _ a Hnd Ha).
  by rewrite app_assoc.
Qed.


(* ===================================================================== *)
(*  THE ROUND'S BANNER, STILL OWED (lane IO-LEAF, M6a(2)).               *)
(*                                                                       *)
(*  [wr_pro] is where the round's CHOICE byte goes, and eighteen bytes    *)
(*  before it stands /init, owing the round's banner.  That is the shape  *)
(*  the console lease carries between a child's exit and the fork that    *)
(*  follows it -- /init's own loop head -- and the one thing it needs     *)
(*  beyond [wr_pro]'s side conditions is WHICH open prologue it is in:    *)
(*  [j] failed sub-rounds, so the banner starts [pro_round * j] bytes     *)
(*  into the round's block.  [EchoOut.proc_upto_round_banner_open]        *)
(*  (PROLOGUE-ALTS-2) is what reads the bytes off it.                     *)
(* ===================================================================== *)
Definition wr_pre (cs : list nat) (n : nat) : list (bv 8) :=
  if decide (n = 0%nat) then [] else line_alts !!! 3%nat.

Definition wr_ban (ps cs : list nat) (n P : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat)
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps = replicate j 1%nat
        /\ P = (length (proc_upto ps cs n) + length (wr_pre cs n)
                + pro_round * j)%nat).

Lemma pro_of_replicate_length (j : nat) :
  length (pro_of (replicate j 1%nat))
  = (pro_round * j + length u_banner)%nat.
Proof.
  assert (Hb : length u_banner = 18%nat) by (vm_compute; reflexivity).
  assert (He : length u_execfail = 21%nat) by (vm_compute; reflexivity).
  assert (Ha : length (pro_alts !!! 1%nat) = 21%nat)
    by (vm_compute; reflexivity).
  assert (Hr : pro_round = 39%nat) by (vm_compute; reflexivity).
  induction j as [| j IH].
  - cbn [replicate pro_of]. lia.
  - replace (replicate (S j) 1%nat) with (1%nat :: replicate j 1%nat)
      by reflexivity.
    change (pro_of (1%nat :: replicate j 1%nat))
      with (u_banner ++ pro_alts !!! 1%nat
            ++ pro_more 1%nat (pro_of (replicate j 1%nat))).
    rewrite pro_more_1 (length_app u_banner)
            (length_app (pro_alts !!! 1%nat)) IH. lia.
Qed.

Lemma pro_done_replicate (j : nat) : ~ pro_done (replicate j 1%nat).
Proof.
  rewrite /pro_done Exists_exists. intros (a & Ha & Hne).
  apply elem_of_list_In, elem_of_replicate in Ha. by destruct Ha as [-> _].
Qed.

(* THE BANNER IS THE LAST EIGHTEEN BYTES OF THE ROUND'S BLOCK, so an
   /init standing at its head is a [wr_pro] eighteen bytes on. *)
Lemma wr_ban_pro (ps cs : list nat) (n P : nat) :
  wr_ban ps cs n P -> wr_pro ps cs n (P + length u_banner)%nat.
Proof.
  intros (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
  rewrite /wr_pro. split_and!; try assumption.
  - rewrite Hopen. exact (pro_done_replicate j).
  - rewrite proc_upto_snoc length_app.
    rewrite (pending_n_round_pre ps cs n Hm Hr) length_app.
    rewrite Hopen pro_of_replicate_length HP /wr_pre. lia.
Qed.

Lemma wr_ban_byte (ps cs : list nat) (n P i : nat) (b : bv 8) :
  wr_ban ps cs n P -> u_banner !! i = Some b ->
  proc_upto ps cs (S n) !! (P + i)%nat = Some b.
Proof.
  intros (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)) Hb.
  rewrite HP /wr_pre.
  exact (proc_upto_round_banner_open ps cs n j i b Hm Hr Hopen Hb).
Qed.

Lemma wr_ban_round0 : wr_ban [] [] 0%nat 0%nat.
Proof.
  rewrite /wr_ban. split_and!.
  - intros q Hq. lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - by left.
  - exists 0%nat. split; [ by vm_compute | by vm_compute ].
Qed.

(* ---- a run of blocks that owe nothing leaves the stream alone ---- *)
Lemma proc_upto_gap (ps cs : list nat) (n d : nat) :
  (forall j, (n <= j)%nat -> (j < n + d)%nat -> pending_n ps cs j = []) ->
  proc_upto ps cs (n + d) = proc_upto ps cs n.
Proof.
  induction d as [| d IH]; intros Hj.
  - by rewrite Nat.add_0_r.
  - replace (n + S d)%nat with (S (n + d))%nat by lia.
    rewrite proc_upto_snoc (Hj (n + d)%nat ltac:(lia) ltac:(lia)) app_nil_r.
    apply IH. intros j H1 H2. apply Hj; lia.
Qed.

Lemma pro_rounds_one : pro_rounds [0%nat] = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  THE THREE STEPS.                                                     *)
(* ===================================================================== *)

(* (1) THE ROUND'S CHOICE BYTE, at an open prologue: filing alternative 0 *)
(*     appends the prompt's two bytes to the round's block, so the        *)
(*     writer's cursor is one short of a stream two longer.               *)
Lemma wr_pro_dollar (ps cs : list nat) (n P : nat) :
  wr_pro ps cs n P -> wr_sp (ps ++ [0%nat]) cs n (S P).
Proof.
  intros (Hpin & Hm & Hdv & Hr & Hnd & HP).
  pose proof echo_line_length as HL.
  assert (Hle : (pro_idx cs (n `div` length echo_line) <= pro_rounds ps)%nat)
    by exact (pro_pin_idx_le ps cs n Hpin).
  assert (Hpre : ps `prefix_of` (ps ++ [0%nat])) by by eexists.
  (* the stream, byte for byte *)
  assert (Hlow : proc_upto (ps ++ [0%nat]) cs n = proc_upto ps cs n).
  { symmetry. rewrite /proc_upto. apply proc_upto_from_ext.
    intros j _ Hj. apply (pending_n_ps_ext ps (ps ++ [0%nat]) cs j Hpre).
    apply (pro_pin_at ps cs n j Hpin). lia. }
  assert (Hup : proc_upto (ps ++ [0%nat]) cs (S n)
                = proc_upto ps cs (S n) ++ u_prompt).
  { rewrite !proc_upto_snoc Hlow.
    rewrite (pending_n_round_snoc ps cs n 0%nat Hm Hr Hnd
               ltac:(lia) Hle) wr_pro_alts_0.
    by rewrite app_assoc. }
  assert (Hlen : length (proc_upto (ps ++ [0%nat]) cs (S n)) = S (S P)).
  { rewrite Hup length_app wr_prompt_len. lia. }
  split.
  - rewrite /wr_open. split_and!.
    + exact (pro_pin_mono ps (ps ++ [0%nat]) cs n Hpre Hpin).
    + exact Hm.
    + exact Hdv.
    + rewrite pro_rounds_app pro_rounds_one. lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (proc_upto ps cs (S n)))%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.

(* (2) THE LINE'S CHOICE BYTE, at a settled round whose last line still    *)
(*     owes its block: filing alternative 2 -- the child recorded no       *)
(*     choice -- makes the block the prompt itself.                        *)
Lemma wr_blk_dollar (ps cs : list nat) (n P : nat) :
  wr_blk ps cs n P -> wr_sp ps (cs ++ [2%nat]) n (S P).
Proof.
  intros (Hpin & Hm & Hdv & HP).
  pose proof echo_line_length as HL.
  assert (Hn17 : n = (length echo_line * S (length cs))%nat).
  { pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
    rewrite Hdv in Hdm. lia. }
  assert (Hn : (length echo_line <= n)%nat) by nia.
  assert (Hpre : cs `prefix_of` (cs ++ [2%nat])) by by eexists.
  assert (Hnew : (cs ++ [2%nat]) !!! length cs = 2%nat).
  { rewrite list_lookup_total_alt lookup_app_r; [| lia].
    by rewrite Nat.sub_diag. }
  assert (Hold : forall j, (j < length cs)%nat ->
                   (cs ++ [2%nat]) !!! j = cs !!! j)
    by (intros j Hj; exact (lookup_total_prefix cs (cs ++ [2%nat]) j Hpre Hj)).
  assert (Hidx : forall j, (j <= length cs)%nat ->
                   pro_idx (cs ++ [2%nat]) j = pro_idx cs j).
  { apply (pro_idx_ext (cs ++ [2%nat]) cs (length cs)).
    intros j Hj. exact (Hold j Hj). }
  (* the stream below [n] does not read the new choice *)
  assert (Hlow : proc_upto ps (cs ++ [2%nat]) n = proc_upto ps cs n).
  { symmetry.
    apply (proc_upto_cs_prefix_pred ps ps cs (cs ++ [2%nat]) n
             ltac:(reflexivity) Hpre Hpin).
    assert (Hd1 : ((n - 1) `div` length echo_line)%nat = length cs).
    { symmetry. apply (Nat.div_unique (n - 1) (length echo_line)
                         (length cs) (length echo_line - 1)%nat); nia. }
    rewrite Hd1. lia. }
  assert (Hpend : pending_n ps (cs ++ [2%nat]) n = u_prompt).
  { rewrite /pending_n. case_decide as H0; [ exfalso; lia |].
    case_decide as Hm2; [| done].
    rewrite /alt_cont.
    replace (n `div` length echo_line - 1)%nat with (length cs) by lia.
    rewrite Hnew. case_decide as H3; [ exfalso; lia |].
    by rewrite wr_line_alts_2 app_nil_r. }
  assert (Hup : proc_upto ps (cs ++ [2%nat]) (S n)
                = proc_upto ps cs n ++ u_prompt)
    by (rewrite proc_upto_snoc Hlow Hpend; reflexivity).
  assert (Hlen : length (proc_upto ps (cs ++ [2%nat]) (S n)) = S (S P)).
  { rewrite Hup length_app wr_prompt_len. lia. }
  split.
  - rewrite /wr_open. split_and!.
    + intros q Hq'. rewrite (Hidx q ltac:(nia)). exact (Hpin q Hq').
    + exact Hm.
    + rewrite length_app Hdv. cbn [length]. lia.
    + rewrite Hdv pro_idx_S Hnew. case_decide as H3; [ exfalso; lia |].
      rewrite (Hidx (length cs) ltac:(lia)).
      assert (Hlt : (length echo_line * (length cs) < n)%nat) by nia.
      pose proof (Hpin (length cs) Hlt). lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (proc_upto ps cs n))%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.

(* (3) THE SPACE, and the state it leaves: the second prompt byte is the   *)
(*     last of the round's block, so the cursor lands exactly on the       *)
(*     stream's end -- [wr_open].                                          *)
Lemma wr_sp_open (ps cs : list nat) (n P : nat) :
  wr_sp ps cs n P -> wr_open ps cs n (S P).
Proof. by intros [H _]. Qed.

(* (4) THE READ: seventeen echoed bytes later the transcript owes that     *)
(*     line's block and nothing has been written, so the cursor has not    *)
(*     moved and the shape is [wr_blk].                                    *)
Lemma wr_open_read (ps cs : list nat) (n P : nat) :
  wr_open ps cs n P -> wr_blk ps cs (n + length echo_line)%nat P.
Proof.
  intros (Hpin & Hm & Hdv & Hrd & HP).
  pose proof echo_line_length as HL.
  assert (Hn17 : n = (length echo_line * (n `div` length echo_line))%nat).
  { pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm. lia. }
  assert (Hsum : (n + length echo_line)%nat
                 = (length echo_line * S (n `div` length echo_line))%nat)
    by lia.
  rewrite /wr_blk. split_and!.
  - intros q Hq.
    destruct (decide (q < n `div` length echo_line)%nat) as [Hlt | Hge].
    + apply Hpin. nia.
    + assert (Hqe : q = (n `div` length echo_line)%nat) by nia.
      rewrite Hqe. exact Hrd.
  - rewrite Hsum Nat.mul_comm. apply Nat.Div0.mod_mul.
  - rewrite Hsum Nat.mul_comm Nat.div_mul; [| lia]. by rewrite Hdv.
  - rewrite HP.
    replace (n + length echo_line)%nat with (S n + (length echo_line - 1))%nat
      by lia.
    f_equal. symmetry. apply proc_upto_gap. intros j H1 H2.
    rewrite /pending_n. case_decide as H0; [ exfalso; lia |].
    case_decide as Hm2; [| done]. exfalso.
    assert (Hji : j = (n + (j - n))%nat) by lia.
    rewrite Hji -Nat.Div0.add_mod_idemp_l Hm Nat.add_0_l in Hm2.
    rewrite Nat.mod_small in Hm2; lia.
Qed.

Section echo_links.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* ------------------------------------------------------------------ *)
  (*  THE LAW.  Each conjunct is [EchoOut]'s link with its Coq-level      *)
  (*  premises turned into [⌜⌝] wands, so that the whole thing is one     *)
  (*  [iProp] a program can hold; each is a CLOSED entailment under the   *)
  (*  equations, hence intuitionistic, hence persistent.                  *)
  (* ------------------------------------------------------------------ *)
  Definition echo_link_w : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜((n0 `div` length echo_line) <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜proc_upto ps0 cs0 (S n0) !! P = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition echo_link_blk : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜(0 < n0)%nat⌝ -∗
        ⌜(n0 `mod` length echo_line)%nat = 0%nat⌝ -∗
        ⌜((n0 `div` length echo_line) <= S (length cs0))%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜P = length (proc_upto ps0 cs0 n0)⌝ -∗
        ⌜(a < length line_alts)%nat⌝ -∗
        ⌜line_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (W'') THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE, the
     block-first link's twin one level up: the writer that resolves the
     round's alternative (init after an exec failure or a fork failure,
     sh after its [fork1] panic) files the INDEX and the bound that comes
     back has grown by one -- in [ps], not in [cs]. *)
  Definition echo_link_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜(n0 `mod` length echo_line)%nat = 0%nat⌝ -∗
        ⌜n0 = 0%nat \/ cs0 !!! (n0 `div` length echo_line - 1)%nat = 3%nat⌝ -∗
        ⌜((n0 `div` length echo_line) <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜~ pro_done (pro_from (pro_idx cs0 (n0 `div` length echo_line)) ps0)⌝ -∗
        ⌜P = length (proc_upto ps0 cs0 (S n0))⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ E_lb v n0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* THE TAINT ROUTE, and it is not a convenience: every per-byte loop
     invariant of a program tower is [<the era's cursor> ∨ T], so the
     TAINT arm of byte [i] has to produce byte [i+1]'s link on its own. *)
  Definition echo_link_taint : iProp Σ :=
    (□ ∀ (k : nat) (b : bv 8) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  Definition echo_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        era_pin γ k v -∗ dl_cnt v (1/2) n -∗
        (read_ret T k v n ws -∗ Φ) -∗
        read_link k ws Φ)%I.

  (* THE READ SIDE'S TAINT ROUTE, [echo_link_taint]'s twin and needed for
     the same reason (lane IO-LEAF, M5): what sh's lease carries is the
     era's delivered-count half OR the taint, and on the taint arm the
     read must still be able to move the boundary's [dl].
     [EchoOut.ein_sup_deliv] is exactly that move, and it is the READ half
     of what [App.Happ_in_sup] gives the licence route. *)
  Definition echo_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ read_link k ws Φ)%I.

  Definition echo_links : iProp Σ :=
    (echo_link_w ∗ echo_link_blk ∗ echo_link_pro ∗ echo_link_taint
     ∗ echo_link_rd ∗ echo_link_rd_taint)%I.

  Global Instance echo_link_w_persistent : Persistent echo_link_w.
  Proof. rewrite /echo_link_w. apply _. Qed.
  Global Instance echo_link_blk_persistent : Persistent echo_link_blk.
  Proof. rewrite /echo_link_blk. apply _. Qed.
  Global Instance echo_link_pro_persistent : Persistent echo_link_pro.
  Proof. rewrite /echo_link_pro. apply _. Qed.
  Global Instance echo_link_taint_persistent : Persistent echo_link_taint.
  Proof. rewrite /echo_link_taint. apply _. Qed.
  Global Instance echo_link_rd_persistent : Persistent echo_link_rd.
  Proof. rewrite /echo_link_rd. apply _. Qed.
  Global Instance echo_link_rd_taint_persistent : Persistent echo_link_rd_taint.
  Proof. rewrite /echo_link_rd_taint. apply _. Qed.
  Global Instance echo_links_persistent : Persistent echo_links.
  Proof. rewrite /echo_links. apply _. Qed.

  (* ---- the five projections, which is all a consumer ever uses ---- *)
  Lemma echo_links_w : echo_links -∗ echo_link_w.
  Proof. by iIntros "($ & _ & _ & _ & _ & _)". Qed.
  Lemma echo_links_blk : echo_links -∗ echo_link_blk.
  Proof. by iIntros "(_ & $ & _ & _ & _ & _)". Qed.
  Lemma echo_links_pro : echo_links -∗ echo_link_pro.
  Proof. by iIntros "(_ & _ & $ & _ & _ & _)". Qed.
  Lemma echo_links_taint : echo_links -∗ echo_link_taint.
  Proof. by iIntros "(_ & _ & _ & $ & _ & _)". Qed.
  Lemma echo_links_rd : echo_links -∗ echo_link_rd.
  Proof. by iIntros "(_ & _ & _ & _ & $ & _)". Qed.
  Lemma echo_links_rd_taint : echo_links -∗ echo_link_rd_taint.
  Proof. by iIntros "(_ & _ & _ & _ & _ & $)". Qed.

  (* =================================================================== *)
  (*  THE ERA'S WRITE CREDENTIAL AT A LINE BOUNDARY (lane IO-LEAF, M6a)   *)
  (*                                                                     *)
  (*  What the console lease carries besides the reader's half of the     *)
  (*  delivered count: the era's cursor, the two lower bounds and the     *)
  (*  pure shape that says where the cursor stands.  OR THE TAINT, for    *)
  (*  every other credential's reason -- a tainted era owes no transcript *)
  (*  and the lease's holder proves nothing about the wire.               *)
  (* =================================================================== *)
  Definition ewc_owed (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_owed ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Definition ewc_sp (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_sp ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Definition ewc_open (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_open ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Global Instance ewc_owed_timeless v n : Timeless (ewc_owed v n).
  Proof. rewrite /ewc_owed. apply _. Qed.
  Global Instance ewc_sp_timeless v n : Timeless (ewc_sp v n).
  Proof. rewrite /ewc_sp. apply _. Qed.
  Global Instance ewc_open_timeless v n : Timeless (ewc_open v n).
  Proof. rewrite /ewc_open. apply _. Qed.

  Lemma ewc_owed_taint v n : T -∗ ewc_owed v n.
  Proof. iIntros "HT". rewrite /ewc_owed. by iRight. Qed.
  Lemma ewc_open_taint v n : T -∗ ewc_open v n.
  Proof. iIntros "HT". rewrite /ewc_open. by iRight. Qed.

  (* ...AND THE THREE AS ONE FAMILY, indexed by how many of the shell's two
     prompt bytes are out (lane IO-LEAF, M6a(1)/M6a(3)): [0] the boundary
     itself, [1] the '$' written, [2] the whole prompt written.  What the
     shell's command loop carries beside its cursor is this at [0], what
     its prompt leaves is this at [2], and the read of the next line takes
     [2] at [n] back to [0] at [n + 17] ([ewc_read]). *)
  Definition ewc_pr (v : era_pins) (n : nat) (p : nat) : iProp Σ :=
    match p with
    | O => ewc_owed v n
    | S O => ewc_sp v n
    | _ => ewc_open v n
    end.

  Global Instance ewc_pr_timeless v n p : Timeless (ewc_pr v n p).
  Proof. rewrite /ewc_pr. destruct p as [| [| p]]; apply _. Qed.

  (* ...WITH THE ERA'S PIN BESIDE IT, which is the shape a program below
     the application holds: the shell's loop names no [v], so the pin
     travels inside and every step re-reads it ([EchoOut.era_pin_agree]). *)
  Definition ewc_cred (k : nat) (n p : nat) : iProp Σ :=
    (∃ v : era_pins, era_pin γ k v ∗ ewc_pr v n p)%I.

  Global Instance ewc_cred_timeless k n p : Timeless (ewc_cred k n p).
  Proof. rewrite /ewc_cred. apply _. Qed.

  (* ...AND THE ONE PLACE THE CREDENTIAL IS BORN: round 0, at count 0,
     with no round and no line resolved and the writer eighteen banner
     bytes in.  [UInitBanner] is what supplies it. *)
  Lemma wr_owed_round0 : wr_owed [] [] 0%nat 18%nat.
  Proof.
    left. rewrite /wr_pro. split_and!.
    - intros q Hq. lia.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - by left.
    - vm_compute. intro H. inversion H.
    - vm_compute. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  /INIT'S BANNER, AT AN ARBITRARY ROUND (lane IO-LEAF, M6a(2)).       *)
  (*                                                                     *)
  (*  The credential at [wr_ban] with [i] of the banner's eighteen bytes  *)
  (*  already out.  Every byte is an ORDINARY write -- the round's choice *)
  (*  is still open and the banner is the tail of the block the open      *)
  (*  prologue already owes -- so the whole walk is [echo_link_w], and    *)
  (*  what it ends at is [wr_pro]: the prompt's own shape.  That is how   *)
  (*  the credential gets from /init's loop head to the shell it forks,   *)
  (*  round 0 and every restart alike.                                    *)
  (* =================================================================== *)
  Definition ewc_ban (v : era_pins) (n : nat) (i : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_ban ps cs n P⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Global Instance ewc_ban_timeless v n i : Timeless (ewc_ban v n i).
  Proof. rewrite /ewc_ban. apply _. Qed.

  Lemma ewc_ban_taint v n i : T -∗ ewc_ban v n i.
  Proof. iIntros "HT". rewrite /ewc_ban. by iRight. Qed.

  Lemma echo_banner_step (k : nat) (v : era_pins) (n i : nat) (b : bv 8)
      (Φ : iProp Σ) :
    u_banner !! i = Some b ->
    era_pin γ k v -∗ echo_links -∗ ewc_ban v n i -∗
    (ewc_ban v n (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_ban. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (wr_ban_byte ps cs n P i b Hw Hb) as Hby.
    pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
    iApply ("Hw" $! k v (P + i)%nat n b ps cs Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { exact Hby. }
    iIntros "Hres". iApply "HΦ".
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, P.
    replace (P + S i)%nat with (S (P + i))%nat by lia.
    iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
  Qed.

  (* ...AND WHAT THE EIGHTEENTH BYTE LEAVES: the prompt's own credential
     at the same count, which is what /init lends the shell. *)
  Lemma ewc_ban_done (v : era_pins) (n : nat) :
    ewc_ban v n (length u_banner) -∗ ewc_owed v n.
  Proof.
    rewrite /ewc_ban /ewc_owed.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. left.
    exact (wr_ban_pro ps cs n P Hw).
  Qed.

  (* =================================================================== *)
  (*  THE SHELL'S PROMPT, BYTE BY BYTE, AT EITHER SHAPE.                  *)
  (*                                                                     *)
  (*  The '$' RESOLVES something in both cases -- the round's prologue    *)
  (*  alternative ([echo_link_pro] at [a = 0]) when the round is still    *)
  (*  open, the LINE's block ([echo_link_blk] at [a = 2] -- the child     *)
  (*  recorded no choice) when it is not -- and the [ ] after it is an    *)
  (*  ordinary byte of what the first one fixed ([echo_link_w]).  So the  *)
  (*  shell's walk spends ONE pair of steps at every prompt it prints,    *)
  (*  round 0's and every later one alike.                                *)
  (* =================================================================== *)
  Lemma echo_prompt_dollar (k : nat) (v : era_pins) (n : nat) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links -∗ ewc_owed v n -∗ (ewc_sp v n -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_blk with "Hlk") as "#Hblk".
    iDestruct (echo_links_pro with "Hlk") as "#Hpro".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_owed. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /ewc_sp. by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hhd : pro_alts !!! 0%nat !! 0%nat = Some b)
      by (rewrite wr_pro_alts_0 Hb; exact wr_prompt_head).
    assert (Hhd2 : line_alts !!! 2%nat !! 0%nat = Some b)
      by (rewrite wr_line_alts_2 Hb; exact wr_prompt_head).
    destruct Hw as [Hw | Hw].
    - (* the round's prologue is open: the '$' files alternative 0 *)
      pose proof (wr_pro_dollar ps cs n P Hw) as Hsp.
      destruct Hw as (Hpin & Hm & Hdv & Hr & Hnd & HP).
      iApply ("Hpro" $! k v P n 0%nat b ps cs Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { vm_compute. lia. }
      { exact Hhd. }
      iIntros "Hres". iApply "HΦ". rewrite /ewc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [0%nat]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
    - (* the round is settled: the '$' is the line's block, alternative 2 *)
      pose proof (wr_blk_dollar ps cs n P Hw) as Hsp.
      destruct Hw as (Hpin & Hm & Hdv & HP).
      pose proof echo_line_length as HL.
      assert (Hpos : (0 < n)%nat).
      { destruct (decide (n = 0%nat)) as [Hz | Hne]; [| lia].
        rewrite Hz Nat.Div0.div_0_l in Hdv. lia. }
      iApply ("Hblk" $! k v P n 2%nat b ps cs Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hpos. }
      { exact Hm. }
      { lia. }
      { exact Hpin. }
      { exact HP. }
      { vm_compute. lia. }
      { exact Hhd2. }
      iIntros "Hres". iApply "HΦ". rewrite /ewc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, (cs ++ [2%nat]), (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
  Qed.

  Lemma echo_prompt_space (k : nat) (v : era_pins) (n : nat) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    era_pin γ k v -∗ echo_links -∗ ewc_sp v n -∗ (ewc_open v n -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_sp. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /ewc_open. by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [Hop Hby].
    pose proof Hop as (Hpin & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v P n b ps cs Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /ewc_open.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    by iPureIntro.
  Qed.

  (* ...AND WHAT A LINE'S READ DOES TO IT: nothing at all to the cursor
     ([EchoOut.pcount_echo]), and everything to the shape -- the line just
     echoed owes its block, so the credential is back at [wr_blk] and the
     next prompt is that block's first byte.  The fresh bound comes off the
     read's own receipt ([EchoOut.read_ret]). *)
  Lemma ewc_read (v : era_pins) (n : nat) :
    E_lb v (n + length echo_line)%nat -∗ ewc_open v n -∗
    ewc_owed v (n + length echo_line)%nat.
  Proof.
    iIntros "#HE' Hc". rewrite /ewc_open /ewc_owed.
    iDestruct "Hc" as "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE'".
    iPureIntro. right. exact (wr_open_read ps cs n P Hw).
  Qed.

  (* ================================================================== *)
  (*  ...AND THE LAW HOLDS, under the record's four equations.  This is  *)
  (*  the one place in the arc where the application's claims and the    *)
  (*  kernel's console contracts are the same object, and it is exactly  *)
  (*  where [UInitBoot.echo_Hinit_boot] already stands.                  *)
  (* ================================================================== *)
  Section echo_links_holds.
    Context (Hout : @riscv_out_res Σ (@riscv_fixedGS Σ HRg) = eout T γ).
    Context (Hin : @riscv_in_res Σ (@riscv_fixedGS Σ HRg) = ein T γ).
    Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = etag T).
    Context (Hwin : @riscv_win_res Σ (@riscv_fixedGS Σ HRg) = ewin T γ).

    Lemma echo_links_holds : ⊢ echo_links.
    Proof.
      rewrite /echo_links /echo_link_w /echo_link_blk /echo_link_pro
              /echo_link_taint /echo_link_rd /echo_link_rd_taint.
      iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit]]]].
      - iIntros "!>" (k v P n0 b ps0 cs0 Φ) "%Hdiv %Hpin0 %Hb".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k v P n0 a b ps0 cs0 Φ).
        iIntros "%Hpos %Hmod %Hdiv %Hpin0 %HPeq %Halt %Hhead".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link_blk with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k v P n0 a b ps0 cs0 Φ).
        iIntros "%Hmod %Hpr %Hdiv %Hpin0 %Hnd %HPeq %Halt %Hhead".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link_pro with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k b Φ) "HT HΦ".
        iApply (echo_write_link_taint T γ with "HT HΦ"); try assumption.
      - iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
        iApply (echo_read_link with "Hpin Hdl HΦ"); try assumption.
      - iIntros "!>" (k ws Φ) "#HT HΦ".
        iIntros (o pops dl) "#Hlb Hres _".
        rewrite /in_res_at Hin.
        iMod (ein_sup_deliv T γ k (default [] o) pops dl ws
                with "HT Hres") as "Hres".
        iModIntro. iExists o. iFrame "Hlb Hres". by iApply "HΦ".
    Qed.
  End echo_links_holds.

End echo_links.
