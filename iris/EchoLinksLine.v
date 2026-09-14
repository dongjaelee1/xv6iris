(* ===================================================================== *)
(*  EchoLinksLine.v -- THE ERA'S WRITE CREDENTIAL ACROSS ONE TURN OF THE  *)
(*  SHELL'S COMMAND LOOP WHEN A CHILD RUNS, AND ACROSS THE SHELL'S OWN    *)
(*  FORK PANIC (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane          *)
(*  SH-LINE-CRED, the lemmas M3b core wires into the walk).               *)
(*                                                                       *)
(*  [EchoLinks] carries the credential from a line boundary through the   *)
(*  shell's prompt and the line's read: [ewc_owed] --'$'--> [ewc_sp]      *)
(*  --' '--> [ewc_open] --read--> [ewc_owed] at [n + 17].  What is        *)
(*  missing is everything a CHILD does between that read and the next     *)
(*  prompt, and what the shell does when its fork fails:                  *)
(*                                                                       *)
(*    [ewc_blk v n a i]   alternative [a] of the line's block chosen, [i]  *)
(*                        of its bytes out ([i = 0]: nothing chosen yet;  *)
(*                        the first byte files the choice, exactly as     *)
(*                        echo's first byte does in [UEchoOut.ech]);      *)
(*    [ewc_post v n a]    the block written up to its last two bytes --   *)
(*                        the "$ " every line alternative but the panic   *)
(*                        ends in, which the SHELL writes after [wait];   *)
(*    [ewc_panic v n i]   [ewc_blk] at [a = 3]: "fork\n", the shell's own *)
(*                        panic line, whose end is the BANNER of a fresh  *)
(*                        prologue round ([EchoLinks.wr_ban] at [j = 0]). *)
(*                                                                       *)
(*  ONE FAMILY, [ewc_blk], carries all three: the child's run, the exec   *)
(*  failure's diagnostic, and the panic are the same walk at different    *)
(*  [a].  The prompt after a child is then two steps at [ewc_post], and   *)
(*  the loop's boundary credential is WIDENED to [ewc_line]: the round's  *)
(*  open prologue ([wr_pro], round 0 and every restart) OR a line block   *)
(*  written up to its prompt ([ewc_post] at some [a < 3]; [a = 2] is the  *)
(*  child that recorded no choice, i.e. [ewc_owed]'s [wr_blk] arm         *)
(*  itself).  [ewc_lpr]/[ewc_lcred] are [EchoLinks.ewc_pr]/[ewc_cred] at  *)
(*  that widened boundary, so the shell's [Wc] can be instantiated here   *)
(*  and nothing in [UkSh] changes (review-m6a3.md, Finding 2).            *)
(*                                                                       *)
(*  THE ONE SHAPE [EchoLinks] GETS WRONG for these steps -- not missing,  *)
(*  loose: [wr_open]/[wr_blk] record only [pro_idx cs q < pro_rounds ps],  *)
(*  "the round this block is in has settled", which ADMITS a writer whose *)
(*  own lower bound [ps] has already resolved a round that has not        *)
(*  opened.  The shell's panic opens round [S (pro_idx cs (length cs))]   *)
(*  and [wr_ban] wants that round's resolution to be [replicate j 1] with *)
(*  [j = 0] -- i.e. EMPTY -- which the loose shape cannot give.  The      *)
(*  claim's own invariant ([EchoOut.ps_len_ok] (A): nothing is filed for  *)
(*  a round that has not opened) says it is empty; the credential's pure  *)
(*  shape has to say so too.  So every shape here carries [wr_tail]:      *)
(*                                                                       *)
(*    [wr_tail ps cs := pro_from (S (pro_idx cs (length cs))) ps = []]     *)
(*                                                                       *)
(*  ([wr_pro] already pins it: its [~ pro_done] arm settles the round     *)
(*  exactly at the choice byte, [wr_pro_tail]).  The tight shapes are     *)
(*  [wr_blk_t]/[wr_sp_t]/[wr_open_t]; the loose ones are implied          *)
(*  ([ewc_sp_t_sp], [ewc_open_t_open]) and never needed again.            *)
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
Require Import EchoLinks.
(* as in EchoDisc / EchoOutPure / EchoOut / EchoLinks: the Sail imports
   leave string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.


(* ===================================================================== *)
(*  S0  THE LITERALS, BY COMPUTATION.  Every fact below is closed: the    *)
(*  alternative index is destructed into its three (or four) cases first. *)
(* ===================================================================== *)
Lemma line_alts_len0 : length (line_alts !!! 0%nat) = 14%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma line_alts_len1 : length (line_alts !!! 1%nat) = 19%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma line_alts_len2_ : length (line_alts !!! 2%nat) = 2%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma line_alts_len3 : length (line_alts !!! 3%nat) = 5%nat.
Proof. vm_compute. reflexivity. Qed.

(* the panic line does NOT end in the prompt: "fork\n", five bytes, the
   last of them the newline *)
Lemma line_alts_3_bytes : line_alts !!! 3%nat = sb "fork"%string ++ nlb.
Proof. reflexivity. Qed.

(* every line alternative but the panic is at least the prompt long *)
Lemma line_alts_len_ge2 (a : nat) :
  (a < 3)%nat -> (2 <= length (line_alts !!! a))%nat.
Proof.
  intros Ha. destruct a as [| [| [| a]]].
  - rewrite line_alts_len0. lia.
  - rewrite line_alts_len1. lia.
  - rewrite line_alts_len2_. lia.
  - exfalso. lia.
Qed.

(* ...and its last two bytes ARE the prompt *)
Lemma line_alts_dollar (a : nat) :
  (a < 3)%nat ->
  line_alts !!! a !! (length (line_alts !!! a) - 2)%nat
  = Some (u_prompt !!! 0%nat).
Proof.
  intros Ha. destruct a as [| [| [| a]]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exfalso. lia.
Qed.

Lemma line_alts_space (a : nat) :
  (a < 3)%nat ->
  line_alts !!! a !! (length (line_alts !!! a) - 1)%nat
  = Some (u_prompt !!! 1%nat).
Proof.
  intros Ha. destruct a as [| [| [| a]]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exfalso. lia.
Qed.

(* a byte of [line_alts !!! a] exists only for a real alternative: out of
   range the list is the default [[]] *)
Lemma line_alts_lt (a i : nat) (b : bv 8) :
  line_alts !!! a !! i = Some b -> (a < length line_alts)%nat.
Proof.
  intros Hb.
  destruct (decide (a < length line_alts)%nat) as [? | Hge]; [done |].
  exfalso. pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
  rewrite list_lookup_total_alt (lookup_ge_None_2 line_alts a ltac:(lia))
    in Hlt.
  cbn in Hlt. lia.
Qed.

Lemma snoc_lookup_total (cs : list nat) (a : nat) : (cs ++ [a]) !!! length cs = a.
Proof.
  rewrite list_lookup_total_alt lookup_app_r; [| lia].
  by rewrite Nat.sub_diag.
Qed.


(* ===================================================================== *)
(*  S1  THE TIGHT SHAPES                                                  *)
(* ===================================================================== *)
(* THE ROUND THIS BLOCK IS IN IS THE LAST ONE RESOLVED: nothing of [ps]
   is filed beyond it.  [pro_idx cs (length cs)] is the round of the
   block that closes line [length cs] -- the block a [wr_blk] owes, and
   the block a [wr_open] has just written ([n / 17 = length cs] there). *)
Definition wr_tail (ps cs : list nat) : Prop :=
  pro_from (S (pro_idx cs (length cs))) ps = [].

Definition wr_blk_t (ps cs : list nat) (n P : nat) : Prop :=
  wr_blk ps cs n P /\ wr_tail ps cs.

Definition wr_sp_t (ps cs : list nat) (n P : nat) : Prop :=
  wr_sp ps cs n P /\ wr_tail ps cs.

Definition wr_open_t (ps cs : list nat) (n P : nat) : Prop :=
  wr_open ps cs n P /\ wr_tail ps cs.

(* the choice list of a block with [i] bytes out: the first byte files it *)
Definition blkcs (cs : list nat) (a i : nat) : list nat :=
  match i with O => cs | S _ => cs ++ [a] end.

(* ---- what [wr_blk] says about the count ---- *)
Lemma wr_blk_n (ps cs : list nat) (n P : nat) :
  wr_blk ps cs n P -> n = (length echo_line * S (length cs))%nat.
Proof.
  intros (_ & Hm & Hdv & _). pose proof echo_line_length as HL.
  pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
  rewrite Hdv Hm in Hdm. lia.
Qed.

Lemma wr_blk_pos (ps cs : list nat) (n P : nat) :
  wr_blk ps cs n P -> (0 < n)%nat.
Proof.
  intros Hw. pose proof (wr_blk_n ps cs n P Hw). pose proof echo_line_length.
  lia.
Qed.

(* ...and it is echo's own stage ([UEchoOut.echo_stage], spelled out) *)
Lemma wr_blk_t_stage (ps cs : list nat) (n P : nat) :
  wr_blk_t ps cs n P ->
  n = (S (length cs) * length echo_line)%nat
  /\ P = length (proc_upto ps cs n)
  /\ pro_pin ps cs n
  /\ wr_tail ps cs.
Proof.
  intros [Hw Ht]. pose proof (wr_blk_n ps cs n P Hw) as Hn.
  destruct Hw as (Hpin & _ & _ & HP). split_and!; [lia | exact HP | exact Hpin | exact Ht].
Qed.

(* ---- filing an alternative reads no block below the boundary ---- *)
Lemma wr_blk_pin_snoc (ps cs : list nat) (n P a : nat) :
  wr_blk ps cs n P -> pro_pin ps (cs ++ [a]) n.
Proof.
  intros Hw. pose proof (wr_blk_n ps cs n P Hw) as Hn.
  destruct Hw as (Hpin & _). pose proof echo_line_length as HL.
  intros q Hq. rewrite (pro_idx_app_le cs [a] q); [exact (Hpin q Hq) | nia].
Qed.

Lemma wr_blk_low (ps cs : list nat) (n P a : nat) :
  wr_blk ps cs n P -> proc_upto ps (cs ++ [a]) n = proc_upto ps cs n.
Proof.
  intros Hw. pose proof (wr_blk_n ps cs n P Hw) as Hn.
  destruct Hw as (Hpin & Hm & Hdv & HP). pose proof echo_line_length as HL.
  symmetry.
  apply (proc_upto_cs_prefix_pred ps ps cs (cs ++ [a]) n
           ltac:(reflexivity) ltac:(by eexists) Hpin).
  assert (Hd1 : ((n - 1) `div` length echo_line)%nat = length cs).
  { symmetry. apply (Nat.div_unique (n - 1) (length echo_line)
                       (length cs) (length echo_line - 1)%nat); nia. }
  rewrite Hd1. lia.
Qed.

(* ---- the block a [wr_blk] owes, once alternative [a] is filed ---- *)
Lemma wr_blk_pending (ps cs : list nat) (n P a : nat) :
  wr_blk ps cs n P ->
  pending_n ps (cs ++ [a]) n = alt_cont ps (cs ++ [a]) (length cs).
Proof.
  intros Hw. pose proof (wr_blk_pos ps cs n P Hw) as Hpos.
  destruct Hw as (_ & Hm & Hdv & _).
  rewrite /pending_n. case_decide as H0; [exfalso; lia |].
  case_decide as Hm2; [| done].
  replace (n `div` length echo_line - 1)%nat with (length cs) by lia.
  reflexivity.
Qed.

Lemma wr_blk_alt (ps cs : list nat) (n P a : nat) :
  wr_blk ps cs n P -> a <> 3%nat ->
  pending_n ps (cs ++ [a]) n = line_alts !!! a.
Proof.
  intros Hw Ha. rewrite (wr_blk_pending ps cs n P a Hw) /alt_cont
                        snoc_lookup_total.
  case_decide as H3; [done |]. by rewrite app_nil_r.
Qed.

Lemma wr_blk_alt3 (ps cs : list nat) (n P : nat) :
  wr_blk ps cs n P ->
  pending_n ps (cs ++ [3%nat]) n
  = line_alts !!! 3%nat ++ pro_of (pro_from (S (pro_idx cs (length cs))) ps).
Proof.
  intros Hw. rewrite (wr_blk_pending ps cs n P 3%nat Hw) /alt_cont
                     snoc_lookup_total.
  case_decide as H3; [| done].
  by rewrite (pro_idx_app_le cs [3%nat] (length cs) ltac:(lia)).
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR: byte [j] of the alternative
   is byte [P + j] of the stream, for EVERY alternative -- the panic's
   block goes on into the next round's prologue, but its first five bytes
   are the panic line all the same. *)
Lemma wr_blk_byte (ps cs : list nat) (n P a j : nat) (b : bv 8) :
  wr_blk ps cs n P -> line_alts !!! a !! j = Some b ->
  proc_upto ps (cs ++ [a]) (S n) !! (P + j)%nat = Some b.
Proof.
  intros Hw Hb. pose proof Hw as (_ & _ & _ & HP).
  rewrite proc_upto_snoc (wr_blk_low ps cs n P a Hw) lookup_app_r; [| lia].
  replace (P + j - length (proc_upto ps cs n))%nat with j by lia.
  destruct (decide (a = 3%nat)) as [-> | Ha].
  - rewrite (wr_blk_alt3 ps cs n P Hw) lookup_app_l; [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  - by rewrite (wr_blk_alt ps cs n P a Hw Ha).
Qed.

(* ---- the round index does not move when a non-panic alternative is filed ---- *)
Lemma pro_idx_snoc_ne (cs : list nat) (a : nat) :
  a <> 3%nat -> pro_idx (cs ++ [a]) (S (length cs)) = pro_idx cs (length cs).
Proof.
  intros Ha. rewrite pro_idx_S snoc_lookup_total decide_False; [| exact Ha].
  rewrite (pro_idx_app_le cs [a] (length cs) ltac:(lia)). lia.
Qed.

Lemma pro_idx_snoc_3 (cs : list nat) :
  pro_idx (cs ++ [3%nat]) (S (length cs)) = S (pro_idx cs (length cs)).
Proof.
  rewrite pro_idx_S snoc_lookup_total
          (pro_idx_app_le cs [3%nat] (length cs) ltac:(lia)).
  first [ (case_decide as H3; [lia | exfalso; exact (H3 eq_refl)]) | lia ].
Qed.

Lemma wr_tail_snoc (ps cs : list nat) (a : nat) :
  a <> 3%nat -> wr_tail ps cs -> wr_tail ps (cs ++ [a]).
Proof.
  intros Ha Ht. rewrite /wr_tail length_app. cbn [length].
  rewrite Nat.add_1_r (pro_idx_snoc_ne cs a Ha). exact Ht.
Qed.

(* ===================================================================== *)
(*  S2  THE STEPS, PURE                                                   *)
(* ===================================================================== *)

(* (1) THE WHOLE BLOCK OF A NON-PANIC ALTERNATIVE, written: the cursor    *)
(*     lands on the stream's end and the round is settled -- [wr_open].   *)
Lemma wr_blk_open (ps cs : list nat) (n P a : nat) :
  wr_blk_t ps cs n P -> a <> 3%nat ->
  wr_open_t ps (cs ++ [a]) n (P + length (line_alts !!! a))%nat.
Proof.
  intros [Hw Ht] Ha. pose proof (wr_blk_n ps cs n P Hw) as Hn.
  pose proof echo_line_length as HL.
  pose proof Hw as (Hpin & Hm & Hdv & HP).
  split; [| exact (wr_tail_snoc ps cs a Ha Ht)].
  rewrite /wr_open. split_and!.
  - exact (wr_blk_pin_snoc ps cs n P a Hw).
  - exact Hm.
  - rewrite length_app Hdv. cbn [length]. lia.
  - rewrite Hdv (pro_idx_snoc_ne cs a Ha). apply Hpin. nia.
  - rewrite proc_upto_snoc (wr_blk_low ps cs n P a Hw)
            (wr_blk_alt ps cs n P a Hw Ha) length_app HP. reflexivity.
Qed.

(* (2) ...AND ONE BYTE SHORT OF IT, which is where the shell's ' ' goes:  *)
(*     [wr_sp] at the prompt's second byte.                               *)
Lemma wr_blk_sp (ps cs : list nat) (n P a : nat) :
  wr_blk_t ps cs n P -> (a < 3)%nat ->
  wr_sp_t ps (cs ++ [a]) n (P + (length (line_alts !!! a) - 1))%nat.
Proof.
  intros Hw Ha. pose proof (line_alts_len_ge2 a Ha) as Hlen.
  destruct (wr_blk_open ps cs n P a Hw ltac:(lia)) as [Hop Ht].
  split; [| exact Ht]. split.
  - replace (S (P + (length (line_alts !!! a) - 1)))%nat
      with (P + length (line_alts !!! a))%nat by lia.
    exact Hop.
  - exact (wr_blk_byte ps cs n P a _ _ (proj1 Hw) (line_alts_space a Ha)).
Qed.

(* (3) THE SPACE AND THE READ, as [EchoLinks] has them, with the tail     *)
(*     riding along.                                                      *)
Lemma wr_sp_open_t (ps cs : list nat) (n P : nat) :
  wr_sp_t ps cs n P -> wr_open_t ps cs n (S P).
Proof. intros [Hs Ht]. split; [exact (wr_sp_open ps cs n P Hs) | exact Ht]. Qed.

Lemma wr_open_read_t (ps cs : list nat) (n P : nat) :
  wr_open_t ps cs n P -> wr_blk_t ps cs (n + length echo_line)%nat P.
Proof.
  intros [Ho Ht]. split; [exact (wr_open_read ps cs n P Ho) | exact Ht].
Qed.

(* (4) THE ROUND'S CHOICE BYTE SETTLES ITS ROUND, so the writer's         *)
(*     resolution ends exactly there: [wr_pro]'s [~ pro_done] is the tail. *)
Lemma wr_pro_tail (ps cs : list nat) (n P : nat) :
  wr_pro ps cs n P -> wr_tail (ps ++ [0%nat]) cs.
Proof.
  intros (Hpin & Hm & Hdv & Hr & Hnd & HP).
  pose proof (pro_pin_idx_le ps cs n Hpin) as Hle.
  rewrite Hdv in Hnd Hle.
  rewrite /wr_tail.
  replace (S (pro_idx cs (length cs))) with (pro_idx cs (length cs) + 1)%nat
    by lia.
  rewrite -(pro_from_add 1 (pro_idx cs (length cs)))
          (pro_from_snoc_le (pro_idx cs (length cs)) ps 0%nat Hle).
  cbn [pro_from]. exact (pro_tail_open_snoc _ 0%nat Hnd).
Qed.

Lemma wr_pro_dollar_t (ps cs : list nat) (n P : nat) :
  wr_pro ps cs n P -> wr_sp_t (ps ++ [0%nat]) cs n (S P).
Proof.
  intros Hw. split; [exact (wr_pro_dollar ps cs n P Hw) | exact (wr_pro_tail ps cs n P Hw)].
Qed.

(* (5) THE PANIC LINE OPENS A FRESH ROUND AT THE SAME COUNT: five bytes   *)
(*     in, the writer owes that round's BANNER -- [wr_ban] with no failed *)
(*     sub-round ([j = 0]) and the panic line as the block's prefix        *)
(*     ([wr_pre]).  This is where [wr_tail] is spent.                     *)
Lemma wr_blk_ban (ps cs : list nat) (n P : nat) :
  wr_blk_t ps cs n P ->
  wr_ban ps (cs ++ [3%nat]) n (P + length (line_alts !!! 3%nat))%nat.
Proof.
  intros [Hw Ht]. pose proof (wr_blk_pos ps cs n P Hw) as Hpos.
  pose proof Hw as (Hpin & Hm & Hdv & HP).
  rewrite /wr_ban. split_and!.
  - exact (wr_blk_pin_snoc ps cs n P 3%nat Hw).
  - exact Hm.
  - rewrite length_app Hdv. cbn [length]. lia.
  - right. rewrite Hdv.
    replace (S (length cs) - 1)%nat with (length cs) by lia.
    exact (snoc_lookup_total cs 3%nat).
  - exists 0%nat. split.
    + rewrite Hdv pro_idx_snoc_3. exact Ht.
    + rewrite (wr_blk_low ps cs n P 3%nat Hw) -HP /wr_pre decide_False; [| lia].
      lia.
Qed.


(* ===================================================================== *)
(*  S3  THE CREDENTIAL AS RESOURCES                                       *)
(* ===================================================================== *)
Section echo_links_line.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* THE BLOCK FAMILY: alternative [a] of the line's block chosen, [i] of
     its bytes out -- or the taint.  At [i = 0] nothing is chosen and the
     index [a] is not read ([ewc_blk_0]). *)
  Definition ewc_blk (v : era_pins) (n a i : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_blk_t ps cs n P⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v (blkcs cs a i) ∗ E_lb v n) ∨ T)%I.

  (* ...the block written up to its prompt, which the shell writes after
     [wait] ([a < 3]; [a = 2] is the block-first '$' itself, nothing out) *)
  Definition ewc_post (v : era_pins) (n a : nat) : iProp Σ :=
    ewc_blk v n a (length (line_alts !!! a) - 2)%nat.

  (* ...and the shell's own panic line, [i] of its five bytes out *)
  Definition ewc_panic (v : era_pins) (n i : nat) : iProp Σ :=
    ewc_blk v n 3%nat i.

  (* THE OPEN-PROLOGUE ARM of [EchoLinks.ewc_owed] on its own *)
  Definition ewc_pro (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pro ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Definition ewc_sp_t (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_sp_t ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Definition ewc_open_t (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_open_t ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  (* THE LOOP'S BOUNDARY CREDENTIAL, WIDENED: the round's prologue is
     still open (sh's first prompt of a round: '$' files [ps ++ [0]]), or
     a line's block has been written up to its prompt by whoever took
     alternative [a] -- echo ([a = 0]), the exec-failed child ([a = 1]),
     or nobody ([a = 2], the child died at the null store and sh's '$'
     is the block's first byte). *)
  Definition ewc_line (v : era_pins) (n : nat) : iProp Σ :=
    (ewc_pro v n ∨ (∃ a : nat, ⌜(a < 3)%nat⌝ ∗ ewc_post v n a))%I.

  (* ...indexed by the prompt bytes out, [EchoLinks.ewc_pr]'s twin *)
  Definition ewc_lpr (v : era_pins) (n p : nat) : iProp Σ :=
    match p with
    | O => ewc_line v n
    | S O => ewc_sp_t v n
    | _ => ewc_open_t v n
    end.

  (* ...with the era's pin beside it, [EchoLinks.ewc_cred]'s twin: the
     shape the shell's [Wc] is instantiated at *)
  Definition ewc_lcred (k : nat) (n p : nat) : iProp Σ :=
    (∃ v : era_pins, era_pin γ k v ∗ ewc_lpr v n p)%I.

  Global Instance ewc_blk_timeless v n a i : Timeless (ewc_blk v n a i).
  Proof. rewrite /ewc_blk. apply _. Qed.
  Global Instance ewc_post_timeless v n a : Timeless (ewc_post v n a).
  Proof. rewrite /ewc_post. apply _. Qed.
  Global Instance ewc_panic_timeless v n i : Timeless (ewc_panic v n i).
  Proof. rewrite /ewc_panic. apply _. Qed.
  Global Instance ewc_pro_timeless v n : Timeless (ewc_pro v n).
  Proof. rewrite /ewc_pro. apply _. Qed.
  Global Instance ewc_sp_t_timeless v n : Timeless (ewc_sp_t v n).
  Proof. rewrite /ewc_sp_t. apply _. Qed.
  Global Instance ewc_open_t_timeless v n : Timeless (ewc_open_t v n).
  Proof. rewrite /ewc_open_t. apply _. Qed.
  Global Instance ewc_line_timeless v n : Timeless (ewc_line v n).
  Proof. rewrite /ewc_line. apply _. Qed.
  Global Instance ewc_lpr_timeless v n p : Timeless (ewc_lpr v n p).
  Proof. rewrite /ewc_lpr. destruct p as [| [| p]]; apply _. Qed.
  Global Instance ewc_lcred_timeless k n p : Timeless (ewc_lcred k n p).
  Proof. rewrite /ewc_lcred. apply _. Qed.

  (* ---- the taint inhabits every shape ---- *)
  Lemma ewc_blk_taint v n a i : T -∗ ewc_blk v n a i.
  Proof. iIntros "HT". rewrite /ewc_blk. by iRight. Qed.
  Lemma ewc_pro_taint v n : T -∗ ewc_pro v n.
  Proof. iIntros "HT". rewrite /ewc_pro. by iRight. Qed.
  Lemma ewc_sp_t_taint v n : T -∗ ewc_sp_t v n.
  Proof. iIntros "HT". rewrite /ewc_sp_t. by iRight. Qed.
  Lemma ewc_open_t_taint v n : T -∗ ewc_open_t v n.
  Proof. iIntros "HT". rewrite /ewc_open_t. by iRight. Qed.
  Lemma ewc_line_taint v n : T -∗ ewc_line v n.
  Proof. iIntros "HT". rewrite /ewc_line. iLeft. by iApply ewc_pro_taint. Qed.
  Lemma ewc_lpr_taint v n p : T -∗ ewc_lpr v n p.
  Proof.
    iIntros "HT". rewrite /ewc_lpr. destruct p as [| [| p]];
      [ by iApply ewc_line_taint | by iApply ewc_sp_t_taint
      | by iApply ewc_open_t_taint ].
  Qed.

  (* ---- the tight shapes imply [EchoLinks]'s loose ones ---- *)
  Lemma ewc_pro_owed v n : ewc_pro v n -∗ EchoLinks.ewc_owed T v n.
  Proof.
    rewrite /ewc_pro /EchoLinks.ewc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. by left.
  Qed.

  Lemma ewc_blk_owed v n a : ewc_blk v n a 0%nat -∗ EchoLinks.ewc_owed T v n.
  Proof.
    rewrite /ewc_blk /EchoLinks.ewc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    cbn [blkcs]. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. right.
    exact (proj1 Hw).
  Qed.

  Lemma ewc_sp_t_sp v n : ewc_sp_t v n -∗ EchoLinks.ewc_sp T v n.
  Proof.
    rewrite /ewc_sp_t /EchoLinks.ewc_sp. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma ewc_open_t_open v n : ewc_open_t v n -∗ EchoLinks.ewc_open T v n.
  Proof.
    rewrite /ewc_open_t /EchoLinks.ewc_open. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. exact (proj1 Hw).
  Qed.

  (* ---- the block family at [i = 0] reads no alternative ---- *)
  Lemma ewc_blk_0 v n a a' : ewc_blk v n a 0%nat -∗ ewc_blk v n a' 0%nat.
  Proof. rewrite /ewc_blk. cbn [blkcs]. iIntros "H". iExact "H". Qed.

  (* ...and it is the [a = 2] arm of the widened boundary: the block-first
     '$' of a child that recorded no choice *)
  Lemma ewc_line_of_blk0 v n a : ewc_blk v n a 0%nat -∗ ewc_line v n.
  Proof.
    iIntros "Hc". rewrite /ewc_line. iRight. iExists 2%nat.
    iSplitR; [iPureIntro; lia |].
    assert (H2 : (length (line_alts !!! 2%nat) - 2)%nat = 0%nat)
      by (rewrite line_alts_len2_; reflexivity).
    rewrite /ewc_post H2. iApply (ewc_blk_0 with "Hc").
  Qed.

  Lemma ewc_line_of_post v n a : (a < 3)%nat -> ewc_post v n a -∗ ewc_line v n.
  Proof.
    intros Ha. iIntros "Hc". rewrite /ewc_line. iRight. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma ewc_line_of_pro v n : ewc_pro v n -∗ ewc_line v n.
  Proof. iIntros "Hc". rewrite /ewc_line. by iLeft. Qed.

  (* =================================================================== *)
  (*  S4  ONE BYTE OF THE BLOCK, THROUGH THE ERA'S LINKS                  *)
  (*                                                                     *)
  (*  The block-first byte FILES the alternative ([echo_link_blk]); every *)
  (*  byte after it is an ordinary byte of the block the choice fixed     *)
  (*  ([echo_link_w]).  No bound on [i] beyond the byte's existence: the  *)
  (*  credential does not know WHO writes a byte, only that it is next.   *)
  (* =================================================================== *)
  Lemma echo_blk_step (k : nat) (v : era_pins) (n a i : nat) (b : bv 8)
      (Φ : iProp Σ) :
    line_alts !!! a !! i = Some b ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_blk v n a i -∗
    (ewc_blk v n a (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_blk with "Hlk") as "#Hblk".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_blk. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (proj1 Hw) as Hwb. pose proof Hwb as (Hpin & Hm & Hdv & HP).
    pose proof (wr_blk_pos ps cs n P Hwb) as Hpos.
    pose proof (line_alts_lt a i b Hb) as Ha.
    destruct i as [| i'].
    - (* THE BLOCK-FIRST BYTE files the alternative *)
      cbn [blkcs]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v P n a b ps cs Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hpos. }
      { exact Hm. }
      { lia. }
      { exact Hpin. }
      { exact HP. }
      { exact Ha. }
      { exact Hb. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs]. rewrite Nat.add_1_r.
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
    - (* every byte after it, at the choice list the first one extended *)
      cbn [blkcs].
      iApply ("Hw" $! k v (P + S i')%nat n b ps (cs ++ [a]) Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { rewrite length_app Hdv. cbn [length]. lia. }
      { exact (wr_blk_pin_snoc ps cs n P a Hwb). }
      { exact (wr_blk_byte ps cs n P a (S i') b Hwb Hb). }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs].
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
  Qed.

  (* the block written up to its prompt IS [ewc_post], by definition *)
  Lemma ewc_blk_done v n a :
    ewc_blk v n a (length (line_alts !!! a) - 2)%nat -∗ ewc_post v n a.
  Proof. rewrite /ewc_post. iIntros "$". Qed.

  (* ...and one byte further it is the half-written prompt *)
  Lemma ewc_blk_sp v n a :
    (a < 3)%nat ->
    ewc_blk v n a (length (line_alts !!! a) - 1)%nat -∗ ewc_sp_t v n.
  Proof.
    intros Ha. rewrite /ewc_blk /ewc_sp_t. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (line_alts_len_ge2 a Ha) as Hlen.
    assert (Hbc : blkcs cs a (length (line_alts !!! a) - 1) = cs ++ [a]).
    { destruct (length (line_alts !!! a) - 1)%nat as [| k] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]), (P + (length (line_alts !!! a) - 1))%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_blk_sp ps cs n P a Hw Ha).
  Qed.

  (* =================================================================== *)
  (*  S5  THE SHELL'S PROMPT AFTER A CHILD, AND AT THE WIDENED BOUNDARY   *)
  (* =================================================================== *)
  (* THE '$' AFTER A CHILD: an ordinary byte of the chosen block when the
     child wrote its share ([a = 0, 1]), the block-FIRST byte when it
     recorded no choice ([a = 2]) -- [echo_blk_step] at [i = length - 2]
     is both, and what it leaves is the half-written prompt. *)
  Lemma echo_prompt_dollar_post (k : nat) (v : era_pins) (n a : nat)
      (b : bv 8) (Φ : iProp Σ) :
    (a < 3)%nat -> b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_post v n a -∗
    (ewc_sp_t v n -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Ha Hb. iIntros "#Hpin #Hlk Hc HΦ".
    pose proof (line_alts_len_ge2 a Ha) as Hlen.
    assert (Hby : line_alts !!! a !! (length (line_alts !!! a) - 2)%nat
                  = Some b)
      by (rewrite Hb; exact (line_alts_dollar a Ha)).
    iApply (echo_blk_step k v n a (length (line_alts !!! a) - 2)%nat b Φ Hby
              with "Hpin Hlk Hc [HΦ]").
    iIntros "Hc". iApply "HΦ".
    replace (S (length (line_alts !!! a) - 2))%nat
      with (length (line_alts !!! a) - 1)%nat by lia.
    iApply (ewc_blk_sp v n a Ha with "Hc").
  Qed.

  (* THE ' ' AFTER IT: [EchoLinks.echo_prompt_space], with the tail along *)
  Lemma echo_prompt_space_t (k : nat) (v : era_pins) (n : nat) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_sp_t v n -∗
    (ewc_open_t v n -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_sp_t. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply ewc_open_t_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [[Hop Hby] Ht].
    pose proof Hop as (Hpin & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v P n b ps cs Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /ewc_open_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    iPureIntro. exact (wr_sp_open_t ps cs n P (conj (conj Hop Hby) Ht)).
  Qed.

  (* THE '$' AT THE WIDENED BOUNDARY: the round's choice byte when the
     prologue is open ([echo_link_pro] at [a = 0], as in
     [EchoLinks.echo_prompt_dollar]'s first case), the byte after the
     child's share otherwise. *)
  Lemma echo_prompt_dollar_line (k : nat) (v : era_pins) (n : nat)
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_line v n -∗
    (ewc_sp_t v n -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    rewrite /ewc_line. iDestruct "Hc" as "[Hc | Hc]"; last first.
    { iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (echo_prompt_dollar_post k v n a b Φ Ha Hb
                with "Hpin Hlk Hc HΦ"). }
    iDestruct (echo_links_pro with "Hlk") as "#Hpro".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_pro. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply ewc_sp_t_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hhd : pro_alts !!! 0%nat !! 0%nat = Some b)
      by (rewrite wr_pro_alts_0 Hb; exact wr_prompt_head).
    pose proof (wr_pro_dollar_t ps cs n P Hw) as Hsp.
    destruct Hw as (Hpin & Hm & Hdv & Hr & Hnd & HP).
    iApply ("Hpro" $! k v P n 0%nat b ps cs Φ
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { exact Hm. }
    { exact Hr. }
    { lia. }
    { exact Hpin. }
    { exact Hnd. }
    { exact HP. }
    { rewrite pro_alts_length. lia. }
    { exact Hhd. }
    iIntros "Hres". iApply "HΦ". rewrite /ewc_sp_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists (ps ++ [0%nat]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    by iPureIntro.
  Qed.

  (* ...AS ONE STEP FAMILY over the prompt's two bytes, [UShOut.ushpr_step]'s
     twin at the widened boundary *)
  Lemma ewc_lpr_step (k : nat) (v : era_pins) (n p : nat) (b : bv 8)
      (Φ : iProp Σ) :
    u_prompt !! p = Some b ->
    (p < 2)%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_lpr v n p -∗
    (ewc_lpr v n (S p) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb Hp. destruct p as [| [| p]]; [| | exfalso; lia].
    - assert (Hb0 : b = u_prompt !!! 0%nat).
      { rewrite wr_prompt_head in Hb. by injection Hb. }
      iIntros "#Hpin #Hlk Hc HΦ".
      iApply (echo_prompt_dollar_line k v n b Φ Hb0 with "Hpin Hlk Hc HΦ").
    - assert (Hb1 : b = u_prompt !!! 1%nat).
      { rewrite wr_prompt_tail in Hb. by injection Hb. }
      iIntros "#Hpin #Hlk Hc HΦ".
      iApply (echo_prompt_space_t k v n b Φ Hb1 with "Hpin Hlk Hc HΦ").
  Qed.

  (* =================================================================== *)
  (*  S6  THE READ, landing on the block family                           *)
  (* =================================================================== *)
  (* [EchoLinks.ewc_read]'s twin: the line just echoed owes its block and
     no alternative is chosen yet -- so this is [ewc_blk] at [i = 0] for
     EVERY [a]; the fork lends it and the child's first byte decides. *)
  Lemma ewc_read_t (v : era_pins) (n a : nat) :
    E_lb v (n + length echo_line)%nat -∗ ewc_open_t v n -∗
    ewc_blk v (n + length echo_line)%nat a 0%nat.
  Proof.
    iIntros "#HE' Hc". rewrite /ewc_open_t /ewc_blk.
    iDestruct "Hc" as "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. cbn [blkcs]. rewrite Nat.add_0_r.
    iFrame "Htn Hps Hcs HE'". iPureIntro. exact (wr_open_read_t ps cs n P Hw).
  Qed.

  (* ...and, at the loop's family, [UkSh.ush_wc_read]'s content *)
  Lemma ewc_lpr_read (v : era_pins) (n : nat) :
    E_lb v (n + length echo_line)%nat -∗ ewc_lpr v n 2%nat -∗
    ewc_lpr v (n + length echo_line)%nat 0%nat.
  Proof.
    iIntros "#HE' Hc". cbn [ewc_lpr].
    iApply (ewc_line_of_blk0 v _ 0%nat).
    iApply (ewc_read_t v n 0%nat with "HE' Hc").
  Qed.

  Lemma ewc_lcred_read (k n : nat) (v : era_pins) :
    era_pin γ k v -∗ E_lb v (n + length echo_line)%nat -∗
    ewc_lcred k n 2%nat -∗ ewc_lcred k (n + length echo_line)%nat 0%nat.
  Proof.
    iIntros "#Hpin #HE' Hc". rewrite /ewc_lcred.
    iDestruct "Hc" as (v') "[#Hpin' Hc]".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iExists v. iFrame "Hpin". iApply (ewc_lpr_read with "HE' Hc").
  Qed.

  (* =================================================================== *)
  (*  S7  THE PANIC, and the banner it opens                              *)
  (* =================================================================== *)
  Lemma echo_panic_step (k : nat) (v : era_pins) (n i : nat) (b : bv 8)
      (Φ : iProp Σ) :
    line_alts !!! 3%nat !! i = Some b ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_panic v n i -∗
    (ewc_panic v n (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. rewrite /ewc_panic. exact (echo_blk_step k v n 3%nat i b Φ Hb).
  Qed.

  (* THE FIVE BYTES OUT, THE NEXT ROUND'S BANNER IS OWED: what the shell
     hands back to /init through its exit payload, at the same count, and
     what pays the restart round's banner ([EchoLinks.echo_banner_step]
     from [ewc_ban _ _ 0]). *)
  Lemma ewc_panic_done (v : era_pins) (n : nat) :
    ewc_panic v n (length (line_alts !!! 3%nat)) -∗ EchoLinks.ewc_ban T v n 0%nat.
  Proof.
    rewrite /ewc_panic /ewc_blk /EchoLinks.ewc_ban.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hbc : blkcs cs 3%nat (length (line_alts !!! 3%nat)) = cs ++ [3%nat])
      by (rewrite line_alts_len3; reflexivity).
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [3%nat]), (P + length (line_alts !!! 3%nat))%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (wr_blk_ban ps cs n P Hw).
  Qed.

  (* =================================================================== *)
  (*  S8  THE ENTRY: /init's eighteenth banner byte lands on the widened  *)
  (*      boundary's open-prologue arm ([EchoLinks.ewc_ban_done]'s twin;  *)
  (*      that lemma's [ewc_owed] admits a loose [wr_blk] arm it never   *)
  (*      produces, which is why the entry must come through here).      *)
  (* =================================================================== *)
  Lemma ewc_ban_done_line (v : era_pins) (n : nat) :
    EchoLinks.ewc_ban T v n (length u_banner) -∗ ewc_line v n.
  Proof.
    rewrite /EchoLinks.ewc_ban. iIntros "[Hl | #HT]"; last by iApply ewc_line_taint.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iApply ewc_line_of_pro. rewrite /ewc_pro.
    iLeft. iExists ps, cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_ban_pro ps cs n P Hw).
  Qed.

  (* =================================================================== *)
  (*  S9  ECHO'S EXIT PAYLOAD IS [ewc_post] AT [a = 0]                    *)
  (*                                                                     *)
  (*  [UEchoOut.echq v ps0 cs0 n0 P] is [fun _ => ech ... 12] with        *)
  (*  [ech v ps0 cs0 n0 P 12 = (turn v (P + 12) ∗ ps_lb v ps0 ∗ cs_lb v   *)
  (*  (cs0 ++ [0]) ∗ E_lb v n0) ∨ T] under [echo_stage ps0 cs0 n0 P]      *)
  (*  (the three pure premises below).  It is not nameable here (it sits  *)
  (*  above the file system), so the conversion is stated at its body:   *)
  (*  M3b core applies it after [rewrite /echq /ech; cbn [echcs]].  The   *)
  (*  fourth premise, [wr_tail], is what the child was LENT with          *)
  (*  ([ewc_blk _ _ _ 0]'s shape) and echo carries unchanged.             *)
  (* =================================================================== *)
  Lemma ewc_post_of_ech (v : era_pins) (ps0 cs0 : list nat) (n0 P : nat) :
    n0 = (S (length cs0) * length echo_line)%nat ->
    P = length (proc_upto ps0 cs0 n0) ->
    pro_pin ps0 cs0 n0 ->
    wr_tail ps0 cs0 ->
    ((turn v (P + 12)%nat ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [0%nat])
      ∗ E_lb v n0) ∨ T) -∗
    ewc_post v n0 0%nat.
  Proof.
    intros Hn0 HP Hpin Ht. pose proof echo_line_length as HL.
    assert (H12 : (length (line_alts !!! 0%nat) - 2)%nat = 12%nat)
      by (rewrite line_alts_len0; reflexivity).
    rewrite /ewc_post H12 /ewc_blk.
    iIntros "[(Htn & #Hps & #Hcs & #HE) | #HT]"; last by iRight.
    iLeft. iExists ps0, cs0, P. cbn [blkcs]. iFrame "Htn Hps Hcs HE".
    iPureIntro. split; [| exact Ht].
    rewrite /wr_blk. split_and!.
    - exact Hpin.
    - rewrite Hn0. apply Nat.Div0.mod_mul.
    - rewrite Hn0. apply Nat.div_mul. lia.
    - exact HP.
  Qed.

  (* ...and the lend's other end: [ewc_blk _ _ _ 0] unfolds to the turn
     bundle at the stage echo's constructor asks for, plus [wr_blk_t_stage] *)
  Lemma ewc_blk_0_lend (v : era_pins) (n a : nat) :
    ewc_blk v n a 0%nat -∗
    (∃ ps cs P : _, ⌜wr_blk_t ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T.
  Proof.
    rewrite /ewc_blk. cbn [blkcs]. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    rewrite Nat.add_0_r. iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
    by iPureIntro.
  Qed.

End echo_links_line.
