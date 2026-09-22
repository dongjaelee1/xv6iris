(* ===================================================================== *)
(*  UCatPipe.v -- cat's ROUND AND ENTRY AT A PIPE READ END (lane         *)
(*  CAT-PIPE, design/app-pipe.md SS5.3, SS4.1).                          *)
(*                                                                       *)
(*  [UCatKernel.v] is cat's round at the FILE claim and [UCatOut.v] is    *)
(*  its console payment at the FILE stage; this file is the PIPELINE      *)
(*  application's twin of both, with ONE structural difference that is    *)
(*  the whole point of the lane:                                         *)
(*                                                                       *)
(*    THERE IS NO OFFSET.  The file round carries an abstract [Hold : nat *)
(*    -> iProp] -- "the descriptor HELD AT [p]" -- because a file read    *)
(*    runs at an offset the descriptor records, and                       *)
(*    [UCatKernel.cat_round_at]'s whole shape (the boxed obligation AT    *)
(*    [Hold p], the [Hpin] row) exists to pin that offset to the console  *)
(*    cursor.  A pipe has none: the READ POINTER is the protocol's own    *)
(*    [PipeProto.rcur], one exclusive permit, and the console cursor IS   *)
(*    that number.  So the round's invariant has ONE existential [c] and  *)
(*    two resources at it, and no [Hpin] premise at all.                  *)
(*                                                                       *)
(*  WHAT IS HERE.  SS1-2: the pipeline stage's own cursor family [pcch]   *)
(*  ([UCatOut]'s [cch] at [PipeLinks]' links and [PipeOutPure]'s pure     *)
(*  layer) -- what SH-PIPE-ROUND lends cat and gets back.  SS3: the read  *)
(*  row, cat's [read] at ledger slot 0 taken at [UkReadPipe]'s standard-  *)
(*  slot leaf with [PipeProto.pipe_rpay_of_inv] for the payment.  SS4:    *)
(*  the round.  SS5: the entry at argv ["cat"].  SS6: the exit row and    *)
(*  the consumer test.                                                   *)
(*                                                                       *)
(*  THE ONE PREMISE, AND IT IS A KERNEL ROW NOBODY HAS STATED (this       *)
(*  lane's finding; see SS3's note): a pipe read can answer -1, and cat's *)
(*  loop branches on exactly that ([bltz a0,0x6a] -> "cat: read error").  *)
(*  The FILE round refutes the tail with lane OFF-LINK's count bound      *)
(*  (every count is at most 512, so the signed reading is the unsigned    *)
(*  one).  At a pipe the bound does not hold: [UkReadPipe.                *)
(*  uread_pipe_ans] admits -1, [PipeQueue.pipe_rstop_noobs] has THREE     *)
(*  arms that produce it, and only two of them are refutable from what a  *)
(*  program owns.  The third -- the reader's KILL SHOT -- is refutable    *)
(*  only by the row [UexecRet.uexec_live_ok] states FOR THE CONSOLE       *)
(*  DEVICE ALONE.  It is taken here as a NAMED premise [pcat_nokill],     *)
(*  stated exactly as that row's pipe twin, and reported.                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UserPtTree.         (* [uptd] / [uva_wmapped] *)
Require Import VcGen.              (* [trunc32_subrange] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import WpUart.             (* [out_link] *)
Require Import UCodeCat.
Require User.CatSyms User.CatInstrs.
Require Import ChildTok.
Require Import FdSlots PipeNames ProcGeom UserFd.
Require Import UexecSlot UexecRet UsysMemOk.
Require Import UexecExecInst.      (* THE INSTANCES: [uexecSG_xv6], [uprogSG_gen] *)
Require Import UkCat.
Require Import UkCatCat.
Require Import UkCatMain.
Require Import ExecEntry.          (* [image_entry] / [image_entry_of_at] *)
Require Import SpecKexec.          (* [kexec_image_ok_fd] *)
Require Import UkAbi.              (* [uk_args_c] / [uka_argc] *)
Require Import ElfUser.            (* [cat_elf] *)
Require Import UEchoKernel.        (* [echo_args] / the key's argument reading *)
Require Import UShEcho.            (* [echo_node_img] *)
Require Import UkShEcho.           (* [echo_argv_bytes] / [echo_off_lt] *)
Require Import UShCat.             (* cat's exec/argv geometry and entry carve *)
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import PipeQueue.          (* the payments and the posts *)
Require Import PipeProto.          (* the protocol: [pipe_inv] / [rcur] / [pipe_rQ] *)
Require Import UkReadRows.         (* [spost_at_read_elim] / [std_fd_st_of_key] *)
Require Import UkReadPipe.         (* the standard-slot pipe read leaf *)
Require Import LineWords EchoDisc.
Require Import PipeDisc PipeOutPure PipeOut PipeLinks.
Require Import EchoOut AppEcho.
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE HALF: THE PIPELINE STAGE cat's ROUND STANDS AT           *)
(*                                                                       *)
(*  [UCatOut.cat_stage] at [PipeOutPure]'s layer, and it is SHORTER by    *)
(*  exactly one conjunct: a pipeline round reads NO STATE, so there is    *)
(*  no [s0], no [fst_upto] and no tie.  What replaces the file's          *)
(*  "[uline_of ... = LCat]" is the alternative's own admissibility        *)
(*  [palt_ok (pcat_line I0) PRan], which is [True] at an [LPipe] line and *)
(*  [False] at an [LEcho] one -- so the stage says the round's line is a *)
(*  PIPELINE line, in the one form the write link asks for.              *)
(* ===================================================================== *)

(* the line cat's round answers *)
Definition pcat_line (I0 : list (bv 8)) : pline :=
  pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat).

(* ...and the bytes cat prints: the round's continuation minus sh's
   prompt.  [PipeDisc.pcont _ PRan = wl_line (drop 1 ws) ++ u_prompt], and
   that head is the LINE the protocol carries -- design SS4.1's cat's
   output is echo's line. *)
Definition pcat_out (I0 : list (bv 8)) : list (bv 8) :=
  wl_line (drop 1 (pline_ws (pcat_line I0))).

Lemma pcat_cont_ran (I0 : list (bv 8)) :
  pcont (pcat_line I0) PRan = pcat_out I0 ++ u_prompt.
Proof using. reflexivity. Qed.

Definition pcat_stage (ps0 cs0 : list nat) (I0 : list (bv 8)) (P : nat)
  : Prop :=
  rest_of I0 = []
  /\ nlines I0 = S (length cs0)
  /\ palt_ok (pcat_line I0) PRan
  /\ P = length (proc_before_p ps0 cs0 I0)
  /\ pro_pin_p ps0 cs0 I0.

Lemma pcat_stage_nonnil ps0 cs0 I0 P :
  pcat_stage ps0 cs0 I0 P -> I0 <> [].
Proof using.
  intros (_ & Hn & _) ->. rewrite nlines_nil in Hn. discriminate.
Qed.

Lemma pcat_stage_last ps0 cs0 I0 P :
  pcat_stage ps0 cs0 I0 P -> (nlines I0 - 1)%nat = length cs0.
Proof using. intros (_ & Hn & _). lia. Qed.

Lemma pcat_stage_nstarted ps0 cs0 I0 P :
  pcat_stage ps0 cs0 I0 P -> nstarted I0 = S (length cs0).
Proof using.
  intros Hst. pose proof Hst as (Hr & Hn & _).
  by rewrite (pop_nstarted_rest_nil I0 Hr) Hn.
Qed.

(* filing an alternative reads no round below the boundary *)
Lemma pcat_stage_pin_snoc ps0 cs0 I0 P a :
  pcat_stage ps0 cs0 I0 P -> pro_pin_p ps0 (cs0 ++ [a]) I0.
Proof using.
  intros Hst. pose proof (pcat_stage_nstarted ps0 cs0 I0 P Hst) as Hns.
  pose proof Hst as (_ & _ & _ & _ & Hpin).
  intros q Hq. rewrite Hns in Hq.
  rewrite (pro_idx_p_ext (cs0 ++ [a]) cs0 q
             ltac:(intros j Hj; rewrite list_lookup_total_alt lookup_app_l;
                   [by rewrite -list_lookup_total_alt | lia])
             q ltac:(lia)).
  apply Hpin. rewrite Hns. exact Hq.
Qed.

(* ...and it moves no byte of what is already out *)
Lemma pcat_blk_low ps0 cs0 I0 P a :
  pcat_stage ps0 cs0 I0 P ->
  proc_before_p ps0 (cs0 ++ [a]) I0 = proc_before_p ps0 cs0 I0.
Proof using.
  intros Hst. pose proof Hst as (Hr & Hn & _ & _ & Hpin). symmetry.
  apply (proc_before_p_cs_prefix ps0 ps0 cs0 (cs0 ++ [a]) I0
           ltac:(reflexivity) ltac:(by eexists) Hpin).
  rewrite (pop_nlines_removelast I0 Hr). lia.
Qed.

(* THE BLOCK cat's ROUND OWES once alternative [a] is filed: at a
   non-panic alternative it is exactly that alternative's continuation.
   There is no state to compute -- [pcont] reads the line and the
   alternative and nothing else, which is where the pipeline application
   is SIMPLER than the file one. *)
Lemma pcat_blk_pending ps0 cs0 I0 P a :
  pcat_stage ps0 cs0 I0 P ->
  palt_panic (palt_of a) = false ->
  pending_at_p ps0 (cs0 ++ [a]) I0 = pcont (pcat_line I0) (palt_of a).
Proof using.
  intros Hst Hnp.
  pose proof (pcat_stage_nonnil ps0 cs0 I0 P Hst) as Hne.
  pose proof (pcat_stage_last ps0 cs0 I0 P Hst) as Hlast.
  pose proof Hst as (Hr & Hn & _ & _ & _).
  assert (Hat : palt_at (cs0 ++ [a]) (nlines I0 - 1)%nat = palt_of a).
  { rewrite /palt_at Hlast list_lookup_total_alt lookup_app_r; [| lia].
    by rewrite Nat.sub_diag. }
  rewrite /pending_at_p decide_False; [| exact Hne].
  rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_p Hat Hnp /pcat_line. by rewrite app_nil_r.
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR: byte [j] of cat's alternative
   is byte [P + j] of the era's process stream. *)
Lemma pcat_blk_byte ps0 cs0 I0 P a j b :
  pcat_stage ps0 cs0 I0 P ->
  palt_panic (palt_of a) = false ->
  pcont (pcat_line I0) (palt_of a) !! j = Some b ->
  proc_stream_p ps0 (cs0 ++ [a]) I0 !! (P + j)%nat = Some b.
Proof using.
  intros Hst Hnp Hb. pose proof Hst as (_ & _ & _ & HP & _).
  rewrite /proc_stream_p (pcat_blk_low ps0 cs0 I0 P a Hst)
          lookup_app_r; [| lia].
  replace (P + j - length (proc_before_p ps0 cs0 I0))%nat with j by lia.
  by rewrite (pcat_blk_pending ps0 cs0 I0 P a Hst Hnp).
Qed.

(* ---- the alternative cat's round files, and its two closed facts ---- *)
Definition pcat_alt : nat := palt_code PRan.

Lemma pcat_alt_of : palt_of pcat_alt = PRan.
Proof using. vm_compute. reflexivity. Qed.

Lemma pcat_alt_panic : palt_panic (palt_of pcat_alt) = false.
Proof using. by rewrite pcat_alt_of. Qed.

(* ===================================================================== *)
(*  THE PURE STEP THE ROUND SPENDS: THE BYTES THE READ DELIVERED ARE THE  *)
(*  ROUND'S OWN, AT THE CURSOR.                                          *)
(*                                                                       *)
(*  [UCatKernel.cat_round_line]'s twin, and its premise is [PipeProto.    *)
(*  pipe_rQ]'s PURE CONJUNCT and nothing else: the node cat gets back     *)
(*  says [acc = take (length acc) (drop c L)], so byte [k] of what it     *)
(*  just read is byte [c + k] of the line -- which is byte [c + k] of the *)
(*  round's continuation, because [pcont _ PRan] is [L ++ u_prompt] and   *)
(*  the cursor never reaches the prompt.  (STOP RULE 2 of the brief: the  *)
(*  stage's write link wants NOTHING BEYOND THIS -- no reading of [cs] or *)
(*  of which line is being echoed.  Answered here.)                      *)
(* ===================================================================== *)
Lemma pcat_round_line (I0 : list (bv 8)) (L : list (bv 8)) (c d : nat)
    (gb : nat -> bv 8) :
  pcat_out I0 = L ->
  (forall j : nat, (j < d)%nat -> L !! (c + j)%nat = Some (gb j)) ->
  forall j : nat, (j < d)%nat ->
    pcont (pcat_line I0) (palt_of pcat_alt) !! (c + j)%nat = Some (gb j).
Proof using.
  intros HL Hgb j Hj.
  rewrite pcat_alt_of pcat_cont_ran HL.
  pose proof (Hgb j Hj) as Hb.
  rewrite (lookup_app_l L u_prompt (c + j)%nat
             (lookup_lt_Some L (c + j)%nat (gb j) Hb)).
  exact Hb.
Qed.

(* ...AND THE BYTES A READ DELIVERED ARE THE LINE'S, at the cursor: this is
   [PipeProto.pipe_rQ]'s PURE CONJUNCT and nothing else.  (STOP RULE 2 of
   the brief: the pipe stage's write link wants NOTHING BEYOND THIS -- no
   reading of [cs], no knowledge of which line is being echoed.  Answered.)
   NOTE THE SHAPE: what comes out is a LOOKUP and not an index bound, and
   deliberately so -- at [acc = []] the cursor may sit anywhere at all
   ([take 0 (drop c L) = []] for every [c]), so "the cursor is inside the
   line" is FALSE as stated and is not what the round needs. *)
Lemma pcat_acc_line (L acc : list (bv 8)) (c : nat) :
  acc = take (length acc) (drop c L) ->
  forall j : nat, (j < length acc)%nat ->
    L !! (c + j)%nat = Some (acc !!! j).
Proof using.
  intros Hacc j Hj.
  transitivity (acc !! j); [ | exact (list_lookup_lookup_total_lt acc j Hj) ].
  symmetry.
  transitivity (take (length acc) (drop c L) !! j);
    [ by rewrite -Hacc | ].
  rewrite lookup_take; [ by rewrite lookup_drop | lia ].
Qed.

(* ===================================================================== *)
(*  2.  THE CURSOR FAMILY AT THE PIPELINE STAGE                           *)
(*                                                                       *)
(*  [UCatOut.cch] at [PipeLinks]' links.  [p] of cat's output bytes are   *)
(*  out and the era's cursor says so -- or the era is TAINTED.  The       *)
(*  choice list grows at the FIRST byte and not before ([pcatcs]); at     *)
(*  [p = 0] the family does not mention the alternative at all, which is  *)
(*  what lets cat hand the turn back UNFILED when the line is empty.      *)
(*                                                                       *)
(*  ONE CONJUNCT FEWER THAN THE FILE'S: there is no [f0_lb] -- a pipe     *)
(*  dies with its era and the claim carries no per-era state.            *)
(* ===================================================================== *)
Section PCatOut.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).

  Definition pcatcs (cs0 : list nat) (a p : nat) : list nat :=
    match p with O => cs0 | S _ => cs0 ++ [a] end.

  Lemma pcatcs_pos (cs0 : list nat) (a p : nat) :
    (0 < p)%nat -> pcatcs cs0 a p = cs0 ++ [a].
  Proof using . intro Hp. destruct p as [| p']; [lia | reflexivity]. Qed.

  Definition pcch (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (a P p : nat) : iProp Σ :=
    ((turn v (P + p)%nat ∗ ps_lb v ps0 ∗ cs_lb v (pcatcs cs0 a p)
      ∗ inp_lb v I0) ∨ echo_taint γ)%I.

  Global Instance pcch_timeless v ps0 cs0 I0 a P p :
    Timeless (pcch v ps0 cs0 I0 a P p).
  Proof using . rewrite /pcch /echo_taint. apply _. Qed.

  (* AT THE CURSOR'S START THE ALTERNATIVE IS NOT YET NAMED. *)
  Lemma pcch_0_alt (v : era_pins) (ps0 cs0 : list nat)
      (I0 : list (bv 8)) (a a' P : nat) :
    pcch v ps0 cs0 I0 a P 0%nat ⊣⊢ pcch v ps0 cs0 I0 a' P 0%nat.
  Proof using . rewrite /pcch /pcatcs. reflexivity. Qed.

  (* ONE BYTE.  The block-first byte FILES the alternative
     ([PipeLinks.pipe_write_link_blk]); every byte after it goes through
     the ordinary link at the choice list the first one extended. *)
  Lemma pcch_step (k : nat) (v : era_pins) (ps0 cs0 : list nat)
      (I0 : list (bv 8)) (a P p : nat) (b : bv 8) (Φ : iProp Σ) :
    pcat_stage ps0 cs0 I0 P ->
    palt_ok (pcat_line I0) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = false ->
    pcont (pcat_line I0) (palt_of a) !! p = Some b ->
    era_pin γ k v -∗
    pcch v ps0 cs0 I0 a P p -∗
    (pcch v ps0 cs0 I0 a P (S p) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hst Hok Hnp Hfk Hb.
    pose proof (pcat_stage_nonnil ps0 cs0 I0 P Hst) as Hne.
    pose proof (pcat_stage_pin_snoc ps0 cs0 I0 P a Hst) as Hpin1.
    pose proof Hst as (Hr & Hn & _ & HP & Hpin).
    iIntros "#Hpin Hc HΦ".
    rewrite /pcch.
    iDestruct "Hc" as "[(Htn & #Hps & #Hcs & #Hilb) | #HT]".
    - destruct p as [| p']; cbn [pcatcs].
      + (* THE BLOCK-FIRST BYTE *)
        rewrite Nat.add_0_r.
        iApply (pipe_write_link_blk g Hcons k v P a b ps0 cs0 I0 Φ
                  Hne Hr ltac:(lia) Hpin HP Hok Hfk Hb
                  with "Hpin Htn Hps Hcs Hilb [HΦ]").
        iIntros "Hres". iApply "HΦ". cbn [pcatcs].
        replace (P + 1)%nat with (S P) by lia. iExact "Hres".
      + (* every byte after it *)
        iApply (pipe_write_link g Hcons k v (P + S p')%nat b ps0
                  (cs0 ++ [a]) I0 Φ
                  ltac:(rewrite length_app; cbn [length]; lia)
                  Hpin1
                  (pcat_blk_byte ps0 cs0 I0 P a (S p') b Hst Hnp Hb)
                  with "Hpin Htn Hps Hcs Hilb [HΦ]").
        iIntros "Hres". iApply "HΦ". cbn [pcatcs].
        replace (P + S (S p'))%nat with (S (P + S p')) by lia.
        iExact "Hres".
    - (* THE TAINT ARM continues the tower on its own *)
      iApply (pipe_write_link_taint g Hcons k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight.
  Qed.

End PCatOut.

(* THE SIGNED READING OF A SMALL COUNT ([UCatKernel.cat_signed_small],
   restated here rather than imported: that file's cone is the FILE
   application's).  A word whose unsigned value is at most 512 has the
   same signed value -- which is what refutes cat's `read error` branch
   wherever the count is a real one. *)
Lemma pcat_signed_small (x : mword 64) :
  (bv_unsigned x <= 512)%Z -> bv_signed x = bv_unsigned x.
Proof using.
  intro H. pose proof (bv_unsigned_in_range _ x) as [Hl _].
  unfold bv_signed. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 9223372036854775808%Z)
    by (vm_compute; reflexivity).
  rewrite Hhm. split; [ lia | ].
  apply (Z.le_lt_trans _ 512); [ exact H | reflexivity ].
Qed.

(* ===================================================================== *)
(*  3.  THE READ ROW: cat's read(0, buf, 512) AT A PIPE READ END          *)
(* ===================================================================== *)
Section UCatPipe.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* NO [ctokG] SECTION VARIABLE, and it is the same trap as the two
     supply classes: [ChildTok.kill_shot] -- which the read post's kill arm
     carries -- resolves its [ctokG] THROUGH the [xv6G] bundle inside
     [UkReadPipe], and a standalone [ctokG] here would make the same
     proposition a different term.  [UCatKernel] omits it for the same
     reason. *)
  Context `{!echoOutG Σ, !pipeProtoG Σ, !pipeOutG Σ}.
  (* NO [uexecSG] AND NO [uprogSG] SECTION VARIABLE, for [UCatKernel]'s
     reason (lane CAT-WALK-2, K2): a variable of either class here would be
     a SECOND instance whose [UkRun.urun] prints identically and does not
     unify with the one [UkReadPipe]'s leaf and [UkCatCat]'s walk run at. *)
  (* ...AND THAT IS NOW HALF TRUE: [uexecSG] stays ambient, and [uprogSG]
     is a SECTION VARIABLE (design SS4.3z item 2).  [UkReadPipe]'s leaf and
     [UkCatCat]'s walk are THEMSELVES [uprogSG]-generic (both bind
     [Context `{PS : uprogSG Σ}]), so a variable here does not make a
     second instance -- it makes this file's round generic in the same one,
     which is what lets an APPLICATION enter cat's paid image at
     [UexecExecInst.uprogSG_free] (where [UexecExecMint.udep_free] is
     closed) instead of at the ambient generic instance, whose only [udep]
     producer is the taint.  Every landed consumer instantiates it
     explicitly and every landed statement is byte-identical after
     [(PS := _)]. *)
  Context `{PS : UexecSG.uprogSG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did, and the
     record equation is at the pipeline application's own claim. *)
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  (* the record's kill equation, [UShRound]'s [Hkill] at this claim: the
     pipeline application's kill credential IS the echo taint
     ([AppPipe.pipe_kill]).  It is an EQUATION, so both directions are
     available -- which is what lets a tainted turn pay a pipe read
     ([PipeQueue.pipe_rpay_taint] wants [RiscvPtsto.app_taint]). *)
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = echo_taint γ).
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).
  Local Notation T := (echo_taint γ).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ------------------------------------------------------------------- *)
  (*  3a.  THE LEAF, RE-PROVED AT THE WALK -- AND WHY (finding 1).         *)
  (*                                                                      *)
  (*  [UkReadPipe.wp_uk_ecall_read_pipe_std] is the leaf this lane was to  *)
  (*  take, and it cannot be taken as it stands, for TWO independent       *)
  (*  reasons read at its statement:                                      *)
  (*                                                                      *)
  (*  (i)  ITS COUNT PREMISE IS THE WHOLE WORD.  It asks for [uint (m !!!  *)
  (*       a2) = Z.of_nat cap]; what cat's loop gives its read obligation  *)
  (*       ([UkCat.kcat_r]) is [bv_signed (subrange_vec_dec (m !!! a2) 31  *)
  (*       0) = Z.of_nat cnt] -- the low 32 bits, signed.  The upper half  *)
  (*       of a2 is unconstrained there, so the premise is not derivable.  *)
  (*       The walk underneath ([UkRunSys.wp_uk_ecall_read_at]) takes the  *)
  (*       SIGNED reading, which is exactly what is in hand.               *)
  (*                                                                      *)
  (*  (ii) IT DROPS THE WALK'S NO-FAULT ROW.  [wp_uk_ecall_read_at] hands  *)
  (*       out [Hnf] -- every byte of the destination is writable-mapped in *)
  (*       any table the key's projection admits -- and [uvis_lazy W =    *)
  (*       false], and [UkReadRows.spost_at_read_elim] exhibits the post's *)
  (*       own table with the three facts [Hnf] wants.  The pipe leaf's    *)
  (*       continuation relays none of them -- so a caller cannot refute   *)
  (*       [PipeQueue.pipe_rstop_noobs]' COPY-OUT FAULT arm, which is one  *)
  (*       of the three ways a pipe read answers -1.                       *)
  (*                                                                      *)
  (*  So the leaf is re-proved here, at the same walk, with the same       *)
  (*  deposit ([UkReadPipe.udepwf_std_read_pipe], taken unchanged) and     *)
  (*  the same post, plus the relayed row.  NOTHING IN [UkReadPipe.v]      *)
  (*  MOVES.                                                              *)
  (* ------------------------------------------------------------------- *)
  Lemma pcat_ecall_read (h : CpuId) (m : regfile) (pc : mword 64)
      (k cap : nat) (f : nat -> bv 8) (avail : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (γp : pipe_names)
      (ua : mword 64)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
      = Z.of_nat cap ->
    (cap <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    m !!! Regidx a1_idx = ua ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ustd γfd l -∗
    pipe_rpay (pn_queue γp) Rp Rpe cap -∗
    ubytes γd (uint (ua)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (M' : gmap Z (bv 8)) (Pt : uptd) (gn : gname),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ UkReadPipe.uread_pipe_ans cap r ⌝ -∗
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (ua) (Z.of_nat i))
           = (uint (ua) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (ua) (Z.of_nat j))
           = Some (g j) ⌝ -∗
       (* THE RELAYED NO-FAULT ROW, at the post's OWN table *)
       ⌜ forall j : nat, (j < k)%nat ->
           uva_wmapped Pt
             (uint (add_vec_int (ua) (Z.of_nat j))) ⌝ -∗
       pipe_rpost_img Pt (pn_queue γp) Rp Rpe (ChildTok.kill_shot gn ∗ app_taint)%I
         cap r M' (ua) -∗
       UserFd.ustd γfd l -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes γd (uint (ua)) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hlt Hl Ha2 Hcapk Hal Hua1. subst ua.
    iIntros "#Hi Hrun Hstd Hpay Hbuf Hcont".
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap).
    { rewrite /sys_rw_count trunc32_subrange. exact Ha2. }
    iPoseProof (UkReadPipe.udepwf_std_read_pipe N m pc l fd wb γp Rp Rpe
                  Ha0 Hlt Hl with "[Hpay]") as "Hsb";
      [ rewrite Hcnt Nat2Z.id; iExact "Hpay" | ].
    iApply (wp_uk_ecall_read_at N h m pc (Z.of_nat cap) k f avail
              (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe)
              (UserFd.ustd γfd l)
              (fun fdv => take NSTD fdv = l)
              Hn Ha2 ltac:(rewrite Nat2Z.id; exact Hcapk) Hal
              (fun fdv => UserFd.ustd_agree γfd fdv l)
              with "Hi Hrun [Hsb] Hstd Hbuf").
    { iApply (udepwf_K_std N m pc USYS_read
                (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe) l with "Hsb"). }
    iIntros (h' r d gW W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Htake %Hlz %Hlive
       Hstd Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(%Hpmp & %Hwfp & %Hlzp & Hcore)".
    iDestruct (UkReadPipe.uread_pipe_core (uvis_gen W) P
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) wb γp
                 (sys_rw_count (m !!! Regidx a2_idx))
                 (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe)
                 Rp Rpe r M' (m !!! Regidx a1_idx)
                 (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l fd
                    (FdOpen true wb (FdPipe γp)) Ha0 Hlt Htake Hl)
                 with "Hcore") as "Hrp".
    rewrite Hcnt in Hret.
    rewrite Hcnt Nat2Z.id.
    rewrite Nat2Z.id in Hd.
    assert (Hnfp : forall j : nat, (j < k)%nat ->
              uva_wmapped P
                (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))))
      by (intros j Hj; exact (Hnf P j Hwfp Hpmp (Hlzp Hlz) Hj)).
    iApply ("Hcont" $! h' r d gW M' P (uvis_gen W)
              with "[%] [%] [%] [%] [%] [%] Hrp Hstd Hrun Hbuf");
      [ exact Hd | exact Hgf
      | exact (UkReadPipe.uread_pipe_ans_of_ret cap r Hret)
      | exact Hlin | exact Himg | exact Hnfp ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3b.  THE ROUND'S READING OF THE READ POST                            *)
  (*                                                                      *)
  (*  Lane PIPE-PROTO-2 FOLDED THIS BACK INTO [PipeProto] (this lane's     *)
  (*  finding 3 was that it is entirely general), so what is left here is  *)
  (*  the name the round is written against.                              *)
  (* ------------------------------------------------------------------- *)
  Lemma pcat_rpost (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (c : nat) (Rk : iProp Σ) (n : nat) (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    pipe_rpost_img Pt (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c)
      Rk n r M' addr -∗
    (∃ (acc : list (bv 8)) (d : nat),
       ⌜(length acc <= n)%nat /\ length acc = d⌝
       ∗ ⌜(forall i : nat, (i < d)%nat ->
             uint (add_vec_int addr (Z.of_nat i))
             = (uint addr + Z.of_nat i)%Z) ->
          forall j : nat, (j < d)%nat ->
            M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (acc !!! j)⌝
       ∗ pipe_rQ pn L c acc
       ∗ ((⌜r = (mword_of_int (Z.of_nat d) : mword 64)⌝
           ∗ (⌜d = 0%nat⌝ -∗ ⌜(0 < n)%nat⌝ -∗
                eof_shot pn (take (c + d)%nat L)))
          ∨ (⌜r = (mword_of_int (-1) : mword 64) /\ d = 0%nat⌝
             ∗ (⌜~ uva_wmapped Pt (uint (add_vec_int addr (Z.of_nat d)))⌝
                ∨ Rk ∨ ⌜n = 0%nat⌝))))
    ∨ (app_taint
       ∗ pipe_rpay (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) n).
  Proof using .
    iIntros "H". iApply (PipeProto.pipe_rpost_line with "H").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3c.  THE THREE INSTRUCTIONS OF ulib's read(), AT THE PIPE            *)
  (*  ([UkCatDeed.wp_kcat_read_deed]'s twin: [c.li a7,5 ; ecall ; c.jr     *)
  (*  ra], the ecall at 3a's leaf.)                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma pcat_read_walk (a : Z) (cnt : nat) (f : nat -> bv 8)
      (h : CpuId) (m : regfile) (avail : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (γp : pipe_names)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    0 <= a -> a < Z64 ->
    m !!! Regidx a1_idx = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
      = Z.of_nat cnt ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    cat_code γt -∗
    UserFd.ustd γfd l -∗
    pipe_rpay (pn_queue γp) Rp Rpe cnt -∗
    ubytes γd a cnt f -∗
    urun N h m (mword_of_int CatSyms.read) avail -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8)
       (M' : gmap Z (bv 8)) (Pt : uptd) (gn : gname),
       ⌜ UkReadPipe.uread_pipe_ans cnt rv ⌝ -∗
       ⌜ forall i : nat, (i < cnt)%nat ->
           uint (add_vec_int (mword_of_int a : mword 64) (Z.of_nat i))
           = (a + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < cnt)%nat ->
           M' !! uint (add_vec_int (mword_of_int a : mword 64) (Z.of_nat j))
           = Some (gb j) ⌝ -∗
       ⌜ forall j : nat, (j < cnt)%nat ->
           uva_wmapped Pt
             (uint (add_vec_int (mword_of_int a : mword 64) (Z.of_nat j))) ⌝ -∗
       pipe_rpost_img Pt (pn_queue γp) Rp Rpe (ChildTok.kill_shot gn ∗ app_taint)%I
         cnt rv M' (mword_of_int a : mword 64) -∗
       UserFd.ustd γfd l -∗
       ubytes γd a cnt gb -∗
       urun N h'
         (<[Regidx a0_idx := rv]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hahi Ha1 Hcnt Hfdv Hfdlt Hl.
    iIntros "#Hcode Hstd Hpay Hbs Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hread & _ & _ & _ & _).
    rewrite Hread.
    (* ---- 0x3c4  c.li a7,5 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3c4)
              (mword_of_int 5 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3c4 with "Hcode"). }
    assert (E0r : add_vec_int (mword_of_int 0x3c4 : mword 64) 2
                  = mword_of_int 0x3c6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emr : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 5 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0r Emr.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int a : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcntr : bv_signed (subrange_vec_dec (m1 !!! Regidx a2_idx) 31 0
                               : mword 32) = Z.of_nat cnt).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hcnt. }
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hfdv. }
    assert (Hua : uint (m1 !!! Regidx a1_idx) = a)
      by (rewrite Ha1r; apply uint_moi; unfold Z64 in *; lia).
    assert (Hua' : uint (mword_of_int a : mword 64) = a)
      by (apply uint_moi; unfold Z64 in *; lia).
    (* ---- 0x3c6  ecall -- THE PIPE'S OWN LEAF ---- *)
    iEval (rewrite <- Hua) in "Hbs".
    iDestruct (uis_cat_3c6 with "Hcode") as "#Hi3c6".
    assert (Hnum : usysno m1 = USYS_read).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int 0x3c6 : mword 64) 4))
                     2 = true)
      by (vm_compute; reflexivity).
    iPoseProof (pcat_ecall_read h1 m1 (mword_of_int 0x3c6) cnt cnt f avail
                  l fd wb γp (m1 !!! Regidx a1_idx) Rp Rpe
                  Hnum Ha0r Hfdlt Hl Hcntr ltac:(lia) Hal4 eq_refl)
      as "Hleaf".
    iApply ("Hleaf" with "Hi3c6 Hrun Hstd Hpay Hbs").
    assert (E1r : add_vec_int (mword_of_int 0x3c6 : mword 64) 4
                  = mword_of_int 0x3ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1r.
    iIntros (h2 rv d gb M' Pt gn) "%Hd %Hgf %Hans %Hlin %Himg %Hnf
                                   Hrp Hstd Hrun Hbs".
    rewrite Ha1r in Hlin. rewrite Hua' in Hlin.
    rewrite Ha1r in Himg. rewrite Ha1r in Hnf.
    iEval (rewrite Ha1r) in "Hrp".
    iEval (rewrite Hua) in "Hbs".
    set (m2 := <[Regidx a0_idx := rv]> m1).
    (* ---- 0x3ca  c.jr ra ---- *)
    assert (Hrar : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) rv
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 5 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3ca) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ca with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 rv gb M' Pt gn
              with "[%] [%] [%] [%] Hrp Hstd Hbs Hrun");
      [ exact Hans | exact Hlin | exact Himg | exact Hnf ].
  Qed.


  (* =================================================================== *)
  (*  4.  THE ROUND                                                       *)
  (*                                                                     *)
  (*  [UCatKernel.cat_round_at]'s twin, and the difference is visible in  *)
  (*  the invariant: ONE existential cursor [c], and at it BOTH the       *)
  (*  protocol's read permit and the era's console credential.  At the    *)
  (*  file claim those are two different numbers held together by an      *)
  (*  [Hpin] premise; at a pipe the read pointer IS the console cursor,   *)
  (*  because the only thing that moves it is the dequeue that produced   *)
  (*  the bytes being printed.                                           *)
  (* =================================================================== *)

  (* what one turn carries: the ledger, and the read permit AT THE CURSOR
     -- or the taint, where the protocol says nothing and the permit may
     have gone into the payment that was never returned. *)
  Definition pcat_hold (pn : pnames) (l : list fdstate) (c : nat) : iProp Σ :=
    (UserFd.ustd γfd l ∗ (rcur pn c ∨ T))%I.

  (* THE ROUND'S INVARIANT, GENERIC IN THE CURSOR (lane SH-PIPE-ROUND-4,
     design 4.3f (R3)).  [pcch] files [pcat_alt] at cat's FIRST byte,
     which is the one thing a TWO-WRITER block may not do; the round's
     proof never unfolds it, so the cursor is a parameter and the landed
     statement is re-derived at [Ch := pcch g v ps0 cs0 I0 pcat_alt P]
     below, byte-identical. *)
  Definition pcat_round_inv_g (pn : pnames) (l : list fdstate)
      (Ch : nat -> iProp Σ) : iProp Σ :=
    (∃ c : nat, pcat_hold pn l c ∗ Ch c)%I.

  Definition pcat_round_inv (pn : pnames) (l : list fdstate) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (P : nat) : iProp Σ :=
    (∃ c : nat, pcat_hold pn l c ∗ pcch g v ps0 cs0 I0 pcat_alt P c)%I.

  (* A FANCY UPDATE IN FRONT OF THE TRIVIAL-POST WP ([UConsOpen.
     fupd_wp_triv] restated; that file is not in this one's cone).
     [RiscvPtsto.wp_triv] is a DEFINITION, so the proofmode's [ElimModal]
     instance for [wp] does not see through it. *)
  Lemma pcat_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  Lemma pcat_round_at_g (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (l : list fdstate) (wb : bool) (I0 : list (bv 8))
      (Ch : nat -> iProp Σ) (Cend : iProp Σ) :
    pcat_out I0 = L ->
    (* fd 0 IS this pipe's read end, in the child's own ledger *)
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    (* THE PROTOCOL -- the whole of what cat knows about the pipe *)
    pipe_inv pn γp L -∗
    (* THE KILL ARM IS PAID BY THE KERNEL NOW (lane KILL-TAINT).  A pipe
       read answers -1 when the reader was KILLED while it waited, and
       what the post hands over at that arm is no longer the bare shot
       but [ChildTok.kill_shot gn * app_taint]: a process inside a
       syscall holds its own incarnation's marker, so a nonzero killed
       flag was written by a THIRD PARTY, who paid the taint into
       <p->lock>'s killed row ([PipeKillMark], [SchedCtx.
       kill_paid_shot_tear]).  The named premise this round used to take
       ([box (forall gn, kill_shot gn -* T)]) is GONE -- and it had to
       go: it is refutable, [PipeKillMark.kill_taint_premise_gives_T]. *)
    (* [Hdg]: cat's `read error` tail, payable at a TAINTED era out of the
       free write law ([UkCatCat.kcat_round_of_law]'s route) *)
    □ (T -∗ UkCatCat.kcat_dg_cr N) -∗
    (* [Hw]: the turn's write, at the cursor and back at the cursor plus
       the count -- COUNT-EXACT, so cat's `write error` tail is refuted
       inside the walk and this round never funds [kcat_dg_cw].  Its
       taint disjunct carries NO count bound (unlike the file round's):
       at a tainted era the cursor is the credential's right arm at every
       index, so a cursor that moves by a nonsense count is still a
       cursor. *)
    (* ...AND ITS PURE FACT IS A LOOKUP INTO [L] (design SS4.3s, lane
       SH-PIPE-ROUND-9).  It used to be a lookup into the ALTERNATIVE
       [pcont (pcat_line I0) (palt_of pcat_alt)], which is [L ++
       u_prompt] -- and that is strictly weaker, because at [c + j =
       length L] it is satisfied by the PROMPT's '$'.  The file era's
       block family steps every byte of the alternative and never
       noticed; the PIPELINE round's two-writer family steps
       [PipeBoth.rsrc L 1 = L] and nothing else, and its own [nodollar]
       premise excludes that byte ([UShPipeAssembly.pcat_hw_gap] is the
       witness).  The content arm below HAS the [L] form
       ([pcat_acc_line]) and used to weaken it here; it now passes it
       straight through, and the landed instance [pcat_round_at] weakens
       it back with [pcat_round_line], statement byte-identical. *)
    (* ...AND THE READER'S OWN LOWER BOUND (design SS4.3t, lane
       SH-PIPE-ROUND-9).  ADDITIVE: it only makes [Hw] easier to supply,
       and the landed instance [pcat_round_at] re-derives by ignoring it.
       It exists because the pipeline round's two-writer family fires its
       MODE at cat's first byte ([PipeBoth.blk2_mode_fire]) and that fire
       demands PIPE-EXEC-ECHO's [YR] -- <<a byte reached the reader>>,
       i.e. [PipeProto.pws_lb pn (take 1 L)].  Its only producer is
       [PipeProto.pws_lb_of_rcur], which needs the READER'S PERMIT; the
       content arm below holds it, one line later it is inside
       [UkCat.kcat_wr_mono]'s post-transformer and out of [Hw]'s reach.
       So it is taken here, at the read's own WP point, and forwarded. *)
    □ (∀ (c nb : nat) (rv : mword 64) (fbb : nat -> bv 8),
         ⌜rv = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
         (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
           /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                L !! (c + j)%nat = Some (fbb j)⌝
          ∨ T) -∗
         (pws_lb pn (take (c + Z.to_nat (bv_unsigned rv))%nat L) ∨ T) -∗
         UserFd.ustd γfd l -∗
         Ch c -∗
         UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
           (ubytes γd CatSyms.buf 512 fbb)
           (fun wret : mword 64 =>
              (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
               ∗ UserFd.ustd γfd l
               ∗ Ch
                   (c + Z.to_nat (bv_unsigned rv))%nat
               ∗ ubytes γd CatSyms.buf 512 fbb))) -∗
    (* [Hend]: the loop's NORMAL exit, which is END OF FILE -- the read
       answered zero, and the protocol's one-shot says the pipe's whole
       contents are the bytes cat has printed. *)
    □ (∀ c : nat,
         (eof_shot pn (take c L) ∨ T) -∗
         pcat_hold pn l c -∗
         Ch c -∗ Cend) -∗
    cat_code γt -∗
    UkCatCat.kcat_round N (mword_of_int 0)
      (pcat_round_inv_g pn l Ch) Cend.
  Proof using Hcons Hkill.
    intros HL Hl0.
    iIntros "#Hinv #Hdg #Hw #Hend #Hcode".
    assert (Hm1s : bv_signed (mword_of_int (-1) : mword 64) = -1)
      by (vm_compute; reflexivity).
    rewrite /UkCatCat.kcat_round. iModIntro.
    iIntros (h m avail f) "%Ha0 %Ha1 %Ha2 _ HI Hbuf Hrun Hcont".
    rewrite /pcat_round_inv_g.
    iDestruct "HI" as (c) "[[Hstd Hcur] Hc]".
    (* THE PAYMENT: the protocol at the cursor, or the taint *)
    iAssert (pipe_rpay (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) 512)
      with "[Hcur]" as "Hpay".
    { iDestruct "Hcur" as "[Hr | #HT]".
      - iApply (pipe_rpay_of_inv pn γp L c 512 with "Hinv Hr").
      - iApply pipe_rpay_taint. rewrite Hkill. iExact "HT". }
    assert (Hfd0 : bv_signed (trunc32 (m !!! Regidx a0_idx))
                   = Z.of_nat 0%nat)
      by (rewrite Ha0; vm_compute; reflexivity).
    iApply (pcat_read_walk CatSyms.buf 512%nat f h m avail l 0%nat wb γp
              (pipe_rQ pn L c) (pipe_rQe pn L c)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              Ha1 Ha2 Hfd0 ltac:(vm_compute; lia) Hl0
              with "Hcode Hstd Hpay Hbuf Hrun").
    iIntros (h' rv gb M' Pt gn) "%Hans %Hlin %Himg %Hnf Hrp Hstd Hbuf Hrun".
    (* SS4.3t: THE POST IS SPLIT HERE, BEFORE [Hcont], so that the content
       arm still has an [mWP] goal to spend [pws_lb_of_rcur]'s fancy
       update at. *)
    iDestruct (pcat_rpost with "Hrp") as "[Hgood | [#HTa _]]"; last first.
    { (* THE TAINT ARM of the post: everything from the taint *)
      iAssert T as "#HT"; [ rewrite -Hkill; iExact "HTa" | ].
      iApply ("Hcont" $! h' rv gb with "[Hstd Hc] Hbuf Hrun").
      iSplit; [| iSplit ].
      - iIntros "_". iApply ("Hdg" with "HT").
      - iIntros "_".
        iApply ("Hend" $! c with "[] [Hstd] Hc"); [ by iRight | ].
        rewrite /pcat_hold. iFrame "Hstd". by iRight.
      - iIntros (nb) "%Hret _".
        iApply (UkCat.kcat_wr_mono N (mword_of_int 1)
                  (mword_of_int CatSyms.buf) nb
                  (ubytes γd CatSyms.buf 512 gb)
                  (fun wret : mword 64 =>
                     (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
                      ∗ UserFd.ustd γfd l
                      ∗ Ch
                          (c + Z.to_nat (bv_unsigned rv))%nat
                      ∗ ubytes γd CatSyms.buf 512 gb)%I)
                  _ with "[] [Hstd Hc]").
        { iIntros (wret) "(%Hws & Hstd & Hc' & Hb)".
          iSplitR "Hb"; [ | iExact "Hb" ].
          iLeft. iSplitR; [ by iPureIntro | ].
          rewrite /pcat_round_inv_g.
          iExists (c + Z.to_nat (bv_unsigned rv))%nat.
          iSplitR "Hc'"; [ | iExact "Hc'" ].
          rewrite /pcat_hold. iFrame "Hstd". by iRight. }
        iApply ("Hw" $! c nb rv gb with "[%] [] [] Hstd Hc");
          [ exact Hret | by iRight | by iRight ]. }
    (* THE CONTENT ARM *)
    iDestruct "Hgood" as (acc d) "([%Hlen %Hd] & %Himg2 & HQ & Harm)".
    iDestruct "HQ" as "[Hr %Hacc]".
    assert (Hd512 : (d <= 512)%nat) by lia.
    (* the bytes the call delivered ARE the line's, at the cursor *)
    assert (Hbytes : forall j : nat, (j < d)%nat ->
              L !! (c + j)%nat = Some (gb j)).
    { intros j Hj.
      assert (Hj' : (j < length acc)%nat) by lia.
      rewrite (pcat_acc_line L acc c Hacc j Hj').
      f_equal. symmetry.
      assert (Hm : M' !! uint (add_vec_int (mword_of_int CatSyms.buf : mword 64)
                                 (Z.of_nat j)) = Some (acc !!! j))
        by (apply (Himg2 ltac:(intros i Hi; apply Hlin; lia)); lia).
      rewrite (Himg j ltac:(lia)) in Hm. by injection Hm as <-. }
    (* SS4.3t: THE READER'S LOWER BOUND, taken at the read's own WP point *)
    iApply pcat_fupd_mwp.
    iMod (pws_lb_of_rcur ⊤ pn γp L (c + length acc)%nat
            ltac:(apply top_subseteq) with "Hinv Hr") as "[Hr #Hlb2]".
    iModIntro.
    iApply ("Hcont" $! h' rv gb with "[Hr Hstd Hc Harm] Hbuf Hrun").
    iDestruct "Harm" as "[[%Hrv Heof] | [[%Hrv %Hd0] Hwhy]]"; last first.
    { (* THE -1 ARMS: two are refuted, the third is the KILL *)
      iAssert T as "#HT".
      { iDestruct "Hwhy" as "[%Hnm | [Hk | %Hn0]]".
        - exfalso. apply Hnm. rewrite Hd0. apply Hnf. lia.
        - iDestruct "Hk" as "[_ HTa]". rewrite -Hkill. iExact "HTa".
        - exfalso. lia. }
      iSplit; [| iSplit ].
      - iIntros "_". iApply ("Hdg" with "HT").
      - iIntros "%Hz". exfalso. rewrite Hrv Hm1s in Hz. lia.
      - iIntros (nb) "%Hret _".
        iApply (UkCat.kcat_wr_mono N (mword_of_int 1)
                  (mword_of_int CatSyms.buf) nb
                  (ubytes γd CatSyms.buf 512 gb)
                  (fun wret : mword 64 =>
                     (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
                      ∗ UserFd.ustd γfd l
                      ∗ Ch
                          (c + Z.to_nat (bv_unsigned rv))%nat
                      ∗ ubytes γd CatSyms.buf 512 gb)%I)
                  _ with "[] [Hstd Hc]").
        { iIntros (wret) "(%Hws & Hstd & Hc' & Hb)".
          iSplitR "Hb"; [ | iExact "Hb" ].
          iLeft. iSplitR; [ by iPureIntro | ].
          rewrite /pcat_round_inv_g.
          iExists (c + Z.to_nat (bv_unsigned rv))%nat.
          iSplitR "Hc'"; [ | iExact "Hc'" ].
          rewrite /pcat_hold. iFrame "Hstd". by iRight. }
        iApply ("Hw" $! c nb rv gb with "[%] [] [] Hstd Hc");
          [ exact Hret | by iRight | by iRight ]. }
    (* THE COUNT ARM: the answer is [d], and [d] is at most 512 *)
    assert (Hbu : bv_unsigned rv = Z.of_nat d).
    { rewrite Hrv -uint_unsigned. apply uint_moi. unfold Z64. lia. }
    assert (Hto : Z.to_nat (bv_unsigned rv) = d)
      by (rewrite Hbu Nat2Z.id; reflexivity).
    assert (Hsg : bv_signed rv = Z.of_nat d).
    { rewrite (pcat_signed_small rv ltac:(rewrite Hbu; lia)). exact Hbu. }
    iSplit; [| iSplit ].
    - (* cat's `read error` is REFUTED at a real count *)
      iIntros "%Hneg". exfalso. rewrite Hsg in Hneg. lia.
    - (* END OF FILE: the read answered zero *)
      iIntros "%Hz". rewrite Hsg in Hz.
      assert (Hd00 : d = 0%nat) by lia.
      iDestruct ("Heof" with "[%] [%]") as "#Hs";
        [ exact Hd00 | lia | ].
      rewrite Hd00 in Hd.
      rewrite Hd00. rewrite Hd. rewrite Nat.add_0_r.
      iApply ("Hend" $! c with "[] [Hstd Hr] Hc"); [ by iLeft | ].
      rewrite /pcat_hold. iFrame "Hstd". iLeft. iExact "Hr".
    - (* THE TURN'S WRITE, at the cursor *)
      iIntros (nb) "%Hret %Hnb0".
      iApply (UkCat.kcat_wr_mono N (mword_of_int 1)
                (mword_of_int CatSyms.buf) nb
                (ubytes γd CatSyms.buf 512 gb)
                (fun wret : mword 64 =>
                   (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
                    ∗ UserFd.ustd γfd l
                    ∗ Ch
                        (c + Z.to_nat (bv_unsigned rv))%nat
                    ∗ ubytes γd CatSyms.buf 512 gb)%I)
                _ with "[Hr] [Hstd Hc]").
      { iIntros (wret) "(%Hws & Hstd & Hc' & Hb)".
        iSplitR "Hb"; [ | iExact "Hb" ].
        iLeft. iSplitR; [ by iPureIntro | ].
        rewrite /pcat_round_inv_g.
        iExists (c + Z.to_nat (bv_unsigned rv))%nat.
        iSplitR "Hc'"; [ | iExact "Hc'" ].
        rewrite /pcat_hold. iFrame "Hstd". iLeft.
        rewrite Hto -Hd. iExact "Hr". }
      iApply ("Hw" $! c nb rv gb with "[%] [] [] Hstd Hc");
        [ exact Hret | | ].
      { iLeft. iPureIntro. rewrite Hto. split; [ exact Hd512 | ].
        exact Hbytes. }
      { iLeft. rewrite Hto -Hd. iExact "Hlb2". }
  Qed.


  (* ...AND THE LANDED STATEMENT, BYTE-IDENTICAL, at cat's own cursor
     ([git diff] shows only the proof).  This is the consumer the FILE
     era's twin has; the pipeline round uses [pcat_round_at_g] at the
     two-writer family's right cursor instead. *)
  Lemma pcat_round_at (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (l : list fdstate) (wb : bool) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (P : nat) (Cend : iProp Σ) :
    pcat_stage ps0 cs0 I0 P ->
    pcat_out I0 = L ->
    (* fd 0 IS this pipe's read end, in the child's own ledger *)
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    (* THE PROTOCOL -- the whole of what cat knows about the pipe *)
    pipe_inv pn γp L -∗
    (* THE KILL ARM IS PAID BY THE KERNEL NOW (lane KILL-TAINT).  A pipe
       read answers -1 when the reader was KILLED while it waited, and
       what the post hands over at that arm is no longer the bare shot
       but [ChildTok.kill_shot gn * app_taint]: a process inside a
       syscall holds its own incarnation's marker, so a nonzero killed
       flag was written by a THIRD PARTY, who paid the taint into
       <p->lock>'s killed row ([PipeKillMark], [SchedCtx.
       kill_paid_shot_tear]).  The named premise this round used to take
       ([box (forall gn, kill_shot gn -* T)]) is GONE -- and it had to
       go: it is refutable, [PipeKillMark.kill_taint_premise_gives_T]. *)
    (* [Hdg]: cat's `read error` tail, payable at a TAINTED era out of the
       free write law ([UkCatCat.kcat_round_of_law]'s route) *)
    □ (T -∗ UkCatCat.kcat_dg_cr N) -∗
    (* [Hw]: the turn's write, at the cursor and back at the cursor plus
       the count -- COUNT-EXACT, so cat's `write error` tail is refuted
       inside the walk and this round never funds [kcat_dg_cw].  Its
       taint disjunct carries NO count bound (unlike the file round's):
       at a tainted era the cursor is the credential's right arm at every
       index, so a cursor that moves by a nonsense count is still a
       cursor. *)
    □ (∀ (c nb : nat) (rv : mword 64) (fbb : nat -> bv 8),
         ⌜rv = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
         (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
           /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                pcont (pcat_line I0) (palt_of pcat_alt) !! (c + j)%nat
                = Some (fbb j)⌝
          ∨ T) -∗
         UserFd.ustd γfd l -∗
         pcch g v ps0 cs0 I0 pcat_alt P c -∗
         UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
           (ubytes γd CatSyms.buf 512 fbb)
           (fun wret : mword 64 =>
              (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
               ∗ UserFd.ustd γfd l
               ∗ pcch g v ps0 cs0 I0 pcat_alt P
                   (c + Z.to_nat (bv_unsigned rv))%nat
               ∗ ubytes γd CatSyms.buf 512 fbb))) -∗
    (* [Hend]: the loop's NORMAL exit, which is END OF FILE -- the read
       answered zero, and the protocol's one-shot says the pipe's whole
       contents are the bytes cat has printed. *)
    □ (∀ c : nat,
         (eof_shot pn (take c L) ∨ T) -∗
         pcat_hold pn l c -∗
         pcch g v ps0 cs0 I0 pcat_alt P c -∗ Cend) -∗
    cat_code γt -∗
    UkCatCat.kcat_round N (mword_of_int 0)
      (pcat_round_inv pn l v ps0 cs0 I0 P) Cend.
  (* THE STATEMENT ABOVE IS BYTE-IDENTICAL (design SS4.3s): its [Hw] keeps
     the ALTERNATIVE's lookup, which is what the file-era consumer
     supplies.  Only the proof moved -- the generic round now asks for
     the [L] form and [pcat_round_line] is the weakening, applied here
     where it used to be applied inside. *)
  Proof using Hcons Hkill.
    intros Hst HL Hl0. iIntros "#Hinv #Hdg #Hw #Hend #Hcode".
    iApply (pcat_round_at_g pn γp L l wb I0
              (pcch g v ps0 cs0 I0 pcat_alt P) Cend HL Hl0
              with "Hinv Hdg [] Hend Hcode").
    iIntros "!>" (c nb rv fbb) "%Hrv Hjust _ Hstd Hc".
    iApply ("Hw" $! c nb rv fbb with "[%] [Hjust] Hstd Hc");
      [ exact Hrv | ].
    iDestruct "Hjust" as "[%Hp | #HT]"; [ | by iRight ].
    destruct Hp as [Hle Hlk]. iLeft. iPureIntro.
    split; [ exact Hle | ].
    exact (pcat_round_line I0 L c (Z.to_nat (bv_unsigned rv)) fbb HL Hlk).
  Qed.

  (* =================================================================== *)
  (*  5.  THE EXIT ROW, OUT OF THE REGISTRY                               *)
  (*                                                                     *)
  (*  cat's table after sh's dance is [R; c; c] -- slot 0 the pipe's READ *)
  (*  END, slots 1 and 2 the console -- above whatever exec left closed.  *)
  (*  kexit's per-descriptor close payments ([UkRun.urun_nopipe], design  *)
  (*  SS2's registry) are then ONE registration for slot 0 and [emp] for  *)
  (*  every other row, and the registration comes out of the protocol's   *)
  (*  own handle.  This is design SS2's claim, at cat: a VERIFIED PROGRAM *)
  (*  THAT HOLDS A PIPE AND IS NOT TAINTED.                               *)
  (* =================================================================== *)
  Lemma pcat_urun_nopipe (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (rb wb : bool) (rest : list fdstate) :
    fdv_nopipe rest ->
    pipe_inv pn γp L -∗
    UkRun.urun_nopipe (FdOpen rb wb (FdPipe γp) :: rest).
  Proof using .
    intros Hrest. iIntros "#Hinv".
    iApply UkRun.urun_nopipe_regs.
    rewrite big_sepL_cons. iSplitR.
    - iApply srow_reg_of_pipe_reg. iApply (pipe_reg_of_inv with "Hinv").
    - iApply (UkRun.srow_regs_nopipe rest Hrest).
  Qed.

  (* =================================================================== *)
  (*  6.  THE CONSUMER TEST, at the concrete line "hi\n"                  *)
  (*                                                                     *)
  (*  A RESOURCE-LEVEL test, as PIPE-PROTO's was and for the same reason: *)
  (*  a WP test would have to supply cat's instruction stream, registers  *)
  (*  and heap, and the walk they go through is SS4's round.  What is     *)
  (*  tested is the three seams the round spends -- the first read's      *)
  (*  payment at cursor 0, a turn that delivered the whole line printing  *)
  (*  EXACTLY the round's first three block bytes, and the second read's  *)
  (*  end-of-file handing over the payload at the frozen contents.        *)
  (* =================================================================== *)
  Definition pcat_hi : list (bv 8) := (sb "hi"%string ++ [wl_nl])%list.

  Lemma pcat_hi_len : length pcat_hi = 3%nat.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma pcat_round_test (pn : pnames) (γp : pipe_names) (I0 : list (bv 8)) :
    pcat_out I0 = pcat_hi ->
    pipe_inv pn γp pcat_hi -∗ rtok pn -∗
    (* (a) THE FIRST READ IS PAID, at cursor 0 *)
    pipe_rpay (pn_queue γp) (pipe_rQ pn pcat_hi 0)
      (pipe_rQe pn pcat_hi 0) 512
    (* (b) A TURN THAT DELIVERED THE WHOLE LINE prints exactly the round's
           first three block bytes and leaves the cursor at 3 *)
    ∗ □ (∀ acc : list (bv 8),
           ⌜length acc = 3%nat⌝ -∗
           pipe_rQ pn pcat_hi 0 acc -∗
           ⌜forall j : nat, (j < 3)%nat ->
              pcont (pcat_line I0) (palt_of pcat_alt) !! j
              = Some (acc !!! j)⌝
           ∗ rcur pn 3%nat)
    (* (c) THE SECOND READ ANSWERS ZERO at end of file, and cat's exit
           payload is the frozen contents -- the whole line *)
    ∗ □ (∀ s : pipe_st, ⌜pst_eof s⌝ -∗ pipe_rQe pn pcat_hi 3%nat [] s -∗
           rcur pn 3%nat ∗ eof_shot pn pcat_hi).
  Proof using .
    intros HL. iIntros "#Hinv Hr".
    iSplitL "Hr".
    { iApply (pipe_rpay_of_inv pn γp pcat_hi 0%nat 512%nat with "Hinv Hr"). }
    iSplit.
    - iIntros "!>" (acc) "%Hlen [Hr %Hacc]". rewrite Hlen.
      iSplitR; [ | iExact "Hr" ]. iPureIntro.
      intros j Hj.
      assert (Hj' : (0 + j < 3)%nat) by lia.
      exact (pcat_round_line I0 pcat_hi 0%nat 3%nat
               (fun k => acc !!! k) HL
               ltac:(intros k Hk;
                     exact (pcat_acc_line pcat_hi acc 0%nat Hacc k
                              ltac:(lia)))
               j Hj).
    - iIntros "!>" (s) "%Heof Hqe".
      iDestruct (pipe_rQe_eof pn pcat_hi 3%nat [] s Heof with "Hqe")
        as "[[Hr _] #Hs]".
      assert (Ht : take (3 + length (@nil (bv 8)))%nat pcat_hi = pcat_hi)
        by (vm_compute; reflexivity).
      rewrite Ht. iFrame "Hr". iExact "Hs".
  Qed.


End UCatPipe.

(* ===================================================================== *)
(*  7.  cat's ENTRY, AT argv ["cat"]                                      *)
(*                                                                       *)
(*  [UCatKernel.cat_image_entry]'s twin at the PIPELINE line's right      *)
(*  command, and the difference is ONE number: the line is `cat` with no  *)
(*  argument, so [argc = 1] and main takes its [argc <= 1] branch --      *)
(*  [cat(0)], the standard input.  THE `cannot open` ARM IS THEREFORE     *)
(*  UNREACHABLE, and the refutation is not a wish: [UkCatMain.            *)
(*  kcat_pay_all] is an ADDITIVE conjunction whose second arm is guarded  *)
(*  on [2 <= length args], [UShCat.cat_args] has [Z.to_nat (uvis_argc W)] *)
(*  entries, and the key's own reading ([UShCat.cat_key_args_holds])      *)
(*  makes that number the node's word count -- which sh built at ONE.     *)
(*  So the payment below discharges the open arm by [lia] and never       *)
(*  mentions [UkCatMain.kcat_dg_open], the file name, the cwd or the      *)
(*  persisted argument area -- all four of which [UCatKernel.cat_pay_at]  *)
(*  carries and all four of which exist only to resolve argv[1].          *)
(*                                                                       *)
(*  IT IS ITS OWN SECTION, for [UCatKernel]'s reason: an entry ALLOCATES  *)
(*  the record its payment is owed at, and a section [uk_names] variable  *)
(*  under that quantifier is durable-notes' non-terminating [iApply].     *)
(* ===================================================================== *)
Section UCatPipeEntry.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* THE PROGRAM INSTANCE IS A SECTION VARIABLE (design SS4.3z item 2):
     [pcat_pay_at]'s body names [UkCatMain.kcat_pay_all] and
     [pcat_pay_at_of_round]'s premise [UkCatCat.kcat_round], both of which
     are [uprogSG]-generic, and the payment interface has to be nameable at
     the instance the ENTERING APPLICATION runs cat at. *)
  Context `{PS : UexecSG.uprogSG Σ}.

  (* WHAT cat's ENTRY OWES ITS PAYER, at the key the entry is about to
     allocate the record for.  [UCatKernel.cat_pay_at] minus everything
     argv[1] needed. *)
  Definition pcat_pay_at (W : uvis) (Q : Z -> iProp Σ) (Pay : iProp Σ)
    : iProp Σ :=
    (∀ N : uk_names Σ,
       ⌜ ukn_pay N = Q ⌝ -∗
       (* THE LINE IS `cat`, WITH NO ARGUMENT *)
       ⌜ Z.to_nat (uvis_argc W) = 1%nat ⌝ -∗
       UserFd.ustd (ukn_fd N) (take NSTD (uvis_fd W)) -∗
       UCodeCat.cat_code (ukn_t N) -∗
       UCodeCat.cat_rodata (ukn_t N) -∗
       UserHeap.uargv (ukn_d N) (uvis_av W) (UShCat.cat_args W) -∗
       Pay -∗
       ∃ Ci : iProp Σ,
         UkCatMain.kcat_pay_all N (UShCat.cat_args W) Ci (ukn_pay N (-1))
         ∗ Ci)%I.

  (* ===================================================================== *)
  (*  [pcat_image_entry] IS RETIRED (lane SH-PIPE-ROUND-5 part 2, design    *)
  (*  SS4.3j; the vacuity is lane EXEC-CAT's finding).                      *)
  (*                                                                       *)
  (*  It stated the (E) half of cat's entry at premises NO CALLER CAN EVER  *)
  (*  MEET: [EchoDisc.line_ok ws] and [length ws = 1%nat] are jointly       *)
  (*  unsatisfiable ([line_ok] contains [2 <= length ws]), and its          *)
  (*  [line_ok] also fixes [ws !! 0 = Some cmd_echo] -- so relaxing the     *)
  (*  count alone would leave a premise saying the command is called        *)
  (*  `echo`.  Both halves are mechanised in [UkShCat.                      *)
  (*  cat_line_premises_absurd] / [cat_line_head_absurd].  The lemma had    *)
  (*  no caller anywhere in the tree.                                       *)
  (*                                                                       *)
  (*  THE ENTRY TO USE IS [UShCatPay.cat_image_entry_1w]: the same body at  *)
  (*  premises a ONE-WORD line meets ([UkShCat.cat_argv_bytes] and          *)
  (*  [ExecArgs.uargv_img] over the general argument layer, no word list    *)
  (*  anywhere), keeping [pcat_pay_at] below as the payment interface so    *)
  (*  that [pcat_pay_at_of_round] plugs into it unchanged.  It could not be *)
  (*  stated HERE: its premises live in [UkShCat.v] and [UShCatPay.v],      *)
  (*  both of which are ABOVE this file ([UShCatPay] imports it, to name    *)
  (*  [pcat_pay_at]).                                                      *)
  (* ===================================================================== *)

  (* ...AND THE `cannot open` ARM IS UNREACHABLE, mechanised: at argc = 1
     the payment's SECOND conjunct is vacuous, so a payer supplies the
     round at fd 0 and NOTHING ELSE -- no open obligation, no [kcat_dg_open]
     and no file name.  This is the brief's item 2, and it is what makes
     cat-at-a-pipe cheaper than cat-at-a-file rather than merely different. *)
  Lemma pcat_pay_at_of_round (W : uvis) (Q : Z -> iProp Σ) (Pay : iProp Σ)
      (l : list fdstate) :
    take NSTD (uvis_fd W) = l ->
    (* the round at fd 0, and what its normal exit leaves *)
    □ (∀ N : uk_names Σ, ⌜ukn_pay N = Q⌝ -∗
         UserFd.ustd (ukn_fd N) l -∗ Pay -∗
         ∃ I Cend : iProp Σ,
           UkCatCat.kcat_round N (mword_of_int 0) I Cend ∗ I
           ∗ (Cend -∗ ukn_pay N (-1))) -∗
    pcat_pay_at W Q Pay.
  Proof using .
    intros Hl. iIntros "#Hround". rewrite /pcat_pay_at.
    iIntros (N) "%Hpayeq %Hargc1 Hstd _ _ _ HPay".
    rewrite Hl.
    iDestruct ("Hround" $! N with "[%] Hstd HPay") as (I Cend) "(Hr & HI & He)";
      [ exact Hpayeq | ].
    iExists emp%I. iSplitR "".
    - rewrite /UkCatMain.kcat_pay_all. iSplit.
      + iIntros "_". iExists Cend. iSplitR "He".
        * rewrite /UkCatMain.kcat_run0. iExists I, Cend. iFrame "Hr HI".
          by iIntros "$".
        * iIntros "[_ Hc]". iApply ("He" with "Hc").
      + (* THE OPEN ARM IS UNREACHABLE: argc is ONE *)
        iIntros "%Hge". exfalso.
        rewrite /UShCat.cat_args echo_args_length Hargc1 in Hge. lia.
    - done.
  Qed.

End UCatPipeEntry.
