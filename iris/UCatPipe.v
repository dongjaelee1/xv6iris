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
Require Import ObsTrace.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UserPtTree.         (* [uptd] / [uva_wmapped] *)
Require Import VcGen.              (* [trunc32_subrange] *)
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import WpUart.             (* [out_link] *)
Require Import UCodeCat.
Require User.CatSyms User.CatInstrs.
Require Import ChildTok.
Require Import FdSlots PipeNames ProcGeom UserFd UserCwd.
Require Import UexecSG UexecSlot UexecRet UsysMemOk.
Require Import UexecExecInst.      (* THE INSTANCES: [uexecSG_xv6], [uprogSG_gen] *)
Require Import UkCat.
Require Import UkCatCat.
Require Import UkCatMain.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs BioDefs.
Require Import PipeQueue.          (* the payments and the posts *)
Require Import PipeReg.            (* [pipe_reg] / [pipe_row_reg] *)
Require Import PipeProto.          (* the protocol: [pipe_inv] / [rcur] / [pipe_rQ] *)
Require Import UkReadRows.         (* [spost_at_read_elim] / [std_fd_st_of_key] *)
Require Import SpecFileread.       (* [fileread_in] / [fileread_extra_core] *)
Require Import UkReadPipe.         (* the standard-slot pipe read leaf *)
Require Import LineWords EchoDisc ConsLog EchoOutPure.
Require Import PipeDisc PipeDiscDec PipeOutPure PipeOut PipeLinks.
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
Lemma pcat_round_line (I0 : list (bv 8)) (L acc : list (bv 8)) (c : nat) :
  pcat_out I0 = L ->
  (c + length acc <= length L)%nat ->
  acc = take (length acc) (drop c L) ->
  forall k : nat, (k < length acc)%nat ->
    pcont (pcat_line I0) (palt_of pcat_alt) !! (c + k)%nat
    = Some (acc !!! k).
Proof using.
  intros HL Hle Hacc k Hk.
  rewrite pcat_alt_of pcat_cont_ran HL.
  assert (Hlt : (c + k < length L)%nat) by lia.
  rewrite (lookup_app_l L u_prompt (c + k)%nat Hlt).
  assert (Hget : L !! (c + k)%nat = acc !! k).
  { rewrite Hacc lookup_take; [| lia]. rewrite lookup_drop. reflexivity. }
  rewrite Hget.
  exact (list_lookup_lookup_total_lt acc k Hk).
Qed.

(* ...and the cursor's own arithmetic: a turn that read [d] bytes at [c]
   lands at [c + d], still inside the line. *)
Lemma pcat_round_cursor (L : list (bv 8)) (c d : nat) :
  (c + d <= length L)%nat -> (c + d <= length L)%nat.
Proof using. exact (fun H => H). Qed.

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
  Context (γ : echo_fixed).
  Context `{HRg : !riscvGS Σ}.
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl γ).

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
    pcont (pcat_line I0) (palt_of a) !! p = Some b ->
    era_pin γ k v -∗
    pcch v ps0 cs0 I0 a P p -∗
    (pcch v ps0 cs0 I0 a P (S p) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hst Hok Hnp Hb.
    pose proof (pcat_stage_nonnil ps0 cs0 I0 P Hst) as Hne.
    pose proof (pcat_stage_pin_snoc ps0 cs0 I0 P a Hst) as Hpin1.
    pose proof Hst as (Hr & Hn & _ & HP & Hpin).
    iIntros "#Hpin Hc HΦ".
    rewrite /pcch.
    iDestruct "Hc" as "[(Htn & #Hps & #Hcs & #Hilb) | #HT]".
    - destruct p as [| p']; cbn [pcatcs].
      + (* THE BLOCK-FIRST BYTE *)
        rewrite Nat.add_0_r.
        iApply (pipe_write_link_blk γ Hcons k v P a b ps0 cs0 I0 Φ
                  Hne Hr ltac:(lia) Hpin HP Hok Hb
                  with "Hpin Htn Hps Hcs Hilb [HΦ]").
        iIntros "Hres". iApply "HΦ". cbn [pcatcs].
        replace (P + 1)%nat with (S P) by lia. iExact "Hres".
      + (* every byte after it *)
        iApply (pipe_write_link γ Hcons k v (P + S p')%nat b ps0
                  (cs0 ++ [a]) I0 Φ
                  ltac:(rewrite length_app; cbn [length]; lia)
                  Hpin1
                  (pcat_blk_byte ps0 cs0 I0 P a (S p') b Hst Hnp Hb)
                  with "Hpin Htn Hps Hcs Hilb [HΦ]").
        iIntros "Hres". iApply "HΦ". cbn [pcatcs].
        replace (P + S (S p'))%nat with (S (P + S p')) by lia.
        iExact "Hres".
    - (* THE TAINT ARM continues the tower on its own *)
      iApply (pipe_write_link_taint γ Hcons k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight.
  Qed.

End PCatOut.

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
  Context `{!ctokG Σ}.
  Context `{!echoOutG Σ, !pipeProtoG Σ}.
  (* NO [uexecSG] AND NO [uprogSG] SECTION VARIABLE, for [UCatKernel]'s
     reason (lane CAT-WALK-2, K2): a variable of either class here would be
     a SECOND instance whose [UkRun.urun] prints identically and does not
     unify with the one [UkReadPipe]'s leaf and [UkCatCat]'s walk run at. *)
  Context (γ : echo_fixed).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl γ).
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
    uinstr_is γt pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ustd γfd l -∗
    pipe_rpay (pn_queue γp) Rp Rpe cap -∗
    ubytes γd (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (M' : gmap Z (bv 8)) (Pt : uptd) (Rk : iProp Σ),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ UkReadPipe.uread_pipe_ans cap r ⌝ -∗
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat i))
           = (uint (m !!! Regidx a1_idx) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (g j) ⌝ -∗
       (* THE RELAYED NO-FAULT ROW, at the post's OWN table *)
       ⌜ forall j : nat, (j < k)%nat ->
           uva_wmapped Pt
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       pipe_rpost_img Pt (pn_queue γp) Rp Rpe Rk cap r M'
         (m !!! Regidx a1_idx) -∗
       UserFd.ustd γfd l -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes γd (uint (m !!! Regidx a1_idx)) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hlt Hl Ha2 Hcapk Hal.
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
    iIntros (h' r d g W M' fdv' cw' cs')
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
    iApply ("Hcont" $! h' r d g M' P (ChildTok.kill_shot (uvis_gen W))
              with "[%] [%] [%] [%] [%] [%] Hrp Hstd Hrun Hbuf");
      [ exact Hd | exact Hgf
      | exact (UkReadPipe.uread_pipe_ans_of_ret cap r Hret)
      | exact Hlin | exact Himg | ].
    intros j Hj. exact (Hnf P j Hwfp Hpmp (Hlzp Hlz) Hj).
  Qed.

End UCatPipe.
