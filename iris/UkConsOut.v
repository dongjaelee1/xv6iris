(* ===================================================================== *)
(* UkConsOut.v -- THE CONSOLE AS AN OUTPUT DEVICE of the endpoint         *)
(* interface, at the GENERIC console claim, for ANY program instance      *)
(* (program-specs cut 4(c), the console).                                 *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4, SS3.4b.  [UkHandler. *)
(* ep_iface]'s write law, specialised to the console: a device owing one  *)
(* of [alts] funds [UkTree.wr_obl] for a chunk [bs] of a chosen           *)
(* alternative [a], answers exactly [length bs] and then owes             *)
(* [drop (length bs) a].  [UCatKernel.cat_w_of_link] is the mould, and    *)
(* this differs from it in three ways only: any program (the stub law     *)
(* [UkStub.stub_law] in place of cat's stub), any alternative (the code   *)
(* is read off [a ∈ alts]), both source halves (data and text, as         *)
(* [UEchoOut] S4 has them).                                               *)
(*                                                                        *)
(* THE ENCODING OF [cons_dev alts].  Beside [cons_short alts] (every      *)
(* alternative is below 2^31 bytes: the kernel reads the count as a C     *)
(* [int], so a longer write does not answer its length -- this is the one *)
(* fact the TAINT arm needs too), the device is                           *)
(*                                                                        *)
(*   - the era's cursor at a block of the writer's stage                   *)
(*     ([lm_wr_blk_t], exactly [GenLinksLine.gwc_blk]'s left arm, with     *)
(*     its witnesses NAMED, because the continuation bytes are read at     *)
(*     them: [lm_abs s0 cs I c] is alternative [c]'s continuation at the   *)
(*     round's own state), and the era's pin, and EITHER                  *)
(*       UNFILED, at the block's first byte: [alts] is the continuations  *)
(*       of a list of CODES [codes], each admissible at the line typed    *)
(*       ([cons_adm]: [lm_ok] and not coverage-ending), so that            *)
(*       [a ∈ alts] picks a code; the list need not be all of them (a     *)
(*       device owing fewer alternatives is a stronger obligation on the   *)
(*       program, and no line model's code space is finite);              *)
(*     OR FILED at code [c] and position [i > 0]:                          *)
(*       [alts = [drop i (lm_abs s0 cs I c)]];                             *)
(*   - or the era's taint, which funds every byte and stays.              *)
(*                                                                        *)
(* [gwc_blk] itself is not used because it lives over M2's link           *)
(* parameters ([gen_params]) and hides its witnesses; here the claim's    *)
(* own parameters ([gen_cparams]) and [GenLinks]' links are the whole     *)
(* supply, and the arm is [gwc_blk]'s word for word.                      *)
(*                                                                        *)
(* THE PROOF.  [cons_dev_sub] narrows the device to [[a]]; [cons_dev_step] *)
(* is one byte ([GenLinks.gwrite_link_blk] at an unfiled device -- it     *)
(* files the code -- and [gwrite_link] at a filed one; the taint through  *)
(* [gwrite_link_taint]); [cons_chain] is the console chain the write      *)
(* leaf's deposit asks for, at the cursor [j ↦ cons_dev [drop j a]];      *)
(* [cons_write] runs the stub law to the ecall, the leaf of the source's  *)
(* half ([cons_leaf]) between, reads the exact count off                  *)
(* [UkWriteLeaf.uwrite_no_short] and returns through the stub.  The       *)
(* source run is SPLIT in two ([usrc_at_split], at any fraction): one     *)
(* half is lent to the leaf, the other rides the deposit (the chain's     *)
(* per-byte premise is read off it) and comes home in the post.           *)
(*                                                                        *)
(* S4: the witnesses at echo and at cat.                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import agree.
From iris.algebra.lib Require Import gmap_view.
From iris.base_logic.lib Require Import own ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import VcGen.              (* [trunc32_subrange] *)
Require Import KstackArith.        (* [bvsigned_moi_small] *)
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import EchoOut.
Require Import GenOutHist.
Require Import GenOut.
Require Import GenLinks.
Require Import CtxIdDefs.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
(* [UserHeap] LAST among the U-tier libraries, as [UEchoOut] has it:
   [UmodeAbi.uargs] has fields that shadow [UserHeap.uarg]'s. *)
Require Import UserHeap.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  S1  THE PURE HALF                                                     *)
(* ===================================================================== *)

(* a fraction, halved: two halves of any [dfrac] make it again *)
Definition dq_half (dq : dfrac) : dfrac :=
  match dq with
  | DfracOwn q => DfracOwn (q / 2)%Qp
  | DfracDiscarded => DfracDiscarded
  | DfracBoth q => DfracBoth (q / 2)%Qp
  end.

Lemma dq_half_op (dq : dfrac) : dq_half dq ⋅ dq_half dq = dq.
Proof.
  destruct dq as [q | | q]; rewrite /dq_half.
  - change (DfracOwn (q / 2)%Qp ⋅ DfracOwn (q / 2)%Qp)
      with (DfracOwn (q / 2 + q / 2)%Qp).
    by rewrite Qp.div_2.
  - exact dfrac_op_discarded.
  - change (DfracBoth (q / 2)%Qp ⋅ DfracBoth (q / 2)%Qp)
      with (DfracBoth (q / 2 + q / 2)%Qp).
    by rewrite Qp.div_2.
Qed.

(* the kernel's count is the caller's request, below the sign boundary
   ([UCatKernel.cat_count_is], generic) *)
Lemma cons_count_is (nb : nat) :
  (Z.of_nat nb < 2 ^ 31)%Z ->
  sys_rw_count (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb.
Proof.
  intros Hlt. change (2 ^ 31)%Z with 2147483648%Z in Hlt.
  assert (Hu : uint (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb)
    by (apply uint_moi; unfold Z64; lia).
  rewrite uint_unsigned in Hu.
  rewrite /sys_rw_count. unfold bv_signed.
  rewrite trunc32_subrange subrange_31_0_unsigned Hu.
  rewrite (Z.mod_small (Z.of_nat nb) 4294967296); [| lia].
  assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
Qed.

(* every alternative a console write can answer the length of *)
Definition cons_short (alts : list (list (bv 8))) : Prop :=
  Forall (fun x => (Z.of_nat (length x) < 2 ^ 31)%Z) alts.

Section cons_pure.
  Context (M : lmodel).

  (* a code the line typed admits, and after which coverage goes on *)
  Definition cons_adm (I : list (bv 8)) (c : nat) : Prop :=
    lm_ok M (lm_line_at M I) (lm_dec M c) /\ lm_term M (lm_dec M c) = false.

  (* THE STREAM BYTE a filed block's later byte is: the continuation at the
     round's state is a prefix of what the round then owes, at ANY
     alternative (at the panic one the next prologue round follows it) *)
  Lemma cons_blk_byte (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (pos c j : nat) (b : bv 8) :
    lm_wr_blk M ps cs s0 I pos ->
    lm_abs M s0 cs I c !! j = Some b ->
    lm_proc_stream M ps (cs ++ [c]) s0 I !! (pos + j)%nat = Some b.
  Proof using.
    intros Hw Hb.
    pose proof (lm_wr_blk_nonnil M ps cs s0 I pos Hw) as Hne.
    pose proof Hw as (_ & Hr & Hn & HP).
    rewrite /lm_proc_stream (lm_wr_blk_low M ps cs s0 I pos c Hw) lookup_app_r; [| lia].
    replace (pos + j - length (lm_proc_before M ps cs s0 I))%nat with j by lia.
    rewrite /lm_pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at (lm_blk_snoc_at M cs I c Hn) (lm_blk_snoc_upto M cs s0 I c Hn).
    rewrite lookup_app_l; [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  Qed.
End cons_pure.

(* ===================================================================== *)
(*  S2  THE SOURCE RUN: its halves, its range, and its leaf               *)
(* ===================================================================== *)
Section cons_src.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* NO [ctokG] AND NO [uexecSG] VARIABLE ([UEchoOut]'s reasons): row 16's
     concrete arm is read here, so the instance is the xv6 one. *)
  Context `{PS : UexecSG.uprogSG Σ}.

  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* one byte at [dq1 ⋅ dq2] is one at each *)
  Lemma ubyteq_op (γ : gname) (dq1 dq2 : dfrac) (a : Z) (b : bv 8) :
    ubyteq γ (dq1 ⋅ dq2) a b ⊣⊢ ubyteq γ dq1 a b ∗ ubyteq γ dq2 a b.
  Proof using .
    rewrite /ubyteq. iSplit.
    - rewrite ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def.
      rewrite -own_op -gmap_view_frag_op agree_idemp. iIntros "$".
    - iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma ubytesq_op (γ : gname) (dq1 dq2 : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    ubytesq γ (dq1 ⋅ dq2) a n f ⊣⊢ ubytesq γ dq1 a n f ∗ ubytesq γ dq2 a n f.
  Proof using .
    rewrite /ubytesq -big_sepL_sep.
    apply big_opL_proper. intros k j _. apply ubyteq_op.
  Qed.

  (* a source run is two runs at half the fraction (the text half is
     persistent and is simply duplicated) *)
  Lemma usrc_at_split (N : uk_names Σ) (tx : bool) (dq : dfrac) (ua : Z)
      (n : nat) (f : nat -> bv 8) :
    usrc_at N tx dq ua n f ⊣⊢
    usrc_at N tx (dq_half dq) ua n f ∗ usrc_at N tx (dq_half dq) ua n f.
  Proof using .
    rewrite /usrc_at. destruct tx.
    - iSplit; [iIntros "#H"; iFrame "H" | iIntros "[$ _]"].
    - rewrite -{1}(dq_half_op dq). apply ubytesq_op.
  Qed.

  (* the empty run is at every address *)
  Lemma usrc_at_rebase (N : uk_names Σ) (tx : bool) (dq : dfrac) (ua ua' : Z)
      (n : nat) (f : nat -> bv 8) :
    (n = 0%nat \/ ua = ua') ->
    usrc_at N tx dq ua n f ⊣⊢ usrc_at N tx dq ua' n f.
  Proof using .
    intros [-> | ->]; [| reflexivity].
    rewrite /usrc_at /ubytesq. destruct tx; cbn [seq]; rewrite !big_sepL_nil; reflexivity.
  Qed.

  (* an owned or fetchable run does not wrap *)
  Lemma urun_usrc_bnd (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (tx : bool) (dq : dfrac) (ua : Z)
      (n : nat) (f : nat -> bv 8) :
    urun N h m pc avail -∗ usrc_at N tx dq ua n f -∗
    ⌜ forall j : nat, (j < n)%nat -> 0 <= ua + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hs".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hheap & _)".
    rewrite /usrc_at. destruct tx.
    - iDestruct (uheap_text_bytes (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ua n f
                   with "Hheap Hs") as %Hb.
      iPureIntro. intros j Hj. destruct (Hb j Hj) as (_ & _ & Hc). exact Hc.
    - iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz dq ua n f
                   with "Hheap Hs") as %Hb.
      iPureIntro. intros j Hj. exact (proj2 (Hb j Hj)).
  Qed.

  (* the chain's per-byte premise, off either half *)
  Lemma usrc_at_wat (N : uk_names Σ) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (tx : bool) (dq : dfrac)
      (ua : mword 64) (n : nat) (f : nat -> bv 8) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    usrc_at N tx dq (uint ua) n f -∗
    ⌜ forall j : nat, (j < n)%nat ->
        M !! uint (add_vec_int ua (Z.of_nat j)) = Some (f j) ⌝.
  Proof using .
    iIntros "Hheap Hs". rewrite /usrc_at. destruct tx.
    - iDestruct (usrc_ok_utext (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ua n f
                   with "Hheap Hs") as %[Hok _].
      by iPureIntro.
    - iApply (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz dq ua n f
                with "Hheap Hs").
  Qed.

  (* THE WRITE LEAF AT A SOURCE: the data half's or the text half's, as the
     program's reading of its run selects *)
  Lemma cons_leaf (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (fdep : sfam) (l : list fdstate) (tx : bool) (dq : dfrac)
      (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    usrc_at N tx dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (∀ (h' : CpuId) (r : mword 64) (Wv : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf Wv) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf Wv) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf Wv) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜take NSTD (uvis_fd Wv) = l⌝ -∗
       ⌜uvis_lazy Wv = false⌝ -∗
       ⌜ forall (Pt : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf Pt ->
           perm_of (ud_um Pt) (uvis_sz Wv) = uvis_perm Wv ->
           lazy_free (ud_um Pt) (uvis_sz Wv) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped Pt
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       usrc_at N tx dq (uint (m !!! Regidx a1_idx)) nb f -∗
       spost_at uslot 16 fdep Wv r (uvis_M Wv) (uvis_fd Wv) cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal. rewrite /usrc_at. destruct tx.
    - iApply (wp_uk_ecall_write_chain_txt N h m pc avail fdep l nb f Hn Hal).
    - iApply (wp_uk_ecall_write_chain_buf N h m pc avail fdep l dq nb f Hn Hal).
  Qed.
End cons_src.

(* ===================================================================== *)
(*  S3  THE DEVICE AND ITS WRITE LAW                                      *)
(* ===================================================================== *)
Section UkConsOut.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  (* [GenLinks]' section context: the model, the claim's parameters, and
     the record equation *)
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = gcl M G sd A).
  (* ...and the program instance, with its write stub's law *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HPc : !Persistent (up_code P)}.
  Context (Hstub : ⊢ stub_law N (up_code P) 16 (up_write P)).

  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation W := (gcW G).
  (* the era the console chain of a write is at *)
  Local Notation ke := (S gen_id).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* the era's cursor at a block of the stage, [i] bytes out, the first of
     which filed [c] ([GenLinksLine.gwc_blk]'s left arm) *)
  Definition cons_cur (v : era_pins) (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (pos c i : nat) : iProp Σ :=
    (turn v (pos + i)%nat ∗ ps_lb v ps ∗ cs_lb v (lm_blkcs cs c i)
     ∗ inp_lb v I ∗ W ke s0)%I.

  (* THE DEVICE, owing one of [alts] (the file header has the encoding) *)
  Definition cons_dev (alts : list (list (bv 8))) : iProp Σ :=
    (⌜cons_short alts⌝
     ∗ ((∃ (v : era_pins) (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
           (pos : nat),
           ⌜lm_wr_blk_t M ps cs s0 I pos⌝ ∗ PIN ke v
           ∗ ((∃ codes : list nat,
                 ⌜alts = lm_abs M s0 cs I <$> codes⌝
                 ∗ ⌜Forall (cons_adm M I) codes⌝
                 ∗ cons_cur v ps cs s0 I pos 0 0)
              ∨ (∃ c i : nat,
                   ⌜(0 < i)%nat⌝ ∗ ⌜alts = [drop i (lm_abs M s0 cs I c)]⌝
                   ∗ cons_cur v ps cs s0 I pos c i)))
        ∨ T))%I.

  Lemma cons_dev_short (alts : list (list (bv 8))) :
    cons_dev alts -∗ ⌜cons_short alts⌝.
  Proof using . iIntros "[$ _]". Qed.

  Lemma cons_dev_taint (alts : list (list (bv 8))) :
    cons_short alts -> T -∗ cons_dev alts.
  Proof using . iIntros (Hs) "HT". iSplit; [done |]. by iRight. Qed.

  (* the device narrows to the alternative the program chose *)
  Lemma cons_dev_sub (alts : list (list (bv 8))) (a : list (bv 8)) :
    a ∈ alts -> cons_dev alts -∗ cons_dev [a].
  Proof using .
    intros Ha. iIntros "[%Hs Hd]". iSplit.
    { iPureIntro. unfold cons_short in *. apply Forall_singleton.
      exact (proj1 (Forall_forall _ _) Hs a (proj1 (elem_of_list_In _ _) Ha)). }
    iDestruct "Hd" as "[Hd | HT]"; [| by iRight]. iLeft.
    iDestruct "Hd" as (v ps cs s0 I pos) "(%Hw & Hpin & Hd)".
    iExists v, ps, cs, s0, I, pos.
    iSplit; [iPureIntro; exact Hw |]. iSplitL "Hpin"; [iExact "Hpin" |].
    iDestruct "Hd" as "[(%codes & %Hal & %Hadm & Hc) | (%c & %i & %Hi & %Hal & Hc)]".
    - iLeft. subst alts. apply elem_of_list_fmap in Ha as (c & -> & Hc).
      iExists [c].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; apply Forall_singleton;
               exact (proj1 (Forall_forall _ _) Hadm c (proj1 (elem_of_list_In _ _) Hc)) |].
      iExact "Hc".
    - iRight. subst alts. apply elem_of_list_singleton in Ha as ->.
      iExists c, i.
      iSplit; [iPureIntro; exact Hi |].
      iSplit; [iPureIntro; reflexivity |].
      iExact "Hc".
  Qed.

  (* ONE BYTE: the head of what the device owes *)
  Lemma cons_dev_step (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    cons_dev [x] -∗ out_link Uart0 ke b (cons_dev [drop 1 x]).
  Proof using B Hcons.
    intros Hb. iIntros "[%Hs Hd]".
    assert (Hs' : cons_short [drop 1 x]).
    { unfold cons_short in *. apply Forall_singleton. rewrite Forall_singleton in Hs.
      eapply Z.le_lt_trans; [| exact Hs].
      apply Nat2Z.inj_le. rewrite length_drop. lia. }
    iDestruct "Hd" as "[Hd | #HT]"; last first.
    { iApply (gwrite_link_taint M G sd A Hcons ke b with "HT").
      iIntros "#HT'". by iApply cons_dev_taint. }
    iDestruct "Hd" as (v ps cs s0 I pos) "(%Hw & #Hpin & Hd)".
    pose proof Hw as [Hwb Htl].
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    iDestruct "Hd" as "[(%codes & %Hal & %Hadm & Hc) | (%c & %i & %Hi & %Hal & Hc)]".
    - (* UNFILED: the block's first byte files the code *)
      destruct codes as [| c [| c' codes]]; cbn [fmap list_fmap] in Hal;
        try discriminate.
      injection Hal as Hx. subst x.
      rewrite Forall_singleton in Hadm. destruct Hadm as [Hok Hterm].
      iDestruct "Hc" as "(Ht & #Hps & #Hcs & #Hin & #HW)".
      cbn [lm_blkcs]. iEval (rewrite Nat.add_0_r) in "Ht".
      iApply (gwrite_link_blk M G B sd A Hcons ke v pos c b ps cs s0 I _
                (lm_wr_blk_nonnil M ps cs s0 I pos Hwb) Hr ltac:(lia) Hpin0 HP
                Hok Hterm Hb
                with "Hpin Ht Hps Hcs Hin HW").
      iIntros "[(Ht & _ & #Hcs' & _ & _) | #HT]"; last by iApply cons_dev_taint.
      iSplit; [iPureIntro; exact Hs' |]. iLeft. iExists v, ps, cs, s0, I, pos.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iExact "Hpin" |].
      iRight. iExists c, 1%nat.
      iSplit; [iPureIntro; lia |]. iSplit; [iPureIntro; reflexivity |].
      rewrite /cons_cur. cbn [lm_blkcs].
      replace (pos + 1)%nat with (S pos) by lia.
      iFrame "Ht Hps Hcs' Hin HW".
    - (* FILED at [c], [i] bytes out: an ordinary byte of the stream *)
      injection Hal as Hx. subst x.
      rewrite lookup_drop Nat.add_0_r in Hb.
      destruct i as [| i']; [lia |].
      iDestruct "Hc" as "(Ht & #Hps & #Hcs & #Hin & #HW)". cbn [lm_blkcs].
      iApply (gwrite_link M G sd A Hcons ke v (pos + S i') b ps (cs ++ [c]) s0 I _
                ltac:(rewrite length_app /=; lia)
                (lm_wr_blk_pin_snoc M ps cs s0 I pos c Hwb)
                (cons_blk_byte M ps cs s0 I pos c (S i') b Hwb Hb)
                with "Hpin Ht Hps Hcs Hin HW").
      iIntros "[(Ht & _ & _ & _ & _) | #HT]"; last by iApply cons_dev_taint.
      iSplit; [iPureIntro; exact Hs' |]. iLeft. iExists v, ps, cs, s0, I, pos.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iExact "Hpin" |].
      iRight. iExists c, (S (S i')).
      iSplit; [iPureIntro; lia |].
      iSplit.
      { iPureIntro. f_equal. rewrite drop_drop. f_equal. lia. }
      rewrite /cons_cur. cbn [lm_blkcs].
      replace (pos + S (S i'))%nat with (S (pos + S i')) by lia.
      iFrame "Ht Hps Hcs Hin HW".
  Qed.

  (* THE CONSOLE CHAIN at the cursor [j ↦ cons_dev [drop j a]] *)
  Lemma cons_chain (a : list (bv 8)) (Mh : gmap Z (bv 8)) (ua : mword 64)
      (fb : nat -> bv 8) :
    forall (cnt j : nat),
    (forall t : nat, (j <= t)%nat -> (t < j + cnt)%nat -> a !! t = Some (fb t)) ->
    (forall t : nat, (j <= t)%nat -> (t < j + cnt)%nat ->
       Mh !! uint (add_vec_int ua (Z.of_nat t)) = Some (fb t)) ->
    cons_dev [drop j a] -∗
    cons_out_chain ke Mh ua (fun t : nat => cons_dev [drop t a]) j cnt.
  Proof using B Hcons.
    intros cnt. induction cnt as [| cnt IH]; intros j Ha HM.
    - iIntros "Hd". cbn [cons_out_chain]. iExact "Hd".
    - iIntros "Hd". cbn [cons_out_chain]. iSplit; [iExact "Hd" |].
      iIntros (b) "%Hbm".
      rewrite (HM j ltac:(lia) ltac:(lia)) in Hbm. injection Hbm as <-.
      iApply (out_link_mono Uart0 ke (fb j) (cons_dev [drop 1 (drop j a)])
                with "[] [Hd]").
      { iIntros "Hd". rewrite drop_drop.
        replace (j + 1)%nat with (S j) by lia.
        iApply (IH (S j) ltac:(intros t H1 H2; apply Ha; lia)
                  ltac:(intros t H1 H2; apply HM; lia) with "Hd"). }
      iApply (cons_dev_step with "Hd").
      rewrite lookup_drop Nat.add_0_r. apply Ha; lia.
  Qed.

  (* the deposit family row 16 is read at ([UEchoOut.kec_fam]'s mould) *)
  Definition cons_fam (Q : nat -> iProp Σ) : sfam := xfam_wr Q (ukn_pay N).

  (* =================================================================== *)
  (*  THE WRITE LAW: [UkHandler.ei_write] at the console                  *)
  (* =================================================================== *)
  Lemma cons_write (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    a ∈ alts -> bs `prefix_of` a ->
    UserFd.ustd (ukn_fd N) l -∗ cons_dev alts -∗
    (UserFd.ustd (ukn_fd N) l -∗ cons_dev [drop (length bs) a]
     -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using B HPc Hcons Hstub.
    intros Hfd Hl Ha Hpre. iIntros "Hstd Hd HK".
    iDestruct (cons_dev_sub alts a Ha with "Hd") as "Hd".
    iDestruct (cons_dev_short with "Hd") as %Hs.
    assert (Hn31 : (Z.of_nat (length bs) < 2 ^ 31)%Z).
    { unfold cons_short in Hs. rewrite Forall_singleton in Hs.
      eapply Z.le_lt_trans; [| exact Hs].
      apply Nat2Z.inj_le. exact (prefix_length _ _ Hpre). }
    rewrite /wr_obl.
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 #Hcode Hsrc Hrun Hcont".
    (* the run's address, as the leaf spells it: the register's own word,
       which is [ua] wherever a byte is held *)
    iDestruct (urun_usrc_bnd N h m _ avail tx dq ua (length bs) f
                 with "Hrun Hsrc") as %Hbnd.
    assert (Hua : length bs = 0%nat \/ ua = uint (m !!! Regidx a1_idx)).
    { destruct (decide (length bs = 0%nat)) as [Hz | Hnz]; [by left | right].
      destruct (Hbnd 0%nat ltac:(lia)) as [Hlo Hhi].
      change (2 ^ 38) with 274877906944 in Hhi.
      rewrite Ha1. symmetry. apply uint_moi. unfold Z64. lia. }
    iEval (rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx))
                      (length bs) f Hua)) in "Hsrc".
    iDestruct (usrc_at_split with "Hsrc") as "[Hs1 Hs2]".
    (* the three argument rows, at the register file the leaf runs on *)
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat fd)
      by (rewrite Ham0; exact Ha0).
    pose proof (cons_count_is (length bs) Hn31) as Hcz.
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = length bs)
      by (rewrite Ham2 Ha2 Hcz; lia).
    assert (Hsys : usysno (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m) = 16).
    { unfold usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    (* the bytes the program hands over ARE the chosen alternative's *)
    assert (Hab : forall t : nat, (t < length bs)%nat -> a !! t = Some (f t)).
    { intros t Ht. exact (prefix_lookup_Some _ _ _ _ (Hf t Ht) Hpre). }
    (* ---- THE STUB, to the ecall ---- *)
    iPoseProof Hstub as "Hst". rewrite /stub_law.
    iDestruct "Hst" as "#Hst".
    iApply ("Hst" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%Hal Hec Hrun Hret".
    unfold stub_ret.
    iApply (cons_leaf N h1 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
              _ avail
              (cons_fam (fun t : nat =>
                 (cons_dev [drop t a]
                  ∗ usrc_at N tx (dq_half dq) (uint (m !!! Regidx a1_idx))
                      (length bs) f)%I))
              l tx (dq_half dq) (length bs) f Hsys Hal
              with "Hec Hrun [Hd Hs2] Hstd [Hs1]").
    { (* THE DEPOSIT: the console chain at the device, and the half of the
         run the chain's premise is read off, handed back beside it *)
      iApply (uwrite_chain_sup_ret N (fun t : nat => cons_dev [drop t a])
                (usrc_at N tx (dq_half dq) (uint (m !!! Regidx a1_idx))
                   (length bs) f)
                _ _ l fd rb CONSOLE Hi0 Hfd Hl).
      iIntros (Mh pm sz) "Hheap".
      iDestruct (usrc_at_wat N Mh pm sz tx (dq_half dq) (m !!! Regidx a1_idx)
                   (length bs) f with "Hheap Hs2") as %HM.
      iFrame "Hheap Hs2".
      rewrite Ham1 Hcnt.
      iApply (cons_chain a Mh (m !!! Regidx a1_idx) f (length bs) 0%nat
                ltac:(intros t _ Ht; apply Hab; lia)
                ltac:(intros t _ Ht; apply HM; lia)
                with "[Hd]").
      rewrite drop_0. iExact "Hd". }
    { rewrite Ham1. iExact "Hs1". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun t : nat =>
                    (cons_dev [drop t a]
                     ∗ usrc_at N tx (dq_half dq) (uint (m !!! Regidx a1_idx))
                         (length bs) f)%I)
                 (ukn_pay N) Wv ret (uvis_M Wv) (uvis_fd Wv) cw' cs'
                 l fd rb (length bs)
                 ltac:(rewrite Hka0; exact Hi0)
                 Hfd Htk Hl
                 ltac:(rewrite Hka2 Ham2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hret HQ]".
    iDestruct "HQ" as "[Hd Hs2]".
    rewrite Ham1.
    (* ---- THE STUB, back to the caller ---- *)
    iApply ("Hret" $! h' ret with "Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Hstd Hd] [Hs1 Hs2] Hrun").
    - rewrite Hret bvsigned_moi_small;
        [| change (2 ^ 63) with 9223372036854775808; lia].
      iApply ("HK" with "Hstd Hd").
    - rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx))
                 (length bs) f Hua).
      rewrite (usrc_at_split N tx dq). iFrame "Hs1 Hs2".
  Qed.
End UkConsOut.

(* ===================================================================== *)
(*  S4  THE WITNESSES: the law at echo and at cat                         *)
(* ===================================================================== *)
Section UkConsOutInst.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = gcl M G sd A).
  Context (N : uk_names Σ).

  Local Instance cat_prog_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  Lemma cons_write_echo (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    a ∈ alts -> bs `prefix_of` a ->
    UserFd.ustd (ukn_fd N) l -∗ cons_dev M G alts -∗
    (UserFd.ustd (ukn_fd N) l -∗ cons_dev M G [drop (length bs) a]
     -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N (echo_prog N) (Z.of_nat fd) bs K.
  Proof using B Hcons.
    exact (cons_write M G B sd A Hcons N (echo_prog N) (echo_stub_write N)
             l fd rb alts a bs K).
  Qed.

  Lemma cons_write_cat (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    a ∈ alts -> bs `prefix_of` a ->
    UserFd.ustd (ukn_fd N) l -∗ cons_dev M G alts -∗
    (UserFd.ustd (ukn_fd N) l -∗ cons_dev M G [drop (length bs) a]
     -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N (cat_prog N) (Z.of_nat fd) bs K.
  Proof using B Hcons.
    exact (cons_write M G B sd A Hcons N (cat_prog N) (cat_stub_write N)
             l fd rb alts a bs K).
  Qed.
End UkConsOutInst.
