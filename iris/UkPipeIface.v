(* ===================================================================== *)
(* UkPipeIface.v -- THE PIPELINE APPLICATION'S ENDPOINT INTERFACE: one     *)
(* [UkHandler.ep_iface] from the pipeline's console ([UkPipeConsOut]: the *)
(* popen device of the two-writer round, and the generic device at the   *)
(* single-writer rounds), a pipe's two ends ([UkPipeDev]) and THE COPY    *)
(* DEVICE (design SS3.4f: cat at a pipe's end, the read end and the       *)
(* console under ONE number), for the two processes of `echo ... | cat`, *)
(* paid end to end through the once-glue [UkHandler.tree_pay_of_conforms] *)
(* (program-specs SS3.4b-SS3.4f).                                          *)
(*                                                                        *)
(* THE REGISTRY IS GHOST STATE, as [UkFileIface]'s: a device number's     *)
(* kind is a token [pif_tok d q v] in one camera; [ei_fds] holds the POOL *)
(* (every unnamed number's whole token) and HALF of each named one, the  *)
(* device resource the other half.  The kinds ([pdev]):                  *)
(*                                                                        *)
(*   [PDPCons]  the console at an OPEN two-writer round, the right       *)
(*              writer's device [UkPipeConsOut.pcons_dev] (cat's cursor  *)
(*              half of the family beside the round's context and [YR]); *)
(*   [PDCons]   the console at a single-writer round,                    *)
(*              [UkConsOut.cons_dev_at v I] at the pipeline's link        *)
(*              parameters, indexed by the section's round;               *)
(*   [PDMute]   a console slot the process writes NOTHING on ([DOut       *)
(*              [[]]]: cat's descriptor 2 at the pipeline, whose          *)
(*              diagnostics the round pays under the taint);             *)
(*   [PDWr]     the pipe's WRITE end at a standard slot ([FdPipe gp]),    *)
(*              [UkPipeDev.pipe_out] / [pipe_halt] (DOutH / DHalt);        *)
(*   [PDRd]     the pipe's READ end at a standard slot,                   *)
(*              [UkPipeDev.pipe_in] (DInE) and the end of file at ANY     *)
(*              point of the line (DInEnd);                              *)
(*   [PDCopy]   THE COPY DEVICE: the pipe's read end on descriptor        *)
(*              [copy_in] (0) and the popen console on [copy_out] (1),   *)
(*              [pif_copy]: the read cursor [c] and the console's cursor  *)
(*              [w] of the two-writer family, tied by the pure facts      *)
(*              [S = drop c L], [pending = drop w (take c L)], [w <= c],  *)
(*              [c <= length L]; [pif_copy_end] adds the EOF shot at      *)
(*              [take c L].  The console's first-byte fact [YR] (a byte   *)
(*              reached the reader) is DERIVED inside the write law from  *)
(*              the read cursor the same resource holds                   *)
(*              ([PipeProto.pws_lb_of_rcur] under the byte link's fancy   *)
(*              update, [pif_wD_step]) -- design SS3.4d's section          *)
(*              variable is gone as an INPUT; [YR] stays a section        *)
(*              variable of the family with [Hyr : pws_lb (take 1 L) ⊢    *)
(*              YR] saying what it is.  [h = true] (the sink a pipe's     *)
(*              write end, the middle cat of `echo | cat | cat`) is        *)
(*              [False] with vacuous laws: a later lane, once a           *)
(*              three-process line exists.                                *)
(*                                                                        *)
(* The section is at ONE round of ONE pipe: the two-writer round's        *)
(* context (v, I, L, the family's three ghosts, the two sides' facts, the *)
(* three pure witnesses [UShPipeLaw.pl_cat_kround] discharges) and the   *)
(* protocol's names (pn, gp, L) are section variables, since echo and     *)
(* cat run in the same round on the same pipe.  The scope of paths is    *)
(* EMPTY ([pif_filesr] is [paths = []]): the pipeline line provisions no  *)
(* file, so [ei_open] / [ei_open_absent] are vacuous, and no tail         *)
(* descriptor is ever bound (every row is a standard slot).             *)
(*                                                                        *)
(* THE EXIT WANDS (design SS3.4e).  [ei_fds] carries [pif_kpay vs]: the   *)
(* payload [pif_pay = ukn_pay N (-1)] up front ([echo_pipe_paid_of_round] *)
(* keeps that reading), or -- while a copy device is registered -- the    *)
(* WAND [pif_exit_k : (T ∨ pif_cend) -∗ ukn_pay N (-1)] from the copy     *)
(* device's END ([pif_cend]: the EOF shot, the read cursor and the        *)
(* console cursor at ONE index, textually [UShPipeLaw.pl_Cend]) or the    *)
(* taint, or -- while a WRITE END is registered (lane F) -- the LEFT      *)
(* WAND [pif_exit_k_left : (T ∨ pif_lexit) -∗ ukn_pay N (-1)] from the    *)
(* write end's end ([pif_lexit]: the cursor at the line's end, or stuck   *)
(* under the reader's shot, or the taint -- textually [UEchoPipe.ep_ok pn *)
(* L (length L)], [ep_exit]'s second conjunct).  Every law frames them;   *)
(* [ei_exit] applies the copy wand to the drained copy device             *)
(* ([pif_copy_end d false []]: [pending = []] makes the two cursors       *)
(* equal) and the left wand to the drained or halted write end -- whose   *)
(* resource ([pipe_out pn L []] / [pipe_halt pn]) lacks the cursor's      *)
(* bound and, halted, the lower bound, both ONE access to the protocol's  *)
(* invariant under the hole's WP ([pif_lexit_of_lend]); the last close of *)
(* an ENDED copy device, or of a drained or halted write end, applies the *)
(* wand at the close.  [pif_exit_k_cat] / [pif_exit_k_left_of] are the   *)
(* glue from the round's continuations, so [cat_copy_paid_of_round] takes *)
(* what [UShPipeLaw.pl_RcR] holds at the entry (no [YR], no payload) and  *)
(* [echo_pipe_paid_of_round'] takes [UEchoPipe.ep_exit -∗ Q (-1)]'s box   *)
(* with the frame [side_L ∗ Wq] lent, no payload before the child runs.   *)
(* [pif_refused] packages the refused fields below so that a file above   *)
(* can assume them at every minted record ([UkPipeEntries]).             *)
(*                                                                        *)
(* WHAT IS PROVED: the console write at all three console kinds, the     *)
(* pipe write (count, halt, taint), the halted write, every zero-length  *)
(* write but one, the pipe read at DInE / DInEnd INCLUDING the early end  *)
(* of file (the end at any point of the line, and the read after the     *)
(* end: [UkPipeDev.pipe_read_eof]), the copy device's read (chunk, end),  *)
(* the read after its end, its write (per byte through the console core  *)
(* [UkConsOut.cons_write] at [pif_wD], the family's step                  *)
(* [UShPipeCatRound.pcat_step_at]), the close of any descriptor (last or *)
(* shared; a copy device's last close at its end pays the exit), the     *)
(* exit, the open laws (vacuous), and [ei_taint_pays] from the generic    *)
(* free handler [UkFreeHandler] at [echo_taint].                          *)
(*                                                                        *)
(* WHAT IS NOT, as section hypotheses at the narrowest refused case:      *)
(*                                                                        *)
(*   [Hhalt_long]   a write of 2^31 bytes or more at a halted write end:  *)
(*             [UkPipeDev.pipe_write_halt] takes the count as a C int.    *)
(*   [Hnil_ro]  a zero-length write at a pipe's read end open read-only  *)
(*             (a PDRd row, or the copy device on [copy_in]):             *)
(*             [UkPipeDev.pipe_write_nil] needs a writable row; the      *)
(*             kernel answers -1 there and no leaf says so.              *)
(*                                                                        *)
(* CLOSED (lane closegap): the LAST close of a copy device before its end *)
(* ([pif_close_open]) or of the write end before it is drained            *)
(* ([pif_close_open_w]) while an exit wand is held -- the wand wants the  *)
(* EOF shot and equal cursors, or the line's end or the reader's shot.    *)
(* [ProgTree.cf_close] asks such a device [drained_at_close] and          *)
(* [ei_close] receives the fact, so both cases are refuted.               *)
(*                                                                        *)
(* WHAT THE INSTANCE FORCED ON THE PURE LAYER (ProgTree, UkHandler; the   *)
(* file application fills the copy laws with [_]):                        *)
(*   - [drained (DCopy _ _ _) = False]: the reader's exit payoff is the   *)
(*     EOF shot, which an open device does not hold; cat exits only at   *)
(*     0, and a pipe answers 0 only at its end, so [cf_read_copy]'s chunk *)
(*     is NONEMPTY (the tree at [DCopy h [] []] no longer needs to exit); *)
(*   - the copy device is a FILTER's: reads at [copy_in], writes at       *)
(*     [copy_out] ([ProgTree]); the two descriptors are two kernel        *)
(*     objects, and a read at the sink is not a pipe read.               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From Stdlib Require Import FunctionalExtensionality.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys.
Require Import VcGen.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
Require Import FdSlots ProcGeom UserFd.
Require Import UexecSG UexecSlot UexecRet.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import ObsTrace ConsLog.
Require Import LineWords LineBytes EchoDisc.
Require Import EchoOut AppEcho.
Require Import EchoOutPure.
Require Import LineModel LineModelLinks.
Require Import GenOutPure GenOut GenLinksLine.
Require Import PipeDisc.
Require Import PipeOutPure PipeOut.
Require Import PipeBothPure PipeBoth.
Require Import PipeNames PipeQueue PipeReg PipeProto.
Require Import PipeLinks PipeLinksLine PipeLinkInst.
Require Import UShPipeRound2.      (* [blk2N] *)
Require Import UShPipeCatRound.    (* [pcat_ch] *)
Require Import AppCfg AppInv AppPipeClaim AppPipeCons.   (* [pipe_pred], [pipe_sup_of_taint] *)
Require Import CtxIdDefs.
(* [UserHeap] LAST among the U-tier libraries, as [UkConsOut] has it *)
Require Import UserHeap.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Require Import UkConsOut UkPipeConsOut UkPipeDev.
Require Import UkFileDev.            (* [file_close_std], the standard-slot close leaf *)
Require Import UkHandler UkFreeHandler.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE REGISTRY                                                      *)
(* ===================================================================== *)

(* what a device is (the file header) *)
Inductive pdev := PDPCons | PDCons | PDMute | PDWr | PDRd | PDCopy.

Definition pifRegR := discrete_funUR (fun _ : nat => optionUR (dfrac_agreeR (leibnizO pdev))).
Class pifRegG (Σ : gFunctors) := PifRegG { pif_reg_inG :: inG Σ pifRegR }.
Definition pifRegΣ : gFunctors := #[GFunctor pifRegR].
Global Instance subG_pifRegΣ {Σ} : subG pifRegΣ Σ -> pifRegG Σ.
Proof. solve_inG. Qed.

(* the pool: the whole token of every number outside [B], at [w] *)
Definition pif_pool (B : gset nat) (w : nat -> pdev) : pifRegR :=
  fun d => if decide (d ∈ B) then None
           else Some (to_dfrac_agree (DfracOwn 1) (w d : leibnizO pdev)).

Definition pif_single (d : nat) (q : Qp) (v : pdev) : pifRegR :=
  discrete_fun_singleton d (Some (to_dfrac_agree (DfracOwn q) (v : leibnizO pdev))).

Lemma pif_dfa_valid (v : pdev) : ✓ (to_dfrac_agree (DfracOwn 1) (v : leibnizO pdev)).
Proof. split; [apply dfrac_valid_own; reflexivity | done]. Qed.

Lemma pif_pool_valid (B : gset nat) (w : nat -> pdev) : ✓ pif_pool B w.
Proof.
  intros d. rewrite /pif_pool. case_decide; [done |].
  apply Some_valid, pif_dfa_valid.
Qed.

Lemma pif_pool_take (B : gset nat) (w : nat -> pdev) (d : nat) :
  d ∉ B -> pif_pool B w ≡ pif_pool ({[d]} ∪ B) w ⋅ pif_single d 1 (w d).
Proof.
  intros Hd x. rewrite discrete_fun_lookup_op /pif_pool /pif_single.
  destruct (decide (x = d)) as [-> | Hne].
  - rewrite discrete_fun_lookup_singleton.
    rewrite decide_False; [| exact Hd]. rewrite decide_True; [| set_solver].
    by rewrite left_id.
  - rewrite discrete_fun_lookup_singleton_ne; [| congruence]. rewrite right_id.
    destruct (decide (x ∈ B)) as [Hx | Hx];
      [rewrite decide_True; [done | set_solver] | rewrite decide_False; [done | set_solver]].
Qed.

Lemma pif_pool_ext (B B' : gset nat) (w w' : nat -> pdev) :
  B = B' -> (forall x, x ∉ B -> w x = w' x) -> pif_pool B w = pif_pool B' w'.
Proof.
  intros <- Hw.
  assert (H : forall x, pif_pool B w x = pif_pool B w' x).
  { intros x. rewrite /pif_pool. case_decide as Hx; [reflexivity |]. by rewrite (Hw x Hx). }
  exact (functional_extensionality _ _ H).
Qed.

(* the birth: the whole pool, at any values *)
Lemma pif_reg_alloc `{!pifRegG Σ} (w : nat -> pdev) : ⊢ |==> ∃ γ, own γ (pif_pool ∅ w).
Proof. iApply own_alloc. apply pif_pool_valid. Qed.

(* another descriptor of [fdm] names [d]: what it says of the rest *)
Lemma pif_not_shared (fdm : fdmap) (fd : Z) (d : nat) :
  ~ fd_shared fdm fd d -> forall fd', fd' <> fd -> fdm !! fd' <> Some d.
Proof.
  intros Hns fd' Hne Hfd'. apply Hns. exists fd'. split; [| exact Hfd'].
  apply elem_of_dom. rewrite lookup_delete_ne; [| congruence]. by eexists.
Qed.

(* a device the line reads to its end *)
Lemma pif_drop_nil_le (L : list (bv 8)) (c : nat) :
  drop c L = [] -> (length L <= c)%nat.
Proof.
  intros Hd. apply (f_equal length) in Hd. rewrite length_drop in Hd. simpl in Hd. lia.
Qed.

(* the protocol's namespace misses the console port's: where a byte link's
   fancy update runs, the protocol's invariant can be opened *)
Lemma pif_pipeN_uart : (↑pipeN : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset).
Proof.
  intros x Hx. pose proof (blk2N_pipeN x Hx) as Hy. set_solver.
Qed.

(* the pending bytes after a chunk joined them: the read-but-unwritten
   segment of the line grows by the chunk *)
Lemma pif_pending_grow (L : list (bv 8)) (c w : nat) (cb S' : list (bv 8)) :
  (w <= c)%nat -> (c <= length L)%nat -> drop c L = cb ++ S' ->
  drop w (take c L) ++ cb = drop w (take (c + length cb) L).
Proof.
  intros Hwc HcL Heq.
  rewrite -take_take_drop Heq take_app_length.
  rewrite drop_app_le; [reflexivity |]. rewrite length_take Nat.min_l; [lia | exact HcL].
Qed.

(* a drained copy device has its two cursors equal *)
Lemma pif_drained_eq (L : list (bv 8)) (c w : nat) :
  (w <= c)%nat -> (c <= length L)%nat -> [] = drop w (take c L) -> w = c.
Proof.
  intros Hwc HcL Hp. apply (f_equal length) in Hp.
  rewrite length_drop length_take Nat.min_l in Hp; [| exact HcL]. cbn [length] in Hp. lia.
Qed.

(* ===================================================================== *)
(*  1.  THE INSTANCE                                                      *)
(* ===================================================================== *)

Section UkPipeIface.
  (* [UkPipeConsOut]'s binder list, plus the protocol's and the registry's *)
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG] SECTION VARIABLES: the holes' two ghost-variable
     classes are taken off the [xv6G] bundle, as [UkFileIface] and
     [UkFileDev] take them, so [UkFileDev.file_close_std]'s [cl_obl] is
     this section's [cl_obl] (UCatPipe's finding: a bound instance is a
     second term that prints the same and does not unify) *)
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pifRegG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* the pipeline application: its claim, its kill credential, its supply *)
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Local Notation T := (echo_taint γ).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Context (r : echo_names).
  Context (Heq : file_app = MkAppcfg echo_names (pipe_pred γ) r).

  (* THE ROUND: its pins, its line, the family's three ghosts, the two
     sides' facts, and the pure facts [UShPipeLaw.pl_cat_kround] discharges *)
  Context (v : era_pins) (I L : list (bv 8)).
  Context (gL gR gM : gname) (XL YR : iProp Σ).
  Context {XL_tl : Timeless XL} {YR_tl : Timeless YR} {YR_pers : Persistent YR}.
  #[local] Existing Instance XL_tl.
  #[local] Existing Instance YR_tl.
  #[local] Existing Instance YR_pers.
  Context (Hnd : Forall nodollar L).
  Context (Hwit2 : forall sel : list bool,
             sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel).
  Context (Hwit1 : forall sel : list bool,
             count_true sel = 0%nat -> (length sel <= length L)%nat ->
             pblk2_wit I L sel).
  (* THE PIPE: the protocol's names and the queue's *)
  Context (pn : pnames) (γp : pipe_names).
  (* the reader's fact of the family IS the protocol's lower bound at the
     line's first byte ([UShPipeLaw.pl_YR]): what the copy device's write
     derives from its read cursor *)
  Context (Hyr : pws_lb pn (take 1%nat L) ⊢ YR).

  (* the process, and ANY program instance with its five stubs *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HPc : !Persistent (up_code P)}.
  Context `{HNc : !ukn_const N}.
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hso : ⊢ stub_law N (up_code P) 15 (up_open P).
  Hypothesis Hsc : ⊢ stub_law N (up_code P) 21 (up_close P).
  Hypothesis Hse : ⊢ exit_stub_law N (up_code P) (up_exit P).

  (* the registry's name *)
  Context (γreg : gname).

  Local Notation γfd := (ukn_fd N).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* the two console devices *)
  Local Notation pcons1 := (cons_dev_at pipe_lm (pipe_params g) (pipe_links g) v I).
  Local Notation pcons2 := (pcons_dev g v I L gL gR gM XL YR).

  (* ------------------------------------------------------------------- *)
  (*  the registry's tokens                                               *)
  (* ------------------------------------------------------------------- *)

  Definition pif_tok (d : nat) (q : Qp) (x : pdev) : iProp Σ := own γreg (pif_single d q x).

  Lemma pif_tok_agree (d : nat) (q1 q2 : Qp) (x1 x2 : pdev) :
    pif_tok d q1 x1 -∗ pif_tok d q2 x2 -∗ ⌜x1 = x2⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite /pif_single discrete_fun_singleton_op discrete_fun_singleton_valid
      -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    by destruct Hv as [_ ?].
  Qed.

  Lemma pif_tok_halves (d : nat) (x : pdev) :
    pif_tok d 1 x ⊣⊢ pif_tok d (1/2) x ∗ pif_tok d (1/2) x.
  Proof using .
    rewrite /pif_tok -own_op /pif_single. f_equiv.
    rewrite (discrete_fun_singleton_op d). f_equiv.
    rewrite -Some_op /to_dfrac_agree -pair_op agree_idemp dfrac_op_own Qp.half_half //.
  Qed.

  Lemma pif_pool_own_take (B : gset nat) (w : nat -> pdev) (d : nat) :
    d ∉ B -> own γreg (pif_pool B w) ⊣⊢ own γreg (pif_pool ({[d]} ∪ B) w) ∗ pif_tok d 1 (w d).
  Proof using . intros Hd. rewrite /pif_tok -own_op -pif_pool_take //. Qed.

  (* a token of a device a descriptor names comes home to the pool *)
  Lemma pif_pool_give (vs : gmap nat pdev) (w : nat -> pdev) (d : nat) (x : pdev) :
    d ∈ dom vs ->
    own γreg (pif_pool (dom vs) w) -∗ pif_tok d 1 x -∗
    own γreg (pif_pool (dom (delete d vs)) (fun y => if decide (y = d) then x else w y)).
  Proof using .
    iIntros (Hd) "Hp Ht".
    set (w' := fun y => if decide (y = d) then x else w y).
    assert (Hw' : w' d = x) by (rewrite /w'; by case_decide).
    rewrite (pif_pool_own_take (dom (delete d vs)) w' d); [| rewrite dom_delete_L; set_solver].
    rewrite Hw'. iFrame "Ht".
    assert (HB : dom vs = {[d]} ∪ dom (delete d vs)).
    { rewrite dom_delete_L. apply set_eq. intros y. rewrite elem_of_union elem_of_singleton
        elem_of_difference elem_of_singleton. split; [| intros [-> | []]; done].
      intros Hy. destruct (decide (y = d)); [by left | by right]. }
    assert (Hww : forall y, y ∉ dom vs -> w y = w' y).
    { intros y Hy. unfold w'. case_decide as Hyd; [| done]. subst y. done. }
    rewrite (pif_pool_ext (dom vs) ({[d]} ∪ dom (delete d vs)) w w' HB Hww). done.
  Qed.

  (* the value the registry holds for a named device, read off its token *)
  Lemma pif_toks_agree (vs : gmap nat pdev) (d : nat) (x x' : pdev) (q : Qp) :
    vs !! d = Some x ->
    ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) -∗ pif_tok d q x' -∗
    ⌜x = x'⌝ ∗ ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) ∗ pif_tok d q x'.
  Proof using .
    iIntros (Hv) "Hm Ht".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hv with "Hm") as "[Hx Hcl]".
    iDestruct (pif_tok_agree with "Hx Ht") as %->.
    iFrame "Ht". iSplit; [done |]. iApply ("Hcl" with "Hx").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  the pure half of [ei_fds]                                           *)
  (* ------------------------------------------------------------------- *)

  (* the row a descriptor's device demands of it: every kind at a standard
     slot; the copy device's two descriptors are the filter's *)
  Definition pif_row (ov : option pdev) (fd : Z) (l : list fdstate) : Prop :=
    match ov with
    | Some PDPCons | Some PDCons | Some PDMute =>
        fd < Z.of_nat NSTD
        /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdDevice CONSOLE))
    | Some PDWr =>
        fd < Z.of_nat NSTD
        /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdPipe γp))
    | Some PDRd =>
        fd < Z.of_nat NSTD
        /\ exists wb, l !! Z.to_nat fd = Some (FdOpen true wb (FdPipe γp))
    | Some PDCopy =>
        (fd = copy_in /\ exists wb, l !! 0%nat = Some (FdOpen true wb (FdPipe γp)))
        \/ (fd = copy_out /\ exists rb, l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)))
    | None => False
    end.

  Definition pif_ok (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) : Prop :=
    (forall fd d, fdm !! fd = Some d -> 0 <= fd)
    /\ (forall fd d, fdm !! fd = Some d -> pif_row (vs !! d) fd l)
    /\ (forall d, d ∈ dom vs <-> exists fd, fdm !! fd = Some d).

  Lemma pif_ok_lookup fdm l vs fd d :
    pif_ok fdm l vs -> fdm !! fd = Some d -> exists x, vs !! d = Some x.
  Proof.
    intros (_ & _ & H3) Hfd. apply elem_of_dom. apply H3. by exists fd.
  Qed.

  (* a row is an open slot below the standard bound *)
  Lemma pif_row_open (ov : option pdev) (fd : Z) (l : list fdstate) :
    pif_row ov fd l ->
    fd < Z.of_nat NSTD /\ exists st, l !! Z.to_nat fd = Some st /\ st <> FdClosed.
  Proof.
    destruct ov as [[| | | | |] |]; simpl; intros H; [| | | | | | destruct H].
    1-5: destruct H as (Hlt & b & Hl); (split; [exact Hlt |]);
         eexists; (split; [exact Hl | discriminate]).
    destruct H as [[-> (wb & Hl)] | [-> (rb & Hl)]].
    - split; [unfold copy_in, NSTD; lia |]. eexists. split; [exact Hl | discriminate].
    - split; [unfold copy_out, NSTD; lia |]. eexists. split; [exact Hl | discriminate].
  Qed.

  (* a row survives a change of another slot *)
  Lemma pif_row_ne (ov : option pdev) (fd : Z) (l : list fdstate) (k : nat) (st : fdstate) :
    Z.to_nat fd <> k -> pif_row ov fd l -> pif_row ov fd (<[k := st]> l).
  Proof.
    intros Hne. destruct ov as [[| | | | |] |]; simpl; intros H; [| | | | | | destruct H].
    1-5: destruct H as (Hlt & b & Hl); (split; [exact Hlt |]); exists b;
         (rewrite list_lookup_insert_ne; [exact Hl | exact (not_eq_sym Hne)]).
    destruct H as [[Hfd (wb & Hl)] | [Hfd (rb & Hl)]]; subst fd.
    - left. split; [reflexivity |]. exists wb.
      rewrite list_lookup_insert_ne; [exact Hl | exact (not_eq_sym Hne)].
    - right. split; [reflexivity |]. exists rb.
      rewrite list_lookup_insert_ne; [exact Hl | exact (not_eq_sym Hne)].
  Qed.

  Lemma pif_ok_close fdm l vs (k : nat) d :
    pif_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> ~ fd_shared fdm (Z.of_nat k) d ->
    pif_ok (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) (delete d vs).
  Proof.
    intros (H1 & H2 & H3) Hfd Hns.
    pose proof (pif_not_shared fdm (Z.of_nat k) d Hns) as Hn.
    split; [| split].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      rewrite (lookup_delete_ne vs); [| intros Hqq; subst d'; exact (Hn fd' (not_eq_sym Hne) Hf)].
      apply pif_row_ne; [| exact (H2 fd' d' Hf)].
      pose proof (H1 fd' d' Hf). lia.
    - intros d'. rewrite dom_delete_L elem_of_difference elem_of_singleton H3. split.
      + intros ((fd' & Hfd') & Hne). exists fd'. apply lookup_delete_Some. split; [| exact Hfd'].
        intros Hqq. subst fd'. rewrite Hfd in Hfd'. injection Hfd' as Hdd. exact (Hne (eq_sym Hdd)).
      + intros (fd' & Hfd'). apply lookup_delete_Some in Hfd' as [Hne Hf].
        split; [by exists fd' |]. intros Hqq. subst d'. exact (Hn fd' (not_eq_sym Hne) Hf).
  Qed.

  Lemma pif_ok_close_shared fdm l vs (k : nat) d :
    pif_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> fd_shared fdm (Z.of_nat k) d ->
    pif_ok (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) vs.
  Proof.
    intros (H1 & H2 & H3) Hfd Hsh.
    split; [| split].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      apply pif_row_ne; [| exact (H2 fd' d' Hf)].
      pose proof (H1 fd' d' Hf). lia.
    - intros d'. rewrite H3. split.
      + intros (fd' & Hfd'). destruct (decide (fd' = Z.of_nat k)) as [-> | Hne].
        * rewrite Hfd in Hfd'. injection Hfd' as <-.
          destruct Hsh as (fd'' & Hin & Hfd''). exists fd''. apply lookup_delete_Some.
          apply elem_of_dom in Hin as [d'' Hd'']. apply lookup_delete_Some in Hd'' as [Hne _].
          split; [exact Hne | exact Hfd''].
        * exists fd'. apply lookup_delete_Some. split; [exact (not_eq_sym Hne) | exact Hfd'].
      + intros (fd' & Hfd'). apply lookup_delete_Some in Hfd' as [_ Hf]. by exists fd'.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  the resources                                                       *)
  (* ------------------------------------------------------------------- *)

  (* THE EXIT PAYLOAD, in one place (the file header) *)
  Definition pif_pay : iProp Σ := ukn_pay N (-1).

  (* THE COPY DEVICE'S END, as the round reads it ([UShPipeLaw.pl_Cend],
     textually): the EOF shot, the read cursor and the console cursor at
     ONE index, each under the taint *)
  Definition pif_cend : iProp Σ :=
    (∃ c : nat, (eof_shot pn (take c L) ∨ T) ∗ (rcur pn c ∨ T) ∗ pcat_ch g gR gM c)%I.

  Lemma pif_cend_of_taint : T -∗ pif_cend.
  Proof using .
    iIntros "#HT". iExists 0%nat. iSplitR; [by iRight |]. iSplitR; [by iRight |].
    iApply (pcat_ch_taint g gR gM with "HT").
  Qed.

  (* THE EXIT WAND (design SS3.4e): the payload from the copy device's end,
     or from the taint *)
  Definition pif_exit_k : iProp Σ := ((T ∨ pif_cend) -∗ ukn_pay N (-1))%I.

  (* the glue from the round's continuation *)
  Lemma pif_exit_k_cat : (pif_cend -∗ ukn_pay N (-1)) -∗ pif_exit_k.
  Proof using .
    iIntros "Hk [#HT | Hce]".
    - iApply "Hk". iApply (pif_cend_of_taint with "HT").
    - iApply ("Hk" with "Hce").
  Qed.

  (* THE LEFT PROCESS'S END (lane F): the write end at the line's end, or
     stuck at a cursor under the reader's shot, or the taint -- textually
     [UEchoPipe.ep_ok pn L (length L)], the second conjunct of [ep_exit],
     so that the round's continuation [ep_exit -∗ Q (-1)] plugs in with the
     frame [side_L ∗ Wq] captured ([echo_pipe_paid_of_round']).  What the
     drained write end holds ([pipe_out pn L []] / [pipe_halt pn]) lacks
     the cursor's BOUND and, halted, the history's lower bound; both are
     one access to the protocol's invariant ([pif_lexit_of_lend]), taken
     under the exit hole's WP. *)
  Definition pif_lexit : iProp Σ :=
    ((wcur pn (length L) ∗ pws_lb pn (take (length L) L))
     ∨ ((∃ c : nat, ⌜(c <= length L)%nat⌝ ∗ (wcur pn c ∗ pws_lb pn (take c L)) ∗ ro_shot pn)
        ∨ app_taint))%I.

  Lemma pif_lexit_of_taint : T -∗ pif_lexit.
  Proof using Hkill. iIntros "#HT". iRight. iRight. rewrite Hkill. iExact "HT". Qed.

  (* THE LEFT EXIT WAND: the payload from the write end's end, or the taint *)
  Definition pif_exit_k_left : iProp Σ := ((T ∨ pif_lexit) -∗ ukn_pay N (-1))%I.

  Lemma pif_exit_k_left_of : (pif_lexit -∗ ukn_pay N (-1)) -∗ pif_exit_k_left.
  Proof using Hkill.
    iIntros "Hk [#HT | Hle]".
    - iApply "Hk". iApply (pif_lexit_of_taint with "HT").
    - iApply ("Hk" with "Hle").
  Qed.

  (* the drained write end, read at the invariant: the cursor is the
     history's length and the history is a prefix of the line *)
  Lemma pif_lexit_of_lend :
    pipe_inv pn γp L -∗ (pipe_out pn L [] ∨ pipe_halt pn) ={⊤}=∗ pif_lexit.
  Proof using .
    iIntros "#Hinv [Hd | Hd]".
    - iDestruct "Hd" as (c) "([%HS _] & Hw & #Hlb)".
      iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
      iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
      iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro]") as "_".
      { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro". by iPureIntro. }
      iModIntro.
      assert (Hc : c = length L).
      { pose proof (prefix_length _ _ Hpre) as Hpl.
        pose proof (pif_drop_nil_le L c (eq_sym HS)) as Hcl. lia. }
      iLeft. rewrite -Hc. iFrame "Hw Hlb".
    - iDestruct "Hd" as (c) "(Hw & #Hsh)".
      iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
      iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
      assert (Hws : ps_ws s0 = take c L).
      { destruct Hpre as [tl Htl]. rewrite -Hlen Htl take_app_length. reflexivity. }
      iDestruct (pws_auth_lb with "Hh") as "[Hh #Hlb]".
      iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro]") as "_".
      { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro". by iPureIntro. }
      iModIntro. iRight. iLeft. iExists c. iFrame "Hw Hsh".
      rewrite -Hws. iFrame "Hlb". iPureIntro.
      pose proof (prefix_length _ _ Hpre) as Hpl. lia.
  Qed.

  (* what [ei_fds] holds towards the exit: the wand while a copy device is
     registered (its end is the payoff), the LEFT wand while a write end is
     registered (its end is the payoff), or the payload itself *)
  Definition pif_kpay (vs : gmap nat pdev) : iProp Σ :=
    ((⌜exists d, vs !! d = Some PDCopy⌝ ∗ pif_exit_k)
     ∨ (⌜exists d, vs !! d = Some PDWr⌝ ∗ pif_exit_k_left)
     ∨ pif_pay)%I.

  Lemma pif_kpay_of_pay (vs : gmap nat pdev) : pif_pay -∗ pif_kpay vs.
  Proof using . iIntros "H". iRight. by iRight. Qed.

  Lemma pif_kpay_cat (vs : gmap nat pdev) (d : nat) :
    vs !! d = Some PDCopy -> (pif_cend -∗ ukn_pay N (-1)) -∗ pif_kpay vs.
  Proof using .
    intros Hv. iIntros "Hk". iLeft. iSplitR; [iPureIntro; by exists d |].
    iApply (pif_exit_k_cat with "Hk").
  Qed.

  Lemma pif_kpay_left (vs : gmap nat pdev) (d : nat) :
    vs !! d = Some PDWr -> pif_exit_k_left -∗ pif_kpay vs.
  Proof using .
    intros Hv. iIntros "Hk". iRight. iLeft. iSplitR; [iPureIntro; by exists d |]. iExact "Hk".
  Qed.

  Lemma pif_kpay_taint (vs : gmap nat pdev) : T -∗ pif_kpay vs -∗ pif_pay.
  Proof using .
    iIntros "#HT [[_ Hk] | [[_ Hkl] | $]]".
    - iApply "Hk". by iLeft.
    - iApply "Hkl". by iLeft.
  Qed.

  (* a registered kind's witness survives another number's departure *)
  Lemma pif_reg_delete_ne (vs : gmap nat pdev) (d : nat) (kd kd' : pdev) :
    vs !! d = Some kd -> kd <> kd' ->
    (exists d', vs !! d' = Some kd') -> exists d', delete d vs !! d' = Some kd'.
  Proof.
    intros Hv Hne [d' Hd']. exists d'.
    rewrite lookup_delete_ne; [exact Hd' |]. intros ->. rewrite Hv in Hd'.
    injection Hd' as Hd'. exact (Hne Hd').
  Qed.

  (* a device of neither wand's kind leaves the registry: the witness stays *)
  Lemma pif_kpay_delete (vs : gmap nat pdev) (d : nat) (kd : pdev) :
    vs !! d = Some kd -> kd <> PDCopy -> kd <> PDWr ->
    pif_kpay vs -∗ pif_kpay (delete d vs).
  Proof using .
    intros Hv Hnc Hnw. iIntros "[[%Hreg Hk] | [[%Hreg Hkl] | Hpay]]".
    - iLeft. iFrame "Hk". iPureIntro. exact (pif_reg_delete_ne vs d kd PDCopy Hv Hnc Hreg).
    - iRight. iLeft. iFrame "Hkl". iPureIntro. exact (pif_reg_delete_ne vs d kd PDWr Hv Hnw Hreg).
    - iRight. by iRight.
  Qed.

  (* ...a copy device leaves while the exit is the left wand's or paid *)
  Lemma pif_kpay_delete_copy (vs : gmap nat pdev) (d : nat) :
    vs !! d = Some PDCopy ->
    ((⌜exists d', vs !! d' = Some PDWr⌝ ∗ pif_exit_k_left) ∨ pif_pay) -∗ pif_kpay (delete d vs).
  Proof using .
    intros Hv. iIntros "[[%Hreg Hkl] | Hpay]".
    - iRight. iLeft. iFrame "Hkl". iPureIntro.
      exact (pif_reg_delete_ne vs d PDCopy PDWr Hv ltac:(discriminate) Hreg).
    - iRight. by iRight.
  Qed.

  (* ...a write end leaves while the exit is the copy wand's or paid *)
  Lemma pif_kpay_delete_wr (vs : gmap nat pdev) (d : nat) :
    vs !! d = Some PDWr ->
    ((⌜exists d', vs !! d' = Some PDCopy⌝ ∗ pif_exit_k) ∨ pif_pay) -∗ pif_kpay (delete d vs).
  Proof using .
    intros Hv. iIntros "[[%Hreg Hk] | Hpay]".
    - iLeft. iFrame "Hk". iPureIntro.
      exact (pif_reg_delete_ne vs d PDWr PDCopy Hv ltac:(discriminate) Hreg).
    - iRight. by iRight.
  Qed.

  (* the application's persistent facts the laws read: the taint's two
     readings, the protocol *)
  Definition pif_env : iProp Σ :=
    (□ (T -∗ app_taint) ∗ □ (T -∗ app_sup) ∗ pipe_inv pn γp L)%I.

  Global Instance pif_env_persistent : Persistent pif_env.
  Proof using . rewrite /pif_env. apply _. Qed.

  Lemma pif_env_of_inv : pipe_inv pn γp L -∗ pif_env.
  Proof using Heq Hkill.
    iIntros "#Hinv". rewrite /pif_env. iFrame "Hinv". iSplit.
    - iIntros "!> #Ht". rewrite Hkill. iExact "Ht".
    - iIntros "!> #Ht". rewrite /AppInv.app_sup. rewrite Heq. cbn [app_pred app_run].
      iApply (pipe_sup_of_taint γ r with "Ht").
  Qed.

  Lemma pif_env_inv : pif_env -∗ pipe_inv pn γp L.
  Proof using . iIntros "(_ & _ & $)". Qed.

  (* [ei_fds], at its ledger, its registry's values and its pool *)
  Definition pif_fds_at (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) : iProp Σ :=
    (UserFd.ustd γfd l ∗ pif_kpay vs ∗ ⌜pif_ok fdm l vs⌝
     ∗ own γreg (pif_pool (dom vs) w)
     ∗ ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x)
     ∗ pif_env)%I.

  Definition pif_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (vs : gmap nat pdev) (w : nat -> pdev), pif_fds_at fdm l vs w)%I.

  (* the console: the popen device of the open round, the generic one, or
     a slot nothing is written on *)
  Definition pif_out (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    ((pif_tok d (1/2) PDPCons ∗ pcons2 alts)
     ∨ (pif_tok d (1/2) PDCons ∗ pcons1 alts)
     ∨ (pif_tok d (1/2) PDMute ∗ ⌜alts = [[]]⌝))%I.

  (* the pipe's write end owing one alternative, and halted *)
  Definition pif_outh (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    (pif_tok d (1/2) PDWr ∗ ∃ S : list (bv 8), ⌜alts = [S]⌝ ∗ pipe_out pn L S)%I.
  Definition pif_halt (d : nat) : iProp Σ :=
    (pif_tok d (1/2) PDWr ∗ pipe_halt pn)%I.

  (* the pipe's read end (DInE), and its end of file at ANY point of the
     line (DInEnd: an ended device owes nothing more) *)
  Definition pif_in (d : nat) (S : list (bv 8)) : iProp Σ :=
    (pif_tok d (1/2) PDRd ∗ pipe_in pn L S)%I.
  Definition pif_in_end (d : nat) : iProp Σ :=
    (pif_tok d (1/2) PDRd ∗ ∃ S : list (bv 8), pipe_in_eof pn L S)%I.

  (* THE COPY DEVICE.  The console's persistent context at the two-writer
     round, WITHOUT the reader's fact [YR] *)
  Definition pif_cctx : iProp Σ :=
    (⌜Z.of_nat (length L) < 2 ^ 31⌝
     ∗ era_pin γ (S gen_id) v
     ∗ pipe_link_taint g
     ∗ blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR
     ∗ □ (XL -∗ YR ={↑pipeN}=∗ False))%I.

  Global Instance pif_cctx_persistent : Persistent pif_cctx.
  Proof using . rewrite /pif_cctx. apply _. Qed.

  (* the two cursors: the pipe's read cursor at [c] and the family's
     console cursor at [w] (cat's half, [UShPipeCatRound.pcat_ch]) *)
  Definition pif_copy_core (c w : nat) : iProp Σ :=
    (⌜(w <= c)%nat /\ (c <= length L)%nat⌝ ∗ rcur pn c ∗ pcat_ch g gR gM w)%I.

  Definition pif_copy (d : nat) (h : bool) (Sc pending : list (bv 8)) : iProp Σ :=
    (⌜h = false⌝ ∗ pif_tok d (1/2) PDCopy ∗ pif_cctx
     ∗ ∃ c w : nat, ⌜Sc = drop c L /\ pending = drop w (take c L)⌝ ∗ pif_copy_core c w)%I.

  Definition pif_copy_end (d : nat) (h : bool) (pending : list (bv 8)) : iProp Σ :=
    (⌜h = false⌝ ∗ pif_tok d (1/2) PDCopy ∗ pif_cctx
     ∗ ∃ c w : nat, ⌜pending = drop w (take c L)⌝ ∗ pif_copy_core c w
                    ∗ eof_shot pn (take c L))%I.

  (* the drained end IS the round's reading of cat's exit *)
  Lemma pif_copy_end_cend (d : nat) (h : bool) :
    pif_copy_end d h [] -∗ pif_tok d (1/2) PDCopy ∗ pif_cend.
  Proof using .
    iIntros "(_ & Htk & _ & %c & %w & %Hp & ([%Hwc %HcL] & Hr & Hc) & #Heof)".
    rewrite (pif_drained_eq L c w Hwc HcL Hp).
    iFrame "Htk". iExists c. iFrame "Hc". iSplitR; [by iLeft |]. by iLeft.
  Qed.

  Definition pif_dev (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DOut alts => pif_out d alts | DOutH alts => pif_outh d alts | DOutM _ => False
    | DHalt => pif_halt d | DIn _ => False | DInE Sin => pif_in d Sin
    | DInEnd => pif_in_end d
    | DCopy h Sc p => pif_copy d h Sc p | DCopyEnd h p => pif_copy_end d h p
    | DCopyHalt => False
    end%I.

  (* the scope of paths is empty *)
  Definition pif_filesr (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      : iProp Σ := ⌜paths = []⌝%I.

  (* THE TAINT: the free handler's, at the application's taint *)
  Definition pif_taint (held : gset Z) : iProp Σ := fh_taint T N held.

  Lemma pif_taint_pays (held : gset Z) (t : proc) :
    safe_fds held t -> pif_taint held -∗ tree_pay N P t.
  Proof using HNc Hsr Hsw Hso Hsc Hse.
    exact (fh_taint_pays T N P Hsr Hsw Hso Hsc Hse held t).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  small facts                                                         *)
  (* ------------------------------------------------------------------- *)

  (* the taint, out of what a law holds at a taint arm: no tail handle *)
  Lemma pif_taint_of_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) :
    pif_ok fdm l vs ->
    app_taint -∗ UserFd.ustd γfd l -∗ pif_kpay vs -∗ pif_env -∗ pif_taint (dom fdm).
  Proof using Hkill.
    intros Hok. iIntros "#Ht Hstd Hkp #He". rewrite /pif_env.
    iDestruct "He" as "(#Hk & #Hs & _)".
    iEval (rewrite Hkill) in "Ht".
    iDestruct (pif_kpay_taint with "Ht Hkp") as "Hpay".
    rewrite /pif_taint /fh_taint /pif_pay. iFrame "Ht Hk Hs Hpay".
    iExists l, ∅. iFrame "Hstd". iSplit; [| by rewrite big_sepM_empty].
    iPureIntro. intros fd Hfd. apply elem_of_dom in Hfd as [d Hd].
    destruct Hok as (H1 & H2 & _). pose proof (H1 fd d Hd) as H0.
    destruct (pif_row_open _ _ _ (H2 fd d Hd)) as (Hlt & st & Hl & Hne).
    split; [unfold NSTD, NOFILE in *; lia |]. left. split; [exact Hlt |].
    exists st. split; [exact Hl | exact Hne].
  Qed.

  (* the kind a device's state admits *)
  Definition pif_kind (x : dspec) (kd : pdev) : Prop :=
    match x with
    | DOut _ => kd = PDPCons \/ kd = PDCons \/ kd = PDMute
    | DOutH _ | DHalt => kd = PDWr
    | DInE _ | DInEnd => kd = PDRd
    | DCopy _ _ _ | DCopyEnd _ _ => kd = PDCopy
    | DOutM _ | DIn _ | DCopyHalt => False
    end.

  (* the token of a device, whatever its state *)
  Lemma pif_dev_tok (d : nat) (x : dspec) :
    pif_dev d x -∗
    ∃ kd : pdev, ⌜pif_kind x kd⌝ ∗ pif_tok d (1/2) kd ∗ (pif_tok d (1/2) kd -∗ pif_dev d x).
  Proof using .
    destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl;
      [| | iIntros "[]" | | iIntros "[]" | | | | | iIntros "[]"].
    - iIntros "[[Htk Hd] | [[Htk Hd] | [Htk %Hm]]]".
      + iExists PDPCons. iFrame "Htk". iSplit; [iPureIntro; by left |].
        iIntros "Htk". iLeft. iFrame.
      + iExists PDCons. iFrame "Htk". iSplit; [iPureIntro; by right; left |].
        iIntros "Htk". iRight. iLeft. iFrame.
      + iExists PDMute. iFrame "Htk". iSplit; [iPureIntro; by right; right |].
        iIntros "Htk". iRight. iRight. iFrame "Htk". by iPureIntro.
    - iIntros "[Htk Hd]". iExists PDWr. iFrame "Htk". iSplit; [done |]. iIntros "Htk". iFrame.
    - iIntros "[Htk Hd]". iExists PDWr. iFrame "Htk". iSplit; [done |]. iIntros "Htk". iFrame.
    - iIntros "[Htk Hd]". iExists PDRd. iFrame "Htk". iSplit; [done |]. iIntros "Htk". iFrame.
    - iIntros "[Htk Hd]". iExists PDRd. iFrame "Htk". iSplit; [done |]. iIntros "Htk". iFrame.
    - iIntros "(%Hh & Htk & Hd)". iExists PDCopy. iFrame "Htk". iSplit; [done |].
      iIntros "Htk". iSplitR; [by iPureIntro |]. iFrame "Htk Hd".
    - iIntros "(%Hh & Htk & Hd)". iExists PDCopy. iFrame "Htk". iSplit; [done |].
      iIntros "Htk". iSplitR; [by iPureIntro |]. iFrame "Htk Hd".
  Qed.

  (* the descriptor is a standard slot of the kind the registry says *)
  Lemma pif_fds_row (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) (fd : Z) (d : nat)
      (kd : pdev) :
    pif_ok fdm l vs -> fdm !! fd = Some d -> vs !! d = Some kd ->
    exists k : nat, fd = Z.of_nat k /\ (k < NSTD)%nat /\ pif_row (Some kd) (Z.of_nat k) l.
  Proof.
    intros (H1 & H2 & _) Hfd Hv. pose proof (H1 fd d Hfd) as H0.
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (Z_of_nat_complete fd H0) as [k ->]. exists k. split; [reflexivity |].
    split; [| exact Hrow]. destruct (pif_row_open _ _ _ Hrow) as [Hlt _]. lia.
  Qed.

  (* the copy device's rows, by the filter's descriptor *)
  Lemma pif_copy_row_in (l : list fdstate) (k : nat) :
    pif_row (Some PDCopy) (Z.of_nat k) l -> Z.of_nat k = copy_in ->
    k = 0%nat /\ exists wb, l !! 0%nat = Some (FdOpen true wb (FdPipe γp)).
  Proof.
    intros [[Hk Hl] | [Hk _]] Hfd; [| unfold copy_in, copy_out in *; lia].
    split; [unfold copy_in in Hk; lia | exact Hl].
  Qed.

  Lemma pif_copy_row_out (l : list fdstate) (k : nat) :
    pif_row (Some PDCopy) (Z.of_nat k) l -> Z.of_nat k = copy_out ->
    k = 1%nat /\ exists rb, l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)).
  Proof.
    intros [[Hk _] | [Hk Hl]] Hfd; [unfold copy_in, copy_out in *; lia |].
    split; [unfold copy_out in Hk; lia | exact Hl].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE FIELDS THE KERNEL REFUSES (the header's list)                   *)
  (* ------------------------------------------------------------------- *)

  (* ...packaged as ONE proposition first (lane F), so that a file above
     this section can assume them at any minted record and any registry
     name in one binder: [pif_refused_holds] below is the tie to the two
     hypotheses the laws are stated at. *)
  Definition pif_refused : Prop :=
    (forall (fdm : fdmap) (fd : Z) (d : nat) (bs : list (bv 8)) (K : Z -> iProp Σ),
       bs <> [] -> fdm !! fd = Some d -> 2 ^ 31 <= Z.of_nat (length bs) ->
       pif_fds fdm -∗ pif_halt d -∗
       ((pif_fds fdm -∗ pif_halt d -∗ K (-1)) ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
       wr_obl N P fd bs K)
    /\ (forall (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
          (w : nat -> pdev) (fd : nat) (d : nat) (x : dspec) (K : Z -> iProp Σ),
          fdm !! Z.of_nat fd = Some d -> (vs !! d = Some PDRd \/ vs !! d = Some PDCopy) ->
          l !! fd = Some (FdOpen true false (FdPipe γp)) ->
          pif_fds_at fdm l vs w -∗ pif_dev d x -∗
          ((pif_fds fdm -∗ pif_dev d x -∗ K 0) ∧ (pif_fds fdm -∗ pif_dev d x -∗ K (-1))
           ∧ (∀ y, pif_taint (dom fdm) -∗ K y)) -∗
          wr_obl N P (Z.of_nat fd) [] K).

  Hypothesis Hhalt_long : forall (fdm : fdmap) (fd : Z) (d : nat) (bs : list (bv 8))
      (K : Z -> iProp Σ),
    bs <> [] -> fdm !! fd = Some d -> 2 ^ 31 <= Z.of_nat (length bs) ->
    pif_fds fdm -∗ pif_halt d -∗
    ((pif_fds fdm -∗ pif_halt d -∗ K (-1)) ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.

  Hypothesis Hnil_ro : forall (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (fd : nat) (d : nat) (x : dspec) (K : Z -> iProp Σ),
    fdm !! Z.of_nat fd = Some d -> (vs !! d = Some PDRd \/ vs !! d = Some PDCopy) ->
    l !! fd = Some (FdOpen true false (FdPipe γp)) ->
    pif_fds_at fdm l vs w -∗ pif_dev d x -∗
    ((pif_fds fdm -∗ pif_dev d x -∗ K 0) ∧ (pif_fds fdm -∗ pif_dev d x -∗ K (-1))
     ∧ (∀ y, pif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P (Z.of_nat fd) [] K.

  Lemma pif_refused_holds : pif_refused.
  Proof using Hhalt_long Hnil_ro.
    exact (conj Hhalt_long Hnil_ro).
  Qed.

  (* THE CLOSE GAP, CLOSED (lane closegap): the LAST close of a copy device
     BEFORE its end while the exit wand is held -- the wand wants the EOF
     shot and the two cursors equal, which an open device does not have --
     is refuted by the close rule's [drained_at_close] fact: at a copy
     device it is [drained], and the registry's kind pins the device to a
     copy kind. *)
  Lemma pif_close_open (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> vs !! d = Some PDCopy -> ~ drained x ->
    drained_at_close x ->
    pif_ok fdm l vs ->
    UserFd.ustd γfd l -∗ pif_exit_k -∗ own γreg (pif_pool (dom vs) w) -∗
    ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) -∗ pif_env -∗
    pif_filesr files paths -∗ pif_dev d x -∗
    ((pif_fds (delete fd fdm) -∗ pif_filesr files paths -∗ K 0)
     ∧ (∀ y, pif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using .
    intros _ _ Hv Hndr Hdc _. iIntros "_ _ _ Htoks _ _ Hd _".
    iDestruct (pif_dev_tok with "Hd") as (kd) "(%Hkd & Htk & _)".
    iDestruct (pif_toks_agree vs d PDCopy kd with "Htoks Htk") as "(%Hvv & _ & _)"; [exact Hv |].
    subst kd. exfalso.
    destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd;
      try (destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate Hkd);
      try discriminate Hkd; try exact Hkd; exact (Hndr Hdc).
  Qed.

  (* ...its twin at the WRITE END (lane F): the last close of the pipe's
     write end BEFORE it is drained while the left wand is held -- the
     wand wants the cursor at the line's end or the reader's shot, which
     an open end owing bytes has neither of *)
  Lemma pif_close_open_w (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> vs !! d = Some PDWr -> ~ drained x ->
    drained_at_close x ->
    pif_ok fdm l vs ->
    UserFd.ustd γfd l -∗ pif_exit_k_left -∗ own γreg (pif_pool (dom vs) w) -∗
    ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) -∗ pif_env -∗
    pif_filesr files paths -∗ pif_dev d x -∗
    ((pif_fds (delete fd fdm) -∗ pif_filesr files paths -∗ K 0)
     ∧ (∀ y, pif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using .
    intros _ _ Hv Hndr Hdc _. iIntros "_ _ _ Htoks _ _ Hd _".
    iDestruct (pif_dev_tok with "Hd") as (kd) "(%Hkd & Htk & _)".
    iDestruct (pif_toks_agree vs d PDWr kd with "Htoks Htk") as "(%Hvv & _ & _)"; [exact Hv |].
    subst kd. exfalso.
    destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd;
      try (destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate Hkd);
      try discriminate Hkd; try exact Hkd; exact (Hndr Hdc).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE LAWS                                                            *)
  (* ------------------------------------------------------------------- *)

  (* the descriptors re-packed after a law that moved nothing in them *)
  Local Ltac pif_repack :=
    iExists _, _, _; iFrame "Hstd Hkp Hpool Htoks He"; by iPureIntro.

  (* [ei_write] at the console, any kind *)
  Lemma pif_write (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    pif_fds fdm -∗ pif_out d alts -∗
    ((pif_fds fdm -∗ pif_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hcons Hsw HPc Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers.
    intros Hne Hfd Ha Hpre. iIntros "Hfds Hout HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct "Hout" as "[[Htk Hd] | [[Htk Hd] | [Htk %Hm]]]".
    - (* the popen device *)
      iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst kd.
      destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pcons_write g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
                (YR_pers := YR_pers) Hnd Hwit2 Hwit1 N P (HPc := HPc) Hsw l k rb alts a bs K
                Hlt Hrow Ha Hpre with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]"); [pif_repack |].
      iLeft. iFrame "Htk Hd".
    - (* the generic device *)
      iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst kd.
      destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (cons_write_gl_at pipe_lm (pipe_params g) (pipe_links g)
                (LINKS_pers := pipe_links_persistent g)
                (pipe_links_gl_w g) (pipe_links_gl_blk g) (pipe_links_gl_taint g)
                N P (HPc := HPc) Hsw v I l k rb alts a bs K Hlt Hrow Ha Hpre with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]"); [pif_repack |].
      iRight. iLeft. iFrame "Htk Hd".
    - (* the mute slot: nothing nonempty is a prefix of what it owes *)
      exfalso. subst alts. apply elem_of_list_singleton in Ha. subst a.
      destruct Hpre as [k Hk]. symmetry in Hk. apply app_eq_nil in Hk as [Hbs _].
      exact (Hne Hbs).
  Qed.

  (* [ei_write_h] at the pipe's write end *)
  Lemma pif_write_h (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    pif_fds fdm -∗ pif_outh d alts -∗
    ((pif_fds fdm -∗ pif_outh d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (pif_fds fdm -∗ pif_halt d -∗ K (-1))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hkill Hsw.
    intros Hne Hfd Ha Hpre. iIntros "Hfds [Htk Hd] HK".
    iDestruct "Hd" as (S) "[-> Hd]".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_write N P Hsw pn γp L S l k rb a bs K Hlt Hrow Ha Hpre Hne with "Hinv Hstd Hd").
    iSplit; [| iSplit].
    - iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]"); [pif_repack |].
      iFrame "Htk". iExists (drop (length bs) a). iFrame "Hd". by iPureIntro.
    - iIntros "Hstd Hh". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Hh Htk] [Htk Hh]"); [pif_repack |].
      iFrame "Htk Hh".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hkp He").
  Qed.

  (* [ei_write_halt]: -1 at the halted write end, at a count the kernel
     reads as a C int; the rest is [Hhalt_long] *)
  Lemma pif_write_halt (fdm : fdmap) (fd : Z) (d : nat) (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_halt d -∗
    ((pif_fds fdm -∗ pif_halt d -∗ K (-1)) ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hkill Hsw Hhalt_long.
    intros Hne Hfd.
    destruct (decide (Z.of_nat (length bs) < 2 ^ 31)) as [Hbnd | Hbnd]; last first.
    { assert (Hge : 2 ^ 31 <= Z.of_nat (length bs))
        by (change (2 ^ 31) with 2147483648 in Hbnd |- *; lia).
      exact (Hhalt_long fdm fd d bs K Hne Hfd Hge). }
    iIntros "Hfds [Htk Hh] HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_write_halt N P Hsw pn γp L l k rb bs K Hlt Hrow Hne Hbnd with "Hinv Hstd Hh").
    iSplit.
    - iIntros "Hstd Hh". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hh Htk] [Htk Hh]"); [pif_repack |].
      iFrame "Htk Hh".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hkp He").
  Qed.

  (* a ZERO-LENGTH write at a console row, at ANY device resource [R]:
     [UkFileIface.fif_cons_nil]'s walk, which never looks inside the
     device -- the chain of no bytes is its own stop *)
  Lemma pif_cons_nil (l : list fdstate) (fd : nat) (rb : bool) (R : iProp Σ)
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ R -∗ (UserFd.ustd γfd l -∗ R -∗ K 0) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw HPc.
    intros Hfd Hl. iIntros "Hstd Hd HK".
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 #Hcode Hsrc Hrun Hcont".
    cbn [length] in *.
    iEval (rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx)) 0 f
                      (or_introl eq_refl))) in "Hsrc".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Ham0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _ ltac:(vm_compute; discriminate)).
    assert (Ham1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _ ltac:(vm_compute; discriminate)).
    assert (Ham2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _ ltac:(vm_compute; discriminate)).
    assert (Hi0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd)
      by (rewrite Ham0; exact Ha0).
    assert (Hcz : sys_rw_count (mword_of_int (Z.of_nat 0) : mword 64) = Z.of_nat 0)
      by (apply cons_count_is; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count (m1 !!! Regidx a2_idx)) = 0%nat)
      by (rewrite Ham2 Ha2 Hcz; lia).
    assert (Hsys : usysno m1 = 16).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Hal6 Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr
                    (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4)) 2
                  = true) by (rewrite E6; exact Hal6).
    unfold stub_ret.
    iApply (cons_leaf N h1 m1 _ avail
              (xfam_wr (fun _ : nat => (R ∗ emp)%I) (ukn_pay N))
              l tx dq 0 f Hsys Hal with "Hec Hrun [Hd] Hstd [Hsrc]").
    { iApply (uwrite_chain_sup_ret N (fun _ : nat => R) emp%I _ _ l fd rb CONSOLE Hi0 Hfd Hl).
      iIntros (Mh pm sz) "Hheap". iFrame "Hheap". iSplitR; [done |].
      rewrite Hcnt. cbn [cons_out_chain]. iExact "Hd". }
    { rewrite Ham1. iExact "Hsrc". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun _ : nat => (R ∗ emp)%I)
                 (ukn_pay N) Wv ret (uvis_M Wv) (uvis_fd Wv) cw' cs'
                 l fd rb 0
                 ltac:(rewrite Hka0; exact Hi0)
                 Hfd Htk Hl
                 ltac:(rewrite Hka2 Ham2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hret [Hd _]]".
    rewrite Ham1 E6.
    iApply ("Hret" $! h' ret with "Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Hstd Hd] [Hs1] Hrun").
    - rewrite Hret. change (bv_signed (mword_of_int (Z.of_nat 0) : mword 64)) with 0.
      iApply ("HK" with "Hstd Hd").
    - rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx)) 0 f
                 (or_introl eq_refl)).
      iExact "Hs1".
  Qed.

  (* a zero-length write at a pipe row, writable or [Hnil_ro] *)
  Local Ltac pif_pipe_nil_arms :=
    iSplit; [| iSplit];
    [ iIntros "Hstd Hd"; iDestruct "HK" as "[HK _]"; iApply ("HK" with "[-Hd] Hd"); pif_repack
    | iIntros "Hstd Hd"; iDestruct "HK" as "[_ [HK _]]"; iApply ("HK" with "[-Hd] Hd"); pif_repack
    | iIntros "Hstd #Ht" (z); iDestruct "HK" as "[_ [_ HK]]"; iApply "HK";
      iApply (pif_taint_of_fds with "Ht Hstd Hkp He"); assumption ].

  (* [ei_write_nil]: by the descriptor's kind *)
  Lemma pif_write_nil (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_dev d x -∗
    ((pif_fds fdm -∗ pif_dev d x -∗ K 0) ∧ (pif_fds fdm -∗ pif_dev d x -∗ K (-1))
     ∧ (∀ y, pif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.
  Proof using Hkill Hsw HPc Hnil_ro.
    intros Hfd. iIntros "Hfds Hd HK".
    iDestruct (pif_dev_tok with "Hd") as (kd) "(%Hkd & Htk & Hback)".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (pif_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iDestruct ("Hback" with "Htk") as "Hd".
    destruct kd.
    - (* the console, three kinds *)
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pif_cons_nil l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd"). pif_repack.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pif_cons_nil l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd"). pif_repack.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pif_cons_nil l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd"). pif_repack.
    - (* the write end *)
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_write_nil N P Hsw γp l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      pif_pipe_nil_arms.
    - (* the read end: writable, or [Hnil_ro] *)
      destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      destruct wb.
      + iApply (pipe_write_nil N P Hsw γp l k true (pif_dev d x) K Hlt Hrow with "Hstd Hd").
        pif_pipe_nil_arms.
      + iApply (Hnil_ro fdm l vs w k d x K Hfd (or_introl Hv) Hrow
                  with "[Hstd Hkp Hpool Htoks] Hd HK").
        iFrame "Hstd Hkp Hpool Htoks He". by iPureIntro.
    - (* the copy device: its read end, or its console *)
      destruct Hrow as [[Hk (wb & Hrow)] | [Hk (rb & Hrow)]].
      + assert (k = 0%nat) as -> by (unfold copy_in in Hk; lia).
        destruct wb.
        * iApply (pipe_write_nil N P Hsw γp l 0 true (pif_dev d x) K Hlt Hrow with "Hstd Hd").
          pif_pipe_nil_arms.
        * iApply (Hnil_ro fdm l vs w 0 d x K Hfd (or_intror Hv) Hrow
                    with "[Hstd Hkp Hpool Htoks] Hd HK").
          iFrame "Hstd Hkp Hpool Htoks He". by iPureIntro.
      + assert (k = 1%nat) as -> by (unfold copy_out in Hk; lia).
        iApply (pif_cons_nil l 1 rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
        iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
        iApply ("HK" with "[-Hd] Hd"). pif_repack.
  Qed.

  (* the read end's row: the descriptor's slot, and [UkPipeDev.pipe_read] *)
  Local Ltac pif_read_row Hok Hfd Hv :=
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow);
    destruct Hrow as (_ & wb & Hrow); rewrite Nat2Z.id in Hrow.

  (* [ei_read_e] at DInE: the chunk, or the end of file wherever the line
     stands *)
  Lemma pif_read_e (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        pif_fds fdm -∗ pif_in d S' -∗ K (RdBytes cb))
     ∧ (pif_fds fdm -∗ pif_in_end d -∗ K (RdBytes []))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd. iIntros "Hfds [Htk Hd] HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. pif_read_row Hok Hfd Hv.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read N P Hsr pn γp L Sin l k wb n K Hlt Hrow Hn with "Hinv Hstd Hd").
    iSplit; [| iSplit].
    - iIntros (cb S') "%Hc Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb S' with "[%] [-Hd Htk] [Htk Hd]"); [exact Hc | pif_repack |].
      iFrame "Htk Hd".
    - iIntros "Hstd Hd". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]"); [pif_repack |].
      iFrame "Htk". iExists Sin. iFrame "Hd".
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hkp He").
  Qed.

  (* [ei_read_end] at DInEnd: the empty chunk again ([UkPipeDev.pipe_read_eof]) *)
  Lemma pif_read_end (fdm : fdmap) (fd : Z) (d : nat) (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_in_end d -∗
    ((pif_fds fdm -∗ pif_in_end d -∗ K (RdBytes []))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd. iIntros "Hfds [Htk Hd] HK".
    iDestruct "Hd" as (S c) "(%Hc & Hr & #Heof)".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. pif_read_row Hok Hfd Hv.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read_eof N P Hsr pn γp L c l k wb n K Hlt Hrow Hn with "Hinv Hstd Hr Heof").
    iSplit.
    - iIntros "Hstd Hr". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hr Htk] [Htk Hr]"); [pif_repack |].
      iFrame "Htk". iExists S, c. iFrame "Hr Heof". by iPureIntro.
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hkp He").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE COPY DEVICE'S LAWS                                              *)
  (* ------------------------------------------------------------------- *)

  (* [ei_read_copy]: the read end at the copy device's cursor, through
     [UkPipeDev.pipe_read_at]; a chunk joins the pending bytes *)
  Lemma pif_read_copy (fdm : fdmap) (fd : Z) (d : nat) (h : bool) (Sin p : list (bv 8))
      (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
    pif_fds fdm -∗ pif_copy d h Sin p -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗ ⌜cb <> []⌝ -∗
        pif_fds fdm -∗ pif_copy d h S' (p ++ cb) -∗ K (RdBytes cb))
     ∧ (pif_fds fdm -∗ pif_copy_end d h p -∗ K (RdBytes []))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd Hfd0. iIntros "Hfds Hd HK".
    iDestruct "Hd" as "(%Hh & Htk & #Hctx & %c & %w & [%HS %Hp] & [%Hwc %HcL] & Hr & Hc)".
    subst h.
    iDestruct "Hfds" as (l vs w') "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    rewrite Hk in Hfd0. subst fd. destruct (pif_copy_row_in l k Hrow Hfd0) as [-> (wb & Hl0)].
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read_at N P Hsr pn γp L c l 0 wb n K Hlt Hl0 Hn with "Hinv Hstd Hr").
    iSplit; [| iSplit].
    - iIntros (cb) "[%Hne %Hchk] Hstd Hr". iModIntro. iDestruct "HK" as "[HK _]".
      assert (HcbL : (c + length cb <= length L)%nat).
      { destruct Hchk as (Hdc & _ & _). apply (f_equal length) in Hdc.
        rewrite length_drop length_app in Hdc. lia. }
      iApply ("HK" $! cb (drop (c + length cb) L) with "[%] [%] [-Htk Hr Hc] [Htk Hr Hc]");
        [rewrite HS; exact Hchk | exact Hne | pif_repack |].
      iSplitR; [done |]. iFrame "Htk Hctx". iExists (c + length cb)%nat, w.
      iSplitR.
      { iPureIntro. split; [reflexivity |]. rewrite Hp.
        destruct Hchk as (Hdc & _ & _). exact (pif_pending_grow L c w cb _ Hwc HcL Hdc). }
      iFrame "Hr Hc". iPureIntro. split; lia.
    - iIntros "Hstd Hr #Heof". iModIntro. iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Htk Hr Hc] [Htk Hr Hc]"); [pif_repack |].
      iSplitR; [done |]. iFrame "Htk Hctx". iExists c, w. iFrame "Hr Hc Heof".
      iPureIntro. split; [exact Hp | split; [exact Hwc | exact HcL]].
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hkp He").
  Qed.

  (* [ei_read_copy_end]: the read after the end answers 0
     ([UkPipeDev.pipe_read_eof]) *)
  Lemma pif_read_copy_end (fdm : fdmap) (fd : Z) (d : nat) (h : bool) (p : list (bv 8))
      (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
    pif_fds fdm -∗ pif_copy_end d h p -∗
    ((pif_fds fdm -∗ pif_copy_end d h p -∗ K (RdBytes []))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd Hfd0. iIntros "Hfds Hd HK".
    iDestruct "Hd" as "(%Hh & Htk & #Hctx & %c & %w & %Hp & ([%Hwc %HcL] & Hr & Hc) & #Heof)".
    subst h.
    iDestruct "Hfds" as (l vs w') "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    rewrite Hk in Hfd0. subst fd. destruct (pif_copy_row_in l k Hrow Hfd0) as [-> (wb & Hl0)].
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read_eof N P Hsr pn γp L c l 0 wb n K Hlt Hl0 Hn with "Hinv Hstd Hr Heof").
    iSplit.
    - iIntros "Hstd Hr". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hr Hc] [Htk Hr Hc]"); [pif_repack |].
      iSplitR; [done |]. iFrame "Htk Hctx". iExists c, w. iFrame "Hr Hc Heof".
      iPureIntro. split; [exact Hp | split; [exact Hwc | exact HcL]].
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hkp He").
  Qed.

  (* THE CONSOLE CORE'S DEVICE FOR THE COPY DEVICE'S WRITE: at the read
     cursor [c] (fixed during a write), the console cursor [w] owing the
     read-but-unwritten segment [drop w (take c L)]; the read cursor and
     the protocol ride along, so that the FIRST byte's reader fact is
     derived at the byte ([pif_wD_step]) *)
  Definition pif_wD (c : nat) (alts : list (list (bv 8))) : iProp Σ :=
    (pif_cctx ∗ pipe_inv pn γp L ∗ ⌜(c <= length L)%nat⌝ ∗ rcur pn c
     ∗ ∃ w : nat, ⌜alts = [drop w (take c L)] /\ (w <= c)%nat⌝ ∗ pcat_ch g gR gM w)%I.

  Lemma pif_wD_short (c : nat) (alts : list (list (bv 8))) :
    pif_wD c alts -∗ ⌜cons_short alts⌝.
  Proof using .
    iIntros "((%HL & _) & _ & %HcL & _ & %w & [-> _] & _)". iPureIntro.
    apply Forall_singleton. rewrite length_drop length_take Nat.min_l; [| exact HcL]. lia.
  Qed.

  Lemma pif_wD_sub (c : nat) (alts : list (list (bv 8))) (a : list (bv 8)) :
    a ∈ alts -> pif_wD c alts -∗ pif_wD c [a].
  Proof using .
    intros Ha. iIntros "(#Hctx & #Hinv & %HcL & Hr & %w & [-> %Hwc] & Hc)".
    apply elem_of_list_singleton in Ha. subst a.
    iFrame "Hctx Hinv Hr". iSplitR; [by iPureIntro |]. iExists w. iFrame "Hc". by iPureIntro.
  Qed.

  (* ONE BYTE: the reader's fact off the read cursor ([PipeProto.
     pws_lb_of_rcur] under the link's fancy update, weakened to the line's
     first byte, read as [YR] by [Hyr]), then the family's step *)
  Lemma pif_wD_step (c : nat) (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    pif_wD c [x] -∗ out_link Uart0 (S gen_id) b (pif_wD c [drop 1 x]).
  Proof using Hcons Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr.
    intros Hb. iIntros "(#Hctx & #Hinv & %HcL & Hr & %w & [%Hx %Hwc] & Hc)".
    injection Hx as ->.
    rewrite lookup_drop Nat.add_0_r in Hb. apply lookup_take_Some in Hb as [HbL Hwlt].
    iDestruct "Hctx" as "(%HL & #Hpin & #Ht & #Hblk & #Hex)".
    iApply fupd_out_link.
    iMod (pws_lb_of_rcur (⊤ ∖ ↑uartN Uart0) pn γp L c pif_pipeN_uart with "Hinv Hr")
      as "[Hr #Hlb]".
    iAssert YR as "#HYR".
    { iApply Hyr. iApply (pws_lb_weaken pn (take c L) (take 1%nat L) with "Hlb").
      exists (drop 1 (take c L)).
      rewrite -{1}(take_drop 1 (take c L)) take_take Nat.min_l; [reflexivity | lia]. }
    iModIntro.
    iApply (pcat_step_at g Hcons v I L gL gR gM XL YR w b _ HbL Hnd Hwit2 Hwit1
              with "Hex Ht Hpin Hblk HYR Hc").
    iIntros "Hc". iFrame "Hinv Hr".
    iSplitR. { iSplitR; [by iPureIntro |]. iFrame "Hpin Ht Hblk". iExact "Hex". }
    iSplitR; [by iPureIntro |]. iExists (S w). iFrame "Hc". iPureIntro. split; [| lia].
    rewrite drop_drop. do 2 f_equal. lia.
  Qed.

  (* the copy device's console write: [UkConsOut.cons_write] at [pif_wD]
     from the descriptor's console row ([copy_out]) *)
  Lemma pif_copy_write (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) (w' : nat -> pdev)
      (d : nat) (c w : nat) (p bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! copy_out = Some d -> vs !! d = Some PDCopy ->
    pif_ok fdm l vs -> (w <= c)%nat -> (c <= length L)%nat ->
    p = drop w (take c L) -> bs `prefix_of` p ->
    UserFd.ustd γfd l -∗ pif_env -∗ rcur pn c -∗ pcat_ch g gR gM w -∗ pif_cctx -∗
    (∀ w2 : nat, ⌜drop (length bs) p = drop w2 (take c L) /\ (w2 <= c)%nat⌝ -∗
       UserFd.ustd γfd l -∗ rcur pn c -∗ pcat_ch g gR gM w2 -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N P copy_out bs K.
  Proof using Hcons Hsw HPc Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr.
    intros Hne Hfd Hv Hok Hwc HcL Hp Hpre. iIntros "Hstd #He Hr Hc #Hctx HK".
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    destruct (pif_copy_row_out l k Hrow (eq_sym Hk)) as [-> (rb & Hl1)].
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    change copy_out with (Z.of_nat 1%nat).
    iApply (cons_write N P (HPc := HPc) Hsw (pif_wD c) (pif_wD_short c) (pif_wD_sub c)
              (pif_wD_step c) l 1 rb [p] p bs K Hlt Hl1
              ltac:(apply elem_of_list_singleton; reflexivity) Hpre with "Hstd [Hr Hc]").
    { iFrame "Hctx Hinv Hr". iSplitR; [by iPureIntro |]. iExists w. iFrame "Hc".
      iPureIntro. split; [by rewrite Hp | exact Hwc]. }
    iIntros "Hstd HD". iDestruct "HD" as "(_ & _ & _ & Hr & %w2 & [%Hw2 %Hw2c] & Hc)".
    injection Hw2 as Hw2.
    iApply ("HK" $! w2 with "[%] Hstd Hr Hc"). split; [exact Hw2 | exact Hw2c].
  Qed.

  (* [ei_write_copy] *)
  Lemma pif_write_copy (fdm : fdmap) (fd : Z) (d : nat) (Sin p bs : list (bv 8))
      (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
    pif_fds fdm -∗ pif_copy d false Sin p -∗
    ((pif_fds fdm -∗ pif_copy d false Sin (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hcons Hsw HPc Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr.
    intros Hne Hfd Hfd1 Hpre. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as "(_ & Htk & #Hctx & %c & %w & [%HS %Hp] & [%Hwc %HcL] & Hr & Hc)".
    iDestruct "Hfds" as (l vs w') "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. iDestruct "HK" as "[HK _]".
    iApply (pif_copy_write fdm l vs w' d c w p bs K Hne Hfd Hv Hok Hwc HcL Hp Hpre
              with "Hstd He Hr Hc Hctx").
    iIntros (w2) "[%Hw2 %Hw2c] Hstd Hr Hc".
    iApply ("HK" with "[-Htk Hr Hc] [Htk Hr Hc]"); [pif_repack |].
    iSplitR; [done |]. iFrame "Htk Hctx". iExists c, w2. iFrame "Hr Hc". iPureIntro.
    split; [split; [exact HS | exact Hw2] | split; [exact Hw2c | exact HcL]].
  Qed.

  (* [ei_write_copy_end]: the same write, the end's shot kept *)
  Lemma pif_write_copy_end (fdm : fdmap) (fd : Z) (d : nat) (p bs : list (bv 8))
      (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
    pif_fds fdm -∗ pif_copy_end d false p -∗
    ((pif_fds fdm -∗ pif_copy_end d false (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hcons Hsw HPc Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr.
    intros Hne Hfd Hfd1 Hpre. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as "(_ & Htk & #Hctx & %c & %w & %Hp & ([%Hwc %HcL] & Hr & Hc) & #Heof)".
    iDestruct "Hfds" as (l vs w') "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. iDestruct "HK" as "[HK _]".
    iApply (pif_copy_write fdm l vs w' d c w p bs K Hne Hfd Hv Hok Hwc HcL Hp Hpre
              with "Hstd He Hr Hc Hctx").
    iIntros (w2) "[%Hw2 %Hw2c] Hstd Hr Hc".
    iApply ("HK" with "[-Htk Hr Hc] [Htk Hr Hc]"); [pif_repack |].
    iSplitR; [done |]. iFrame "Htk Hctx". iExists c, w2. iFrame "Hr Hc Heof". iPureIntro.
    split; [exact Hw2 | split; [exact Hw2c | exact HcL]].
  Qed.

  (* the open laws: the scope is empty (and no device is a DIn) *)
  Lemma pif_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path content : list (bv 8)) (K : Z -> iProp Σ) :
    path ∈ paths -> files path = Some content ->
    pif_fds fdm -∗ pif_filesr files paths -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
        (∀ d : nat, ⌜forall fd', fdm !! fd' <> Some d⌝ -∗
           pif_fds (<[fd := d]> fdm) ∗ False) -∗
        pif_filesr files paths -∗ K fd)
     ∧ (pif_fds fdm -∗ pif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ pif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path 0 K.
  Proof using .
    intros Hp _. iIntros "_ Hfiles _". rewrite /pif_filesr. iDestruct "Hfiles" as %->.
    by apply elem_of_nil in Hp.
  Qed.

  Lemma pif_open_absent (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    pif_fds fdm -∗ pif_filesr files paths -∗
    ((pif_fds fdm -∗ pif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ pif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using .
    intros Hp _ _. iIntros "_ Hfiles _". rewrite /pif_filesr. iDestruct "Hfiles" as %->.
    by apply elem_of_nil in Hp.
  Qed.

  (* the descriptors after a device's last descriptor closed: the slot
     shut, the token home to the pool, the exit payoff as the caller
     re-establishes it at the smaller registry *)
  Lemma pif_fds_after_close (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (k : nat) (d : nat) (kd : pdev) :
    pif_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> ~ fd_shared fdm (Z.of_nat k) d ->
    vs !! d = Some kd ->
    UserFd.ustd γfd (<[k := FdClosed]> l) -∗ pif_kpay (delete d vs) -∗
    own γreg (pif_pool (dom vs) w) -∗
    ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) -∗ pif_tok d (1/2) kd -∗ pif_env -∗
    pif_fds (delete (Z.of_nat k) fdm).
  Proof using .
    intros Hok Hfd Hns Hv. iIntros "Hstd Hkp Hpool Htoks Htk #He".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (pif_tok d 1 kd) with "[Htk Htk']" as "Htk".
    { rewrite pif_tok_halves. iFrame "Htk Htk'". }
    assert (Hdd : d ∈ dom vs) by (apply elem_of_dom; by eexists).
    iDestruct (pif_pool_give vs w d kd Hdd with "Hpool Htk") as "Hpool".
    iExists (<[k := FdClosed]> l), (delete d vs), _.
    iFrame "Hstd Hkp Hpool Htoks He". iPureIntro.
    apply pif_ok_close; [exact Hok | exact Hfd | exact Hns].
  Qed.

  (* the close of one of the copy device's two slots, by its row *)
  Lemma pif_close_copy_slot (l : list fdstate) (k : nat) (K : Z -> iProp Σ) :
    pif_row (Some PDCopy) (Z.of_nat k) l ->
    pipe_reg γp -∗ UserFd.ustd γfd l -∗
    (UserFd.ustd γfd (<[k := FdClosed]> l) -∗ K 0) -∗
    cl_obl N P (Z.of_nat k) K.
  Proof using Hsc.
    intros Hrow. iIntros "#Hreg Hstd HK".
    destruct Hrow as [[Hk (wb & Hl)] | [Hk (rb & Hl)]].
    - assert (k = 0%nat) as -> by (unfold copy_in in Hk; lia).
      iApply (pipe_close N P Hsc γp l 0 true wb K ltac:(unfold NSTD; lia) Hl with "Hreg Hstd").
      iExact "HK".
    - assert (k = 1%nat) as -> by (unfold copy_out in Hk; lia).
      iApply (file_close_std N P Hsc 1 l _ K ltac:(unfold NSTD; lia) Hl ltac:(discriminate)
                Logic.I with "Hstd").
      iExact "HK".
  Qed.

  (* the last close of the write end at its END while the LEFT wand is
     held: the wand is paid under the close's WP, at the invariant *)
  Lemma pif_close_wr_paid (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (k : nat) (d : nat) (rb : bool)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    pif_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> ~ fd_shared fdm (Z.of_nat k) d ->
    vs !! d = Some PDWr -> (k < NSTD)%nat ->
    l !! k = Some (FdOpen rb true (FdPipe γp)) ->
    UserFd.ustd γfd l -∗ pif_exit_k_left -∗ own γreg (pif_pool (dom vs) w) -∗
    ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) -∗ pif_tok d (1/2) PDWr -∗ pif_env -∗
    pif_filesr files paths -∗ (pipe_out pn L [] ∨ pipe_halt pn) -∗
    ((pif_fds (delete (Z.of_nat k) fdm) -∗ pif_filesr files paths -∗ K 0)
     ∧ (∀ y, pif_taint (dom fdm ∖ {[Z.of_nat k]}) -∗ K y)) -∗
    cl_obl N P (Z.of_nat k) K.
  Proof using Hsc.
    intros Hok Hfd Hns Hv Hlt Hrow.
    iIntros "Hstd Hkl Hpool Htoks Htk #He Hfiles Hd HK".
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iPoseProof (pipe_reg_of_inv pn γp L with "Hinv") as "#Hreg".
    iIntros (h m avail) "%Ha0 Hcode Hrun Hcont".
    iApply fupd_wp.
    iMod (pif_lexit_of_lend with "Hinv Hd") as "Hle".
    iDestruct ("Hkl" with "[Hle]") as "Hpay"; [by iRight |].
    iModIntro.
    iPoseProof (pipe_close N P Hsc γp l k rb true K Hlt Hrow
                  with "Hreg Hstd [HK Hpay Hpool Htoks Htk Hfiles]") as "Hcl".
    { iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDWr Hok Hfd Hns Hv
                with "Hstd [Hpay] Hpool Htoks Htk He").
      iApply (pif_kpay_of_pay with "Hpay"). }
    iApply ("Hcl" $! h m avail with "[%] Hcode Hrun Hcont"). exact Ha0.
  Qed.

  (* [ei_close] of a device's last descriptor: a pipe end by the protocol's
     registration ([UkPipeDev.pipe_close]), a console slot by
     [UkFileDev.file_close_std], the token home to the pool, the device
     dropped -- a copy device at its END pays the exit wand first, and open
     it is refuted ([pif_close_open]); the write end at its end (drained,
     or halted) pays the LEFT wand first, and open it is refuted
     ([pif_close_open_w]): the close rule's [drained_at_close] fact *)
  Lemma pif_close (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> drained_at_close x ->
    pif_fds fdm -∗ pif_filesr files paths -∗ pif_dev d x -∗
    ((pif_fds (delete fd fdm) -∗ pif_filesr files paths -∗ K 0)
     ∧ (∀ y, pif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns Hdc. iIntros "Hfds Hfiles Hd HK".
    iDestruct (pif_dev_tok with "Hd") as (kd) "(%Hkd & Htk & Hback)".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (pif_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iPoseProof (pipe_reg_of_inv pn γp L with "Hinv") as "#Hreg".
    destruct kd.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDPCons Hok Hfd Hns Hv
                with "Hstd [Hkp] Hpool Htoks Htk He").
      iApply (pif_kpay_delete vs d PDPCons Hv ltac:(discriminate) ltac:(discriminate) with "Hkp").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDCons Hok Hfd Hns Hv
                with "Hstd [Hkp] Hpool Htoks Htk He").
      iApply (pif_kpay_delete vs d PDCons Hv ltac:(discriminate) ltac:(discriminate) with "Hkp").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDMute Hok Hfd Hns Hv
                with "Hstd [Hkp] Hpool Htoks Htk He").
      iApply (pif_kpay_delete vs d PDMute Hv ltac:(discriminate) ltac:(discriminate) with "Hkp").
    - (* the write end: the copy wand or the payload stay; the LEFT wand is
         paid at a drained or halted end, and open it is refuted *)
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iDestruct "Hkp" as "[Hcp | [[%Hreg Hkl] | Hpay]]".
      + iApply (pipe_close N P Hsc γp l k rb true K Hlt Hrow with "Hreg Hstd").
        iIntros "Hstd". iDestruct "HK" as "[HK _]".
        iApply ("HK" with "[-Hfiles] Hfiles").
        iApply (pif_fds_after_close fdm l vs w k d PDWr Hok Hfd Hns Hv
                  with "Hstd [Hcp] Hpool Htoks Htk He").
        iApply (pif_kpay_delete_wr vs d Hv with "[Hcp]"). by iLeft.
      + iDestruct ("Hback" with "Htk") as "Hd".
        destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd;
          [exfalso; destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate
          | | exfalso; exact Hkd | | exfalso; exact Hkd | exfalso; discriminate Hkd
          | exfalso; discriminate Hkd | exfalso; discriminate Hkd
          | exfalso; discriminate Hkd | exfalso; exact Hkd].
        * (* owing [S]: drained at [S = []], open otherwise *)
          iDestruct "Hd" as "[Htk Hpo]". iDestruct "Hpo" as (S) "[%Halts Hpo]". subst alts.
          destruct (decide (S = [])) as [-> | HS]; last first.
          { iApply (pif_close_open_w fdm l vs w (Z.of_nat k) d (DOutH [S]) files paths K
                      Hfd Hns Hv
                      ltac:(simpl; intros Hin; apply elem_of_list_singleton in Hin;
                            exact (HS (eq_sym Hin)))
                      Hdc Hok with "Hstd Hkl Hpool Htoks He Hfiles [Htk Hpo] HK").
            simpl. iFrame "Htk". iExists S. iFrame "Hpo". by iPureIntro. }
          iApply (pif_close_wr_paid fdm l vs w k d rb files paths K Hok Hfd Hns Hv Hlt Hrow
                    with "Hstd Hkl Hpool Htoks Htk He Hfiles [Hpo] HK").
          by iLeft.
        * (* halted: the reader's shot pays the wand *)
          iDestruct "Hd" as "[Htk Hh]".
          iApply (pif_close_wr_paid fdm l vs w k d rb files paths K Hok Hfd Hns Hv Hlt Hrow
                    with "Hstd Hkl Hpool Htoks Htk He Hfiles [Hh] HK").
          by iRight.
      + iApply (pipe_close N P Hsc γp l k rb true K Hlt Hrow with "Hreg Hstd").
        iIntros "Hstd". iDestruct "HK" as "[HK _]".
        iApply ("HK" with "[-Hfiles] Hfiles").
        iApply (pif_fds_after_close fdm l vs w k d PDWr Hok Hfd Hns Hv
                  with "Hstd [Hpay] Hpool Htoks Htk He").
        iApply (pif_kpay_of_pay with "Hpay").
    - destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k true wb K Hlt Hrow with "Hreg Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDRd Hok Hfd Hns Hv
                with "Hstd [Hkp] Hpool Htoks Htk He").
      iApply (pif_kpay_delete vs d PDRd Hv ltac:(discriminate) ltac:(discriminate) with "Hkp").
    - (* the copy device *)
      iDestruct ("Hback" with "Htk") as "Hd".
      iDestruct "Hkp" as "[[%Hreg Hk] | Hrest]"; last first.
      { (* the exit already paid, or the LEFT process's: the device goes *)
        iDestruct (pif_dev_tok with "Hd") as (kd') "(%Hkd' & Htk & _)".
        destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd, Hkd';
          [exfalso; destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate
          | exfalso; discriminate Hkd | exfalso; exact Hkd | exfalso; discriminate Hkd
          | exfalso; exact Hkd | exfalso; discriminate Hkd | exfalso; discriminate Hkd
          | | | exfalso; exact Hkd]; subst kd';
          (iApply (pif_close_copy_slot l k K Hrow with "Hreg Hstd");
           iIntros "Hstd"; iDestruct "HK" as "[HK _]";
           iApply ("HK" with "[-Hfiles] Hfiles");
           iApply (pif_fds_after_close fdm l vs w k d PDCopy Hok Hfd Hns Hv
                     with "Hstd [Hrest] Hpool Htoks Htk He");
           iApply (pif_kpay_delete_copy vs d Hv with "Hrest")). }
      destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd;
        [exfalso; destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate
        | exfalso; discriminate Hkd | exfalso; exact Hkd | exfalso; discriminate Hkd
        | exfalso; exact Hkd | exfalso; discriminate Hkd | exfalso; discriminate Hkd
        | | | exfalso; exact Hkd].
      + (* open: refuted, [pif_close_open] *)
        iApply (pif_close_open fdm l vs w (Z.of_nat k) d (DCopy h Sc p) files paths K Hfd Hns Hv
                  ltac:(simpl; tauto) Hdc Hok with "Hstd Hk Hpool Htoks He Hfiles Hd HK").
      + destruct (decide (p = [])) as [-> | Hp]; last first.
        { iApply (pif_close_open fdm l vs w (Z.of_nat k) d (DCopyEnd h p) files paths K Hfd Hns Hv
                    ltac:(simpl; exact Hp) Hdc Hok with "Hstd Hk Hpool Htoks He Hfiles Hd HK"). }
        (* the END: the wand is paid at the close *)
        iDestruct (pif_copy_end_cend with "Hd") as "[Htk Hce]".
        iDestruct ("Hk" with "[Hce]") as "Hpay"; [by iRight |].
        iApply (pif_close_copy_slot l k K Hrow with "Hreg Hstd").
        iIntros "Hstd". iDestruct "HK" as "[HK _]".
        iApply ("HK" with "[-Hfiles] Hfiles").
        iApply (pif_fds_after_close fdm l vs w k d PDCopy Hok Hfd Hns Hv
                  with "Hstd [Hpay] Hpool Htoks Htk He").
        iApply (pif_kpay_of_pay with "Hpay").
  Qed.

  (* ...of a shared one: the device stays *)
  Lemma pif_close_shared (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> fd_shared fdm fd d ->
    pif_fds fdm -∗
    ((pif_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, pif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hsh. iIntros "Hfds HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hkp & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iPoseProof (pipe_reg_of_inv pn γp L with "Hinv") as "#Hreg".
    iAssert (UserFd.ustd γfd (<[k := FdClosed]> l) -∗ K 0)%I with "[-Hstd]" as "HK".
    { iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
      iExists (<[k := FdClosed]> l), vs, w. iFrame "Hstd Hkp Hpool Htoks He".
      iPureIntro. exact (pif_ok_close_shared fdm l vs k d Hok Hfd Hsh). }
    destruct kd.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd HK").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd HK").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd HK").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k rb true K Hlt Hrow with "Hreg Hstd HK").
    - destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k true wb K Hlt Hrow with "Hreg Hstd HK").
    - iApply (pif_close_copy_slot l k K Hrow with "Hreg Hstd HK").
  Qed.

  (* [ei_exit]: the payload, or the wand at the drained copy device -- the
     registered copy device is bound (the registry's third clause), its
     resource among the drained devices, and drained it is its END *)
  Lemma pif_exit (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    (forall fd d, fdm !! fd = Some d -> d ∈ ds) ->
    pif_fds fdm -∗ pif_filesr files paths -∗ ([∗ set] d ∈ ds, pif_dev d (dv d)) -∗
    ex_obl N P s.
  Proof using HNc Hse.
    intros Hdr Hds. iIntros "Hfds _ Hdev".
    iDestruct "Hfds" as (l vs w) "(_ & Hkp & %Hok & _ & Htoks & #He)".
    iDestruct "Hkp" as "[[%Hreg Hk] | [[%Hreg Hkl] | Hpay]]".
    - destruct Hreg as [d Hv].
      destruct Hok as (_ & _ & H3).
      destruct (proj1 (H3 d) (elem_of_dom_2 _ _ _ Hv)) as [fd Hfd].
      pose proof (Hds fd d Hfd) as Hin. pose proof (Hdr d Hin) as Hdrd.
      iDestruct (big_sepS_elem_of _ _ _ Hin with "Hdev") as "Hd".
      iDestruct (pif_dev_tok with "Hd") as (kd) "(%Hkd & Htk & Hback)".
      iDestruct (pif_toks_agree vs d PDCopy with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst kd. iDestruct ("Hback" with "Htk") as "Hd".
      remember (dv d) as x eqn:Hx.
      destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd;
        [exfalso; destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate
        | exfalso; discriminate Hkd | exfalso; exact Hkd | exfalso; discriminate Hkd
        | exfalso; exact Hkd | exfalso; discriminate Hkd | exfalso; discriminate Hkd
        | | | exfalso; exact Hkd].
      + simpl in Hdrd. destruct Hdrd.
      + simpl in Hdrd. subst p.
        iDestruct (pif_copy_end_cend with "Hd") as "[_ Hce]".
        iApply (fh_exit_pay N P Hse). iApply "Hk". by iRight.
    - (* the LEFT wand: the registered write end is among the drained
         devices, at the line's end or halted; the wand is paid at the
         invariant, under the exit hole's WP *)
      destruct Hreg as [d Hv].
      destruct Hok as (_ & _ & H3).
      destruct (proj1 (H3 d) (elem_of_dom_2 _ _ _ Hv)) as [fd Hfd].
      pose proof (Hds fd d Hfd) as Hin. pose proof (Hdr d Hin) as Hdrd.
      iDestruct (big_sepS_elem_of _ _ _ Hin with "Hdev") as "Hd".
      iDestruct (pif_dev_tok with "Hd") as (kd) "(%Hkd & Htk & Hback)".
      iDestruct (pif_toks_agree vs d PDWr with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst kd. iDestruct ("Hback" with "Htk") as "Hd".
      iPoseProof (pif_env_inv with "He") as "#Hinv".
      iAssert (pipe_out pn L [] ∨ pipe_halt pn)%I with "[Hd]" as "Hd".
      { remember (dv d) as x eqn:Hx.
        destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p |]; simpl in Hkd;
          [exfalso; destruct Hkd as [Hkd | [Hkd | Hkd]]; discriminate
          | | exfalso; exact Hkd | | exfalso; exact Hkd | exfalso; discriminate Hkd
          | exfalso; discriminate Hkd | exfalso; discriminate Hkd
          | exfalso; discriminate Hkd | exfalso; exact Hkd].
        - simpl in Hdrd. iDestruct "Hd" as "[_ Hpo]". iDestruct "Hpo" as (S) "[%Halts Hpo]".
          subst alts. apply elem_of_list_singleton in Hdrd. subst S. by iLeft.
        - iDestruct "Hd" as "[_ Hh]". by iRight. }
      iIntros (h m avail) "%Hst Hcode Hrun".
      iApply fupd_wp.
      iMod (pif_lexit_of_lend with "Hinv Hd") as "Hle".
      iDestruct ("Hkl" with "[Hle]") as "Hpay"; [by iRight |].
      iModIntro.
      iPoseProof (fh_exit_pay N P Hse s with "Hpay") as "Hex".
      iApply ("Hex" $! h m avail with "[%] Hcode Hrun"). exact Hst.
    - iApply (fh_exit_pay N P Hse with "Hpay").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE RECORD                                                          *)
  (* ------------------------------------------------------------------- *)

  Definition pipe_iface : ep_iface N P.
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr
              Hhalt_long Hnil_ro.
    refine (MkEI N P pif_fds pif_out pif_outh pif_halt (fun _ _ => False%I)
              (fun _ _ => False%I) pif_in pif_in_end
              pif_copy pif_copy_end (fun _ => False%I)
              pif_filesr pif_taint pif_taint_pays
              pif_write pif_write_h _ pif_write_halt pif_write_nil
              _ pif_read_e pif_read_end pif_read_copy pif_read_copy_end
              pif_write_copy _ pif_write_copy_end _ _ pif_open pif_open_absent
              pif_close pif_close_shared pif_exit).
    - (* [ei_write_m]: no file *)
      intros. iIntros "_ []".
    - (* [ei_read] at DIn: a pipe's read end may end early *)
      intros. iIntros "_ []".
    (* the copy device at a sink that may halt ([h = true]): a later lane *)
    - intros. iIntros "_ (%Hh & _)". discriminate Hh.
    - intros. iIntros "_ (%Hh & _)". discriminate Hh.
    - intros. iIntros "_ []".
  Defined.

  Lemma pif_ei_fds : ei_fds N P pipe_iface = pif_fds.
  Proof. reflexivity. Qed.
  Lemma pif_ei_files : ei_files N P pipe_iface = pif_filesr.
  Proof. reflexivity. Qed.
  Lemma pif_dev_of (d : nat) (x : dspec) : dev_of N P pipe_iface d x = pif_dev d x.
  Proof. by destruct x. Qed.

  (* =================================================================== *)
  (*  2.  END TO END: the two processes of `echo ... | cat`                *)
  (* =================================================================== *)

  (* THE RIGHT PROCESS, at the copy device: fds 0 and 1 the copy device
     (the pipe's read end and the popen console) owing the line, fd 2 a
     console slot nothing is written on *)
  Theorem cat_copy_paid (files : list (bv 8) -> option (list (bv 8))) :
    env_res N P pipe_iface (copy_env (DCopy false L []) [[]] files []) {[0%nat; 1%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"]).
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr
              Hhalt_long Hnil_ro.
    iIntros "H".
    iApply (tree_pay_of_conforms N P pipe_iface _ _ _
              (cat_copy_conforms false L [[]] files []
                 ltac:(apply elem_of_list_singleton; reflexivity)
                 ltac:(intros Hf; discriminate Hf))
              (cat_tree_safe _ _) with "H").
  Qed.

  (* THE LEFT PROCESS: fd 1 the write end owing the line, which may halt *)
  Theorem echo_pipe_paid (argv : list (list (bv 8))) (files : list (bv 8) -> option (list (bv 8))) :
    drop 1 argv <> [] -> L = wl_line (drop 1 argv) ->
    env_res N P pipe_iface (pipe_env (DOutH [L]) files) {[0%nat]} -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers Hyr
              Hhalt_long Hnil_ro.
    intros Hne HL. iIntros "H". rewrite HL.
    iApply (tree_pay_of_conforms N P pipe_iface _ _ _
              (echo_pipe_conforms argv files Hne) (echo_tree_safe _ _) with "H").
  Qed.

  (* ---- what the round lends cat ([UShPipeLaw.pl_RcR] and [pl_cat_fd0]):
          the ledger with fd 0 the pipe's read end and fds 1, 2 the console,
          the registry's pool with device 0 the mute console and device 1
          the copy device, the exit continuation, the protocol, the reader's
          permit at 0, the round's context WITHOUT [YR], and the family's
          two halves at 0 ---- *)
  Lemma copy_env_res (l : list fdstate) (wb rb1 rb2 : bool) (w : nat -> pdev)
      (files : list (bv 8) -> option (list (bv 8))) :
    w 0%nat = PDMute -> w 1%nat = PDCopy ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ own γreg (pif_pool ∅ w) -∗
    (pif_cend -∗ ukn_pay N (-1)) -∗
    pipe_inv pn γp L -∗ rtok pn -∗
    era_pin γ (S gen_id) v -∗ pipe_link_taint g -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    PipeBoth.wcur gR (1/2) 0%nat -∗ PipeBoth.wcur gM (1/2) 0%nat -∗
    env_res N P pipe_iface (copy_env (DCopy false L []) [[]] files []) {[0%nat; 1%nat]}.
  Proof using Heq Hkill.
    intros Hw0 Hw1 Hl0 Hl1 Hl2 HL.
    set (fdm := (<[0 := 1%nat]> (<[1 := 1%nat]> {[2 := 0%nat]}) : fdmap)).
    set (vs := (<[0%nat := PDMute]> {[1%nat := PDCopy]} : gmap nat pdev)).
    assert (Hv1 : vs !! 1%nat = Some PDCopy).
    { rewrite /vs lookup_insert_ne; [| done]. apply lookup_singleton. }
    assert (Hok : pif_ok fdm l vs).
    { split; [| split].
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- _] | (_ & [[<- _] | (_ & <- & _)])]; lia.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- <-] | (_ & [[<- <-] | (_ & <- & <-)])].
        + rewrite Hv1. simpl. left. split; [reflexivity | by exists wb].
        + rewrite Hv1. simpl. right. split; [reflexivity | by exists rb1].
        + rewrite /vs lookup_insert. simpl. split; [unfold NSTD; lia | by exists rb2].
      - intros d. rewrite /vs dom_insert_L dom_singleton_L elem_of_union !elem_of_singleton.
        split.
        + intros [-> | ->]; [exists 2 |  exists 0].
          * rewrite /fdm lookup_insert_ne; [| lia]. rewrite lookup_insert_ne; [| lia].
            apply lookup_singleton.
          * apply lookup_insert.
        + intros (fd & Hfd). revert Hfd.
          rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
          intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; [by right | by right | by left]. }
    iIntros "Hstd Hpool Hk #Hinv Hrt #Hpin #Hlt #Hblk #Hex HgR HgM".
    rewrite /env_res.
    iDestruct (pif_pool_own_take ∅ w 0%nat with "Hpool") as "[Hpool Htk0]"; [set_solver |].
    iDestruct (pif_pool_own_take ({[0%nat]} ∪ ∅) w 1%nat with "Hpool") as "[Hpool Htk1]";
      [set_solver |].
    rewrite Hw0 Hw1.
    iDestruct (pif_tok_halves with "Htk0") as "[Htk0a Htk0b]".
    iDestruct (pif_tok_halves with "Htk1") as "[Htk1a Htk1b]".
    iPoseProof (pif_env_of_inv with "Hinv") as "#He".
    iSplit.
    { iPureIntro. intros fd d. cbn [copy_env pe_fd].
      rewrite lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
      intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; set_solver. }
    iSplitL "Hstd Hk Hpool Htk0a Htk1a".
    { rewrite pif_ei_fds. iExists l, vs, w. cbn [copy_env pe_fd].
      iFrame "Hstd He". iSplitL "Hk"; [iApply (pif_kpay_cat vs 1%nat Hv1 with "Hk") |].
      iSplit; [by iPureIntro |].
      iSplitL "Hpool".
      { rewrite (pif_pool_ext (dom vs) ({[1%nat]} ∪ ({[0%nat]} ∪ ∅)) w w);
          [iExact "Hpool" | | intros; reflexivity].
        rewrite /vs dom_insert_L dom_singleton_L. set_solver. }
      rewrite /vs big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton. iFrame "Htk0a Htk1a". }
    iSplitR.
    { rewrite pif_ei_files /pif_filesr. cbn [copy_env pe_paths]. by iPureIntro. }
    rewrite /dev_res big_sepS_union; [| set_solver]. rewrite !big_sepS_singleton !pif_dev_of.
    assert (E0 : pe_dev (copy_env (DCopy false L []) [[]] files []) 0%nat = DOut [[]])
      by reflexivity.
    assert (E1 : pe_dev (copy_env (DCopy false L []) [[]] files []) 1%nat = DCopy false L [])
      by reflexivity.
    rewrite E0 E1. cbn [pif_dev]. iSplitL "Htk0b".
    - iRight. iRight. iFrame "Htk0b". by iPureIntro.
    - iSplitR; [done |]. iFrame "Htk1b".
      iSplitR. { iSplitR; [by iPureIntro |]. iFrame "Hpin Hlt Hblk". iExact "Hex". }
      iExists 0%nat, 0%nat. iSplitR; [iPureIntro; split; reflexivity |].
      iSplitR; [iPureIntro; split; lia |].
      iEval (rewrite /rtok) in "Hrt". iFrame "Hrt".
      rewrite /UShPipeCatRound.pcat_ch. simpl. iLeft. iFrame "HgR HgM".
  Qed.

  Theorem cat_copy_paid_of_round (l : list fdstate) (wb rb1 rb2 : bool) (w : nat -> pdev) :
    w 0%nat = PDMute -> w 1%nat = PDCopy ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ own γreg (pif_pool ∅ w) -∗
    (pif_cend -∗ ukn_pay N (-1)) -∗
    pipe_inv pn γp L -∗ rtok pn -∗
    era_pin γ (S gen_id) v -∗ pipe_link_taint g -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗
    PipeBoth.wcur gR (1/2) 0%nat -∗ PipeBoth.wcur gM (1/2) 0%nat -∗
    tree_pay N P (cat_tree [sb "cat"]).
  Proof using Hcons Heq Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Hyr Hhalt_long Hnil_ro.
    intros Hw0 Hw1 Hl0 Hl1 Hl2 HL.
    iIntros "Hstd Hpool Hk Hinv Hrt Hpin Hlt Hblk Hex HgR HgM".
    iApply (cat_copy_paid (fun _ => None)).
    iApply (copy_env_res l wb rb1 rb2 w (fun _ => None) Hw0 Hw1 Hl0 Hl1 Hl2 HL
              with "Hstd Hpool Hk Hinv Hrt Hpin Hlt Hblk Hex HgR HgM").
  Qed.

  (* ---- what the round lends echo ([UEchoPipe.ep_pay] at [pl_RcL]): fd 1
          the pipe's write end, the payload up front (echo's exit is paid by
          the round, not from a device: [pif_pay] stays for the left
          process), the pool with device 0 the write end, the protocol, the
          write permit at 0 with the empty lower bound ---- *)
  Lemma echo_env_res_k (l : list fdstate) (rb : bool) (w : nat -> pdev)
      (files : list (bv 8) -> option (list (bv 8))) :
    w 0%nat = PDWr ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ pif_kpay ({[0%nat := PDWr]} : gmap nat pdev) -∗
    own γreg (pif_pool ∅ w) -∗
    pipe_inv pn γp L -∗ wcur pn 0%nat -∗ pws_lb pn [] -∗
    env_res N P pipe_iface (pipe_env (DOutH [L]) files) {[0%nat]}.
  Proof using Heq Hkill.
    intros Hw0 Hl1 HL.
    set (fdm := ({[1 := 0%nat]} : fdmap)).
    set (vs := ({[0%nat := PDWr]} : gmap nat pdev)).
    assert (Hok : pif_ok fdm l vs).
    { split; [| split].
      - intros fd d. rewrite /fdm lookup_singleton_Some. intros [<- _]. lia.
      - intros fd d. rewrite /fdm lookup_singleton_Some. intros [<- <-].
        rewrite /vs lookup_singleton. simpl. split; [unfold NSTD; lia | by exists rb].
      - intros d. rewrite /vs dom_singleton_L elem_of_singleton. split.
        + intros ->. exists 1. apply lookup_singleton.
        + intros (fd & Hfd). revert Hfd. rewrite /fdm lookup_singleton_Some. by intros [_ <-]. }
    iIntros "Hstd Hkp Hpool #Hinv Hw Hlb". rewrite /env_res.
    iDestruct (pif_pool_own_take ∅ w 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    rewrite Hw0. iDestruct (pif_tok_halves with "Htk") as "[Htk1 Htk2]".
    iPoseProof (pif_env_of_inv with "Hinv") as "#He".
    iSplit.
    { iPureIntro. intros fd d. cbn [pipe_env pe_fd].
      rewrite lookup_singleton_Some. intros [_ <-]. set_solver. }
    iSplitL "Hstd Hkp Hpool Htk1".
    { rewrite pif_ei_fds. iExists l, vs, w. cbn [pipe_env pe_fd].
      iFrame "Hstd Hkp He".
      iSplit; [by iPureIntro |].
      iSplitL "Hpool"; [by rewrite /vs dom_singleton_L right_id_L |].
      by rewrite /vs big_sepM_singleton. }
    iSplitR.
    { rewrite pif_ei_files /pif_filesr. cbn [pipe_env pe_paths]. by iPureIntro. }
    rewrite /dev_res big_sepS_singleton pif_dev_of.
    assert (E0 : pe_dev (pipe_env (DOutH [L]) files) 0%nat = DOutH [L]) by reflexivity.
    rewrite E0. cbn [pif_dev].
    iFrame "Htk2". iExists L. iSplitR; [by iPureIntro |].
    rewrite /pipe_out. iExists 0%nat. iFrame "Hw". rewrite take_0. iFrame "Hlb".
    iPureIntro. split; [reflexivity | exact HL].
  Qed.

  Lemma echo_env_res (l : list fdstate) (rb : bool) (w : nat -> pdev)
      (files : list (bv 8) -> option (list (bv 8))) :
    w 0%nat = PDWr ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ pif_pay -∗ own γreg (pif_pool ∅ w) -∗
    pipe_inv pn γp L -∗ wcur pn 0%nat -∗ pws_lb pn [] -∗
    env_res N P pipe_iface (pipe_env (DOutH [L]) files) {[0%nat]}.
  Proof using Heq Hkill.
    intros Hw0 Hl1 HL. iIntros "Hstd Hpay Hpool Hinv Hw Hlb".
    iApply (echo_env_res_k l rb w files Hw0 Hl1 HL with "Hstd [Hpay] Hpool Hinv Hw Hlb").
    iApply (pif_kpay_of_pay with "Hpay").
  Qed.

  Theorem echo_pipe_paid_of_round (l : list fdstate) (rb : bool) (w : nat -> pdev)
      (argv : list (list (bv 8))) :
    w 0%nat = PDWr ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    drop 1 argv <> [] -> L = wl_line (drop 1 argv) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ pif_pay -∗ own γreg (pif_pool ∅ w) -∗
    pipe_inv pn γp L -∗ wcur pn 0%nat -∗ pws_lb pn [] -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Heq Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Hyr Hhalt_long Hnil_ro.
    intros Hw0 Hl1 Hne HLw HL. iIntros "Hstd Hpay Hpool Hinv Hw Hlb".
    iApply (echo_pipe_paid argv (fun _ => None) Hne HLw).
    iApply (echo_env_res l rb w (fun _ => None) Hw0 Hl1 HL with "Hstd Hpay Hpool Hinv Hw Hlb").
  Qed.

  (* ---- ...and at the LEFT EXIT WAND (lane F): what the round's
          continuation [UEchoPipe.ep_exit Wq pn L -∗ Q (-1)] is, read here
          as a box over [(side_L pn ∗ Wq) ∗ pif_lexit] (the two are the same
          proposition unfolded), with the frame [side_L pn ∗ Wq] lent up
          front and captured in the wand -- no payload before the child
          runs ---- *)
  Theorem echo_pipe_paid_of_round' (Wq : iProp Σ) (l : list fdstate) (rb : bool)
      (w : nat -> pdev) (argv : list (list (bv 8))) :
    w 0%nat = PDWr ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    drop 1 argv <> [] -> L = wl_line (drop 1 argv) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    □ ((side_L pn ∗ Wq) ∗ pif_lexit -∗ ukn_pay N (-1)) -∗
    side_L pn ∗ Wq -∗
    UserFd.ustd γfd l -∗ own γreg (pif_pool ∅ w) -∗
    pipe_inv pn γp L -∗ wcur pn 0%nat -∗ pws_lb pn [] -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Heq Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Hyr Hhalt_long Hnil_ro.
    intros Hw0 Hl1 Hne HLw HL. iIntros "#Hq Hfr Hstd Hpool Hinv Hw Hlb".
    iApply (echo_pipe_paid argv (fun _ => None) Hne HLw).
    iApply (echo_env_res_k l rb w (fun _ => None) Hw0 Hl1 HL
              with "Hstd [Hfr] Hpool Hinv Hw Hlb").
    iApply (pif_kpay_left _ 0%nat (lookup_singleton _ _)).
    iApply pif_exit_k_left_of. iIntros "Hle". iApply "Hq". iFrame "Hfr Hle".
  Qed.

End UkPipeIface.

(* ===================================================================== *)
(*  3.  THE VACUITY WITNESSES: every hypothesis-free law at cat's and at  *)
(*      echo's instance, through [UkStub]'s stub laws                     *)
(* ===================================================================== *)

Section UkPipeIfaceCat.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pifRegG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context (g : pipe_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = echo_taint (pgn_cl g)).
  Context (v : era_pins) (I L : list (bv 8)).
  Context (gL gR gM : gname) (XL YR : iProp Σ).
  Context {XL_tl : Timeless XL} {YR_tl : Timeless YR} {YR_pers : Persistent YR}.
  Context (Hnd : Forall nodollar L).
  Context (Hwit2 : forall sel : list bool,
             sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel).
  Context (Hwit1 : forall sel : list bool,
             count_true sel = 0%nat -> (length sel <= length L)%nat ->
             pblk2_wit I L sel).
  Context (pn : pnames) (γp : pipe_names).
  Context (Hyr : pws_lb pn (take 1%nat L) ⊢ YR).
  Context (N : uk_names Σ) `{!ukn_const N}.
  Context (γreg : gname).

  Local Instance pif_cat_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.
  Local Instance pif_echo_code_persistent : Persistent (up_code (echo_prog N)).
  Proof using . simpl. apply _. Qed.

  Definition pif_write_cat :=
    pif_write g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
      (YR_pers := YR_pers) Hnd Hwit2 Hwit1 pn γp N (cat_prog N) (cat_stub_write N) γreg.
  Definition pif_write_h_cat :=
    pif_write_h g Hkill L gR gM pn γp N (cat_prog N) (cat_stub_write N) γreg.
  Definition pif_read_e_cat :=
    pif_read_e g Hkill L gR gM pn γp N (cat_prog N) (cat_stub_read N) γreg.
  Definition pif_read_end_cat :=
    pif_read_end g Hkill L gR gM pn γp N (cat_prog N) (cat_stub_read N) γreg.
  Definition pif_read_copy_cat :=
    pif_read_copy g Hkill v I L gL gR gM XL YR pn γp N (cat_prog N) (cat_stub_read N) γreg.
  Definition pif_read_copy_end_cat :=
    pif_read_copy_end g Hkill v I L gL gR gM XL YR pn γp N (cat_prog N) (cat_stub_read N) γreg.
  Definition pif_write_copy_cat :=
    pif_write_copy g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
      (YR_pers := YR_pers) Hnd Hwit2 Hwit1 pn γp Hyr N (cat_prog N) (cat_stub_write N) γreg.
  Definition pif_write_copy_end_cat :=
    pif_write_copy_end g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
      (YR_pers := YR_pers) Hnd Hwit2 Hwit1 pn γp Hyr N (cat_prog N) (cat_stub_write N) γreg.
  Definition pif_close_shared_cat :=
    pif_close_shared g L gR gM pn γp N (cat_prog N) (cat_stub_close N) γreg.
  Definition pif_exit_cat :=
    pif_exit g v I L gL gR gM XL YR pn γp N (cat_prog N) (cat_stub_exit N) γreg.
  Definition pif_taint_pays_cat :=
    pif_taint_pays g N (cat_prog N) (cat_stub_read N) (cat_stub_write N) (cat_stub_open N)
      (cat_stub_close N) (cat_stub_exit N).

  (* ...and at echo's, whose five stubs are real since lane leaf-pipedev *)
  Definition pif_write_echo :=
    pif_write g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
      (YR_pers := YR_pers) Hnd Hwit2 Hwit1 pn γp N (echo_prog N) (echo_stub_write N) γreg.
  Definition pif_write_h_echo :=
    pif_write_h g Hkill L gR gM pn γp N (echo_prog N) (echo_stub_write N) γreg.
  Definition pif_read_e_echo :=
    pif_read_e g Hkill L gR gM pn γp N (echo_prog N) (echo_stub_read N) γreg.
  Definition pif_close_shared_echo :=
    pif_close_shared g L gR gM pn γp N (echo_prog N) (echo_stub_close N) γreg.
  Definition pif_exit_echo :=
    pif_exit g v I L gL gR gM XL YR pn γp N (echo_prog N) (echo_stub_exit N) γreg.
  Definition pif_taint_pays_echo :=
    pif_taint_pays g N (echo_prog N) (echo_stub_read N) (echo_stub_write N) (echo_stub_open N)
      (echo_stub_close N) (echo_stub_exit N).
End UkPipeIfaceCat.
