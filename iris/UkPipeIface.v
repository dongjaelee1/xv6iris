(* ===================================================================== *)
(* UkPipeIface.v -- THE PIPELINE APPLICATION'S ENDPOINT INTERFACE: one     *)
(* [UkHandler.ep_iface] from the pipeline's console ([UkPipeConsOut]: the *)
(* popen device of the two-writer round, and the generic device at the   *)
(* single-writer rounds) and a pipe's two ends ([UkPipeDev]), for the two *)
(* processes of `echo ... | cat`, paid end to end through the once-glue   *)
(* [UkHandler.tree_pay_of_conforms] (program-specs SS3.4b-SS3.4e).        *)
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
(*   [PDWr]     the pipe's WRITE end at a standard slot ([FdPipe gp]),    *)
(*              [UkPipeDev.pipe_out] / [pipe_halt] (DOutH / DHalt);        *)
(*   [PDRd]     the pipe's READ end at a standard slot,                   *)
(*              [UkPipeDev.pipe_in] (DIn and DInE) and [pipe_in_eof] at   *)
(*              the line's end (DInEnd).                                  *)
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
(* WHAT IS PROVED: the console write at both console kinds, the pipe     *)
(* write (count, halt, taint), the halted write, every zero-length write *)
(* but one, the pipe read at DIn / DInE / DInEnd but for the early end   *)
(* of file, the close of any descriptor (a pipe end by the protocol's    *)
(* registration, a console slot by [UkFileDev.file_close_std]; last      *)
(* descriptor or shared), the exit, the open laws (vacuous), and         *)
(* [ei_taint_pays] from the generic free handler [UkFreeHandler] at      *)
(* [echo_taint].                                                          *)
(*                                                                        *)
(* WHAT IS NOT, as section hypotheses at the narrowest refused case:      *)
(*                                                                        *)
(*   [Heof_short]   an end of file at the read end while the line still  *)
(*             owes bytes.  [UkPipeDev.pipe_read] (line 861) hands       *)
(*             [pipe_in_eof pn L S] at ANY [S] (its finding 2); the      *)
(*             tree layer can continue only at the taint, and the short  *)
(*             round is refuted at sh, from the writer's payload          *)
(*             ([PipeProto.pipe_round_reading]), never at the reader.    *)
(*             Design SS3.4e: cat at the pipeline is BLOCKED at the pure  *)
(*             layer until the coupled device kind is ruled; the right   *)
(*             process's theorem is therefore stated at [DIn L].          *)
(*   [Hhalt_long]   a write of 2^31 bytes or more at a halted write end:  *)
(*             [UkPipeDev.pipe_write_halt] (line 672) takes the count as  *)
(*             a C int.                                                  *)
(*   [Hnil_ro]  a zero-length write at the read end open read-only:      *)
(*             [UkPipeDev.pipe_write_nil] (line 717) needs a writable    *)
(*             row; the kernel answers -1 there and no leaf says so.     *)
(*                                                                        *)
(* THE EXIT PAYLOAD is [pif_pay], held up front in [ei_fds] exactly as     *)
(* [UkFileIface] holds [ukn_pay N (-1)] (design SS3.4e, lane A landed the *)
(* exit law's shape, the wand form is not yet in); it is ONE named place. *)
(* At the round the payload is assembled at the END from the reader's    *)
(* EOF shot and both cursors at one index ([UShPipeLaw.pl_Cend]) or the  *)
(* writer's [pipe_payL] with its side token -- a tie between two devices *)
(* the interface's exit cannot express yet.  The [_of_round] forms take  *)
(* [pif_pay] and [YR] as inputs beside what [pl_RcR] / [ep_frame] hold.   *)
(*                                                                        *)
(* THE COPY DEVICE (design SS3.4f, landed in [UkHandler] after this file  *)
(* was cut) is the follow-up: one number on both of cat's descriptors,   *)
(* binding [PDRd]'s read end and [PDPCons]'s console into one [ei_copy]   *)
(* resource, which is where [YR] at the first byte and the early end of  *)
(* file are resolved.  Here its three fields are [False] with vacuous    *)
(* laws, as [UkFileIface] has them.                                       *)
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
Inductive pdev := PDPCons | PDCons | PDWr | PDRd.

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
     slot *)
  Definition pif_row (ov : option pdev) (fd : Z) (l : list fdstate) : Prop :=
    match ov with
    | Some PDPCons | Some PDCons =>
        fd < Z.of_nat NSTD
        /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdDevice CONSOLE))
    | Some PDWr =>
        fd < Z.of_nat NSTD
        /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdPipe γp))
    | Some PDRd =>
        fd < Z.of_nat NSTD
        /\ exists wb, l !! Z.to_nat fd = Some (FdOpen true wb (FdPipe γp))
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
    destruct ov as [[| | |] |]; simpl; intros H; [| | | | destruct H];
      destruct H as (Hlt & b & Hl); (split; [exact Hlt |]);
      eexists; (split; [exact Hl | discriminate]).
  Qed.

  (* a row survives a change of another slot *)
  Lemma pif_row_ne (ov : option pdev) (fd : Z) (l : list fdstate) (k : nat) (st : fdstate) :
    Z.to_nat fd <> k -> pif_row ov fd l -> pif_row ov fd (<[k := st]> l).
  Proof.
    intros Hne. destruct ov as [[| | |] |]; simpl; intros H; [| | | | destruct H];
      destruct H as (Hlt & b & Hl); (split; [exact Hlt |]); exists b;
      (rewrite list_lookup_insert_ne; [exact Hl | exact (not_eq_sym Hne)]).
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
    (UserFd.ustd γfd l ∗ pif_pay ∗ ⌜pif_ok fdm l vs⌝
     ∗ own γreg (pif_pool (dom vs) w)
     ∗ ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x)
     ∗ pif_env)%I.

  Definition pif_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (vs : gmap nat pdev) (w : nat -> pdev), pif_fds_at fdm l vs w)%I.

  (* the console: the popen device of the open round, or the generic one *)
  Definition pif_out (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    ((pif_tok d (1/2) PDPCons ∗ pcons2 alts) ∨ (pif_tok d (1/2) PDCons ∗ pcons1 alts))%I.

  (* the pipe's write end owing one alternative, and halted *)
  Definition pif_outh (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    (pif_tok d (1/2) PDWr ∗ ∃ S : list (bv 8), ⌜alts = [S]⌝ ∗ pipe_out pn L S)%I.
  Definition pif_halt (d : nat) : iProp Σ :=
    (pif_tok d (1/2) PDWr ∗ pipe_halt pn)%I.

  (* the pipe's read end: DIn and DInE are the same resource, DInEnd is the
     end of file at the line's end *)
  Definition pif_in (d : nat) (S : list (bv 8)) : iProp Σ :=
    (pif_tok d (1/2) PDRd ∗ pipe_in pn L S)%I.
  Definition pif_in_end (d : nat) : iProp Σ :=
    (pif_tok d (1/2) PDRd ∗ pipe_in_eof pn L [])%I.

  Definition pif_dev (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DOut alts => pif_out d alts | DOutH alts => pif_outh d alts | DOutM _ => False
    | DHalt => pif_halt d | DIn Sin => pif_in d Sin | DInE Sin => pif_in d Sin
    | DInEnd => pif_in_end d
    | DCopy _ _ _ => False | DCopyEnd _ _ => False | DCopyHalt => False
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
    app_taint -∗ UserFd.ustd γfd l -∗ pif_pay -∗ pif_env -∗ pif_taint (dom fdm).
  Proof using Hkill.
    intros Hok. iIntros "#Ht Hstd Hpay #He". rewrite /pif_env.
    iDestruct "He" as "(#Hk & #Hs & _)".
    iEval (rewrite Hkill) in "Ht".
    rewrite /pif_taint /fh_taint /pif_pay. iFrame "Ht Hk Hs Hpay".
    iExists l, ∅. iFrame "Hstd". iSplit; [| by rewrite big_sepM_empty].
    iPureIntro. intros fd Hfd. apply elem_of_dom in Hfd as [d Hd].
    destruct Hok as (H1 & H2 & _). pose proof (H1 fd d Hd) as H0.
    destruct (pif_row_open _ _ _ (H2 fd d Hd)) as (Hlt & st & Hl & Hne).
    split; [unfold NSTD, NOFILE in *; lia |]. left. split; [exact Hlt |].
    exists st. split; [exact Hl | exact Hne].
  Qed.

  (* the token of a device, whatever its state *)
  Lemma pif_dev_tok (d : nat) (x : dspec) :
    pif_dev d x -∗ ∃ kd : pdev, pif_tok d (1/2) kd ∗ (pif_tok d (1/2) kd -∗ pif_dev d x).
  Proof using .
    destruct x as [alts | alts | cs | | Sin | Sin | | h S p | h p |]; simpl;
      [| | | | | | | iIntros "[]" | iIntros "[]" | iIntros "[]"].
    - iIntros "[[Htk Hd] | [Htk Hd]]".
      + iExists PDPCons. iFrame "Htk". iIntros "Htk". iLeft. iFrame.
      + iExists PDCons. iFrame "Htk". iIntros "Htk". iRight. iFrame.
    - iIntros "[Htk Hd]". iExists PDWr. iFrame "Htk". iIntros "Htk". iFrame.
    - iIntros "[]".
    - iIntros "[Htk Hd]". iExists PDWr. iFrame "Htk". iIntros "Htk". iFrame.
    - iIntros "[Htk Hd]". iExists PDRd. iFrame "Htk". iIntros "Htk". iFrame.
    - iIntros "[Htk Hd]". iExists PDRd. iFrame "Htk". iIntros "Htk". iFrame.
    - iIntros "[Htk Hd]". iExists PDRd. iFrame "Htk". iIntros "Htk". iFrame.
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

  (* ------------------------------------------------------------------- *)
  (*  THE FIELDS THE KERNEL REFUSES (the header's list)                   *)
  (* ------------------------------------------------------------------- *)

  Hypothesis Heof_short : forall (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (d : nat) (fd : nat) (S : list (bv 8)) (K : rd_ans -> iProp Σ),
    fdm !! Z.of_nat fd = Some d -> vs !! d = Some PDRd -> S <> [] ->
    pif_fds_at fdm l vs w -∗ pif_tok d (1/2) PDRd -∗ pipe_in_eof pn L S -∗
    (∀ x, pif_taint (dom fdm) -∗ K x) -∗ K (RdBytes []).

  Hypothesis Hhalt_long : forall (fdm : fdmap) (fd : Z) (d : nat) (bs : list (bv 8))
      (K : Z -> iProp Σ),
    bs <> [] -> fdm !! fd = Some d -> 2 ^ 31 <= Z.of_nat (length bs) ->
    pif_fds fdm -∗ pif_halt d -∗
    ((pif_fds fdm -∗ pif_halt d -∗ K (-1)) ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.

  Hypothesis Hnil_ro : forall (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (fd : nat) (d : nat) (x : dspec) (K : Z -> iProp Σ),
    fdm !! Z.of_nat fd = Some d -> vs !! d = Some PDRd ->
    l !! fd = Some (FdOpen true false (FdPipe γp)) ->
    pif_fds_at fdm l vs w -∗ pif_dev d x -∗
    ((pif_fds fdm -∗ pif_dev d x -∗ K 0) ∧ (pif_fds fdm -∗ pif_dev d x -∗ K (-1))
     ∧ (∀ y, pif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P (Z.of_nat fd) [] K.

  (* ------------------------------------------------------------------- *)
  (*  THE LAWS                                                            *)
  (* ------------------------------------------------------------------- *)

  (* [ei_write] at the console, either kind *)
  Lemma pif_write (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    pif_fds fdm -∗ pif_out d alts -∗
    ((pif_fds fdm -∗ pif_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hcons Hsw HPc Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers.
    intros _ Hfd Ha Hpre. iIntros "Hfds Hout HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct "Hout" as "[[Htk Hd] | [Htk Hd]]".
    - (* the popen device *)
      iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst kd.
      destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pcons_write g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
                (YR_pers := YR_pers) Hnd Hwit2 Hwit1 N P (HPc := HPc) Hsw l k rb alts a bs K
                Hlt Hrow Ha Hpre with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iLeft. iFrame "Htk Hd".
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
      iApply ("HK" with "[-Hd Htk] [Htk Hd]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iRight. iFrame "Htk Hd".
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
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_write N P Hsw pn γp L S l k rb a bs K Hlt Hrow Ha Hpre Hne with "Hinv Hstd Hd").
    iSplit; [| iSplit].
    - iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk". iExists (drop (length bs) a). iFrame "Hd". by iPureIntro.
    - iIntros "Hstd Hh". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Hh Htk] [Htk Hh]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk Hh".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
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
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_write_halt N P Hsw pn γp L l k rb bs K Hlt Hrow Hne Hbnd with "Hinv Hstd Hh").
    iSplit.
    - iIntros "Hstd Hh". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hh Htk] [Htk Hh]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk Hh".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
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

  (* [ei_write_nil]: by the descriptor's kind *)
  Lemma pif_write_nil (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_dev d x -∗
    ((pif_fds fdm -∗ pif_dev d x -∗ K 0) ∧ (pif_fds fdm -∗ pif_dev d x -∗ K (-1))
     ∧ (∀ y, pif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.
  Proof using Hkill Hsw HPc Hnil_ro.
    intros Hfd. iIntros "Hfds Hd HK".
    iDestruct (pif_dev_tok with "Hd") as (kd) "[Htk Hback]".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (pif_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iDestruct ("Hback" with "Htk") as "Hd".
    destruct kd.
    - (* the console *)
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pif_cons_nil l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd").
      iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pif_cons_nil l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd").
      iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
    - (* the write end *)
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_write_nil N P Hsw γp l k rb (pif_dev d x) K Hlt Hrow with "Hstd Hd").
      iSplit; [| iSplit].
      + iIntros "Hstd Hd". iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd").
        iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iIntros "Hstd Hd". iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hd] Hd").
        iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
        iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
    - (* the read end: writable, or [Hnil_ro] *)
      destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      destruct wb.
      + iApply (pipe_write_nil N P Hsw γp l k true (pif_dev d x) K Hlt Hrow with "Hstd Hd").
        iSplit; [| iSplit].
        * iIntros "Hstd Hd". iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd").
          iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
        * iIntros "Hstd Hd". iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hd] Hd").
          iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
        * iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
          iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
      + iApply (Hnil_ro fdm l vs w k d x K Hfd Hv Hrow with "[Hstd Hpay Hpool Htoks] Hd HK").
        iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
  Qed.

  (* the read end's law at a chunk, shared by DIn and DInE: the descriptor's
     row, and [UkPipeDev.pipe_read] *)
  Local Ltac pif_read_row Hok Hfd Hv :=
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow);
    destruct Hrow as (_ & wb & Hrow); rewrite Nat2Z.id in Hrow.

  (* [ei_read] at DIn: the chunk, or the end of file at the line's end
     (which is the empty chunk at nothing owed); the early end is
     [Heof_short] *)
  Lemma pif_read (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        pif_fds fdm -∗ pif_in d S' -∗ K (RdBytes cb))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr Heof_short.
    intros Hn Hfd. iIntros "Hfds [Htk Hd] HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. pif_read_row Hok Hfd Hv.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read N P Hsr pn γp L Sin l k wb n K Hlt Hrow Hn with "Hinv Hstd Hd").
    iSplit; [| iSplit].
    - iIntros (cb S') "%Hc Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb S' with "[%] [-Hd Htk] [Htk Hd]"); [exact Hc | |].
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk Hd".
    - iIntros "Hstd Hd".
      destruct (decide (Sin = [])) as [-> | Hne].
      + iDestruct "HK" as "[HK _]".
        iApply ("HK" $! [] [] with "[%] [-Hd Htk] [Htk Hd]").
        { split; [reflexivity |]. split; [simpl; lia | intros _; reflexivity]. }
        { iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro. }
        { iFrame "Htk". iDestruct "Hd" as (c) "(%Hc & Hr & _)". iExists c. iFrame "Hr".
          by iPureIntro. }
      + iDestruct "HK" as "[_ HK]".
        iApply (Heof_short fdm l vs w d k Sin K Hfd Hv Hne with "[-Hd Htk HK] Htk Hd HK").
        iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
  Qed.

  (* [ei_read_e] at DInE: the chunk, the end of file at the line's end, or
     [Heof_short] *)
  Lemma pif_read_e (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        pif_fds fdm -∗ pif_in d S' -∗ K (RdBytes cb))
     ∧ (pif_fds fdm -∗ pif_in_end d -∗ K (RdBytes []))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr Heof_short.
    intros Hn Hfd. iIntros "Hfds [Htk Hd] HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. pif_read_row Hok Hfd Hv.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read N P Hsr pn γp L Sin l k wb n K Hlt Hrow Hn with "Hinv Hstd Hd").
    iSplit; [| iSplit].
    - iIntros (cb S') "%Hc Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb S' with "[%] [-Hd Htk] [Htk Hd]"); [exact Hc | |].
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk Hd".
    - iIntros "Hstd Hd".
      destruct (decide (Sin = [])) as [-> | Hne].
      + iDestruct "HK" as "[_ [HK _]]".
        iApply ("HK" with "[-Hd Htk] [Htk Hd]").
        { iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro. }
        { iFrame "Htk Hd". }
      + iDestruct "HK" as "[_ [_ HK]]".
        iApply (Heof_short fdm l vs w d k Sin K Hfd Hv Hne with "[-Hd Htk HK] Htk Hd HK").
        iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
  Qed.

  (* [ei_read_end] at DInEnd: the empty chunk again; a nonempty chunk
     after the end is refuted by the count, the end's shot is kept *)
  Lemma pif_read_end (fdm : fdmap) (fd : Z) (d : nat) (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pif_fds fdm -∗ pif_in_end d -∗
    ((pif_fds fdm -∗ pif_in_end d -∗ K (RdBytes []))
     ∧ (∀ x, pif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd. iIntros "Hfds [Htk Hd] HK".
    iDestruct "Hd" as (c) "(%Hc & Hr & #Heof)".
    assert (HcL : (length L <= c)%nat) by (apply pif_drop_nil_le; by symmetry).
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd. pif_read_row Hok Hfd Hv.
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iApply (pipe_read N P Hsr pn γp L [] l k wb n K Hlt Hrow Hn with "Hinv Hstd [Hr]").
    { rewrite /pipe_in. iExists c. by iFrame "Hr". }
    iSplit; [| iSplit].
    - iIntros (cb S') "%Hchk Hstd Hd".
      destruct Hchk as (Happ & _ & _). symmetry in Happ. apply app_eq_nil in Happ as [-> ->].
      iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk". iDestruct "Hd" as (c') "[%Hc' Hr]".
        assert (Hc'L : (length L <= c')%nat) by (apply pif_drop_nil_le; by symmetry).
        rewrite /pipe_in_eof. iExists c'. iFrame "Hr". iSplit; [done |].
        rewrite (take_ge L c'); [| exact Hc'L]. iEval (rewrite (take_ge L c HcL)) in "Heof".
        iExact "Heof".
    - iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]").
      + iExists l, vs, w. iFrame "Hstd Hpay Hpool Htoks He". by iPureIntro.
      + iFrame "Htk Hd".
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pif_taint_of_fds fdm l vs Hok with "Ht Hstd Hpay He").
  Qed.

  (* the open laws: the scope is empty *)
  Lemma pif_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path content : list (bv 8)) (K : Z -> iProp Σ) :
    path ∈ paths -> files path = Some content ->
    pif_fds fdm -∗ pif_filesr files paths -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
        (∀ d : nat, ⌜forall fd', fdm !! fd' <> Some d⌝ -∗
           pif_fds (<[fd := d]> fdm) ∗ pif_in d content) -∗
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

  (* the descriptors after a pipe end's last descriptor closed: the slot
     shut, the token home to the pool *)
  Lemma pif_fds_after_close (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (w : nat -> pdev) (k : nat) (d : nat) (kd : pdev) :
    pif_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> ~ fd_shared fdm (Z.of_nat k) d ->
    vs !! d = Some kd ->
    UserFd.ustd γfd (<[k := FdClosed]> l) -∗ pif_pay -∗ own γreg (pif_pool (dom vs) w) -∗
    ([∗ map] d ↦ x ∈ vs, pif_tok d (1/2) x) -∗ pif_tok d (1/2) kd -∗ pif_env -∗
    pif_fds (delete (Z.of_nat k) fdm).
  Proof using .
    intros Hok Hfd Hns Hv. iIntros "Hstd Hpay Hpool Htoks Htk #He".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (pif_tok d 1 kd) with "[Htk Htk']" as "Htk".
    { rewrite pif_tok_halves. iFrame "Htk Htk'". }
    assert (Hdd : d ∈ dom vs) by (apply elem_of_dom; by eexists).
    iDestruct (pif_pool_give vs w d kd Hdd with "Hpool Htk") as "Hpool".
    iExists (<[k := FdClosed]> l), (delete d vs), _.
    iFrame "Hstd Hpay Hpool Htoks He". iPureIntro.
    apply pif_ok_close; [exact Hok | exact Hfd | exact Hns].
  Qed.

  (* [ei_close] of a pipe end's last descriptor: [UkPipeDev.pipe_close] at
     the protocol's registration, the token home to the pool, the end's
     resource dropped; a console slot by [UkFileDev.file_close_std] *)
  Lemma pif_close (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d ->
    pif_fds fdm -∗ pif_filesr files paths -∗ pif_dev d x -∗
    ((pif_fds (delete fd fdm) -∗ pif_filesr files paths -∗ K 0)
     ∧ (∀ y, pif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns. iIntros "Hfds Hfiles Hd HK".
    iDestruct (pif_dev_tok with "Hd") as (kd) "[Htk Hback]".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
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
                with "Hstd Hpay Hpool Htoks Htk He").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDCons Hok Hfd Hns Hv
                with "Hstd Hpay Hpool Htoks Htk He").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k rb true K Hlt Hrow with "Hreg Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDWr Hok Hfd Hns Hv
                with "Hstd Hpay Hpool Htoks Htk He").
    - destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k true wb K Hlt Hrow with "Hreg Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hfiles] Hfiles").
      iApply (pif_fds_after_close fdm l vs w k d PDRd Hok Hfd Hns Hv
                with "Hstd Hpay Hpool Htoks Htk He").
  Qed.

  (* ...of a shared one: the device stays *)
  Lemma pif_close_shared (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> fd_shared fdm fd d ->
    pif_fds fdm -∗
    ((pif_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, pif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hsh. iIntros "Hfds HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hpay & %Hok & Hpool & Htoks & #He)".
    destruct (pif_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    destruct (pif_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iPoseProof (pif_env_inv with "He") as "#Hinv".
    iPoseProof (pipe_reg_of_inv pn γp L with "Hinv") as "#Hreg".
    destruct kd.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
      iExists (<[k := FdClosed]> l), vs, w. iFrame "Hstd Hpay Hpool Htoks He".
      iPureIntro. exact (pif_ok_close_shared fdm l vs k d Hok Hfd Hsh).
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
      iExists (<[k := FdClosed]> l), vs, w. iFrame "Hstd Hpay Hpool Htoks He".
      iPureIntro. exact (pif_ok_close_shared fdm l vs k d Hok Hfd Hsh).
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k rb true K Hlt Hrow with "Hreg Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
      iExists (<[k := FdClosed]> l), vs, w. iFrame "Hstd Hpay Hpool Htoks He".
      iPureIntro. exact (pif_ok_close_shared fdm l vs k d Hok Hfd Hsh).
    - destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc γp l k true wb K Hlt Hrow with "Hreg Hstd").
      iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
      iExists (<[k := FdClosed]> l), vs, w. iFrame "Hstd Hpay Hpool Htoks He".
      iPureIntro. exact (pif_ok_close_shared fdm l vs k d Hok Hfd Hsh).
  Qed.

  (* [ei_exit]: the payload, held up front (the file header) *)
  Lemma pif_exit (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    (forall fd d, fdm !! fd = Some d -> d ∈ ds) ->
    pif_fds fdm -∗ pif_filesr files paths -∗ ([∗ set] d ∈ ds, pif_dev d (dv d)) -∗
    ex_obl N P s.
  Proof using HNc Hse.
    intros _ _. iIntros "Hfds _ _".
    iDestruct "Hfds" as (l vs w) "(_ & Hpay & _)". rewrite /pif_pay.
    iApply (fh_exit_pay N P Hse with "Hpay").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE RECORD                                                          *)
  (* ------------------------------------------------------------------- *)

  Definition pipe_iface : ep_iface N P.
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Heof_short Hhalt_long Hnil_ro.
    refine (MkEI N P pif_fds pif_out pif_outh pif_halt (fun _ _ => False%I)
              pif_in pif_in pif_in_end
              (fun _ _ _ _ => False%I) (fun _ _ _ => False%I) (fun _ => False%I)
              pif_filesr pif_taint pif_taint_pays
              pif_write pif_write_h _ pif_write_halt pif_write_nil
              pif_read pif_read_e pif_read_end _ _ _ _ _ _ _ pif_open pif_open_absent
              pif_close pif_close_shared pif_exit).
    - intros. iIntros "_ []".
    (* the copy device (design SS3.4f): the follow-up lane's; nothing here *)
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
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

  (* THE RIGHT PROCESS, at [DIn L] (the file header): fd 0 the read end,
     fds 1 and 2 the console owing the line *)
  Theorem cat_pipe_paid (files : list (bv 8) -> option (list (bv 8))) :
    env_res N P pipe_iface (cat_env 0 1 L [L] files []) {[0%nat; 1%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"]).
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Heof_short Hhalt_long Hnil_ro.
    iIntros "H".
    iApply (tree_pay_of_conforms N P pipe_iface _ _ _
              (cat_stdin_conforms L files []) (cat_tree_safe _ _) with "H").
  Qed.

  (* THE LEFT PROCESS: fd 1 the write end owing the line, which may halt *)
  Theorem echo_pipe_paid (argv : list (list (bv 8))) (files : list (bv 8) -> option (list (bv 8))) :
    drop 1 argv <> [] -> L = wl_line (drop 1 argv) ->
    env_res N P pipe_iface (pipe_env (DOutH [L]) files) {[0%nat]} -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Heof_short Hhalt_long Hnil_ro.
    intros Hne HL. iIntros "H". rewrite HL.
    iApply (tree_pay_of_conforms N P pipe_iface _ _ _
              (echo_pipe_conforms argv files Hne) (echo_tree_safe _ _) with "H").
  Qed.

  (* ---- what the round lends cat ([UShPipeLaw.pl_RcR] and [pl_cat_fd0]):
          the ledger with fd 0 the pipe's read end and fds 1, 2 the console,
          the payload, the registry's pool with device 0 the popen console
          and device 1 the read end, the protocol, the reader's permit at
          0, the round's context with [YR], and the family's two halves at
          0 ---- *)
  Lemma cat_env_res (l : list fdstate) (wb rb1 rb2 : bool) (w : nat -> pdev)
      (files : list (bv 8) -> option (list (bv 8))) :
    w 0%nat = PDPCons -> w 1%nat = PDRd ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ pif_pay -∗ own γreg (pif_pool ∅ w) -∗
    pipe_inv pn γp L -∗ rtok pn -∗
    era_pin γ (S gen_id) v -∗ pipe_link_taint g -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗ YR -∗
    PipeBoth.wcur gR (1/2) 0%nat -∗ PipeBoth.wcur gM (1/2) 0%nat -∗
    env_res N P pipe_iface (cat_env 0 1 L [L] files []) {[0%nat; 1%nat]}.
  Proof using Heq Hkill YR_pers.
    intros Hw0 Hw1 Hl0 Hl1 Hl2 HL.
    set (fdm := (<[1 := 0%nat]> (<[2 := 0%nat]> {[0 := 1%nat]}) : fdmap)).
    set (vs := (<[0%nat := PDPCons]> {[1%nat := PDRd]} : gmap nat pdev)).
    assert (Hok : pif_ok fdm l vs).
    { split; [| split].
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- _] | (_ & [[<- _] | (_ & <- & _)])]; lia.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- <-] | (_ & [[<- <-] | (_ & <- & <-)])].
        + rewrite /vs lookup_insert. simpl. split; [unfold NSTD; lia | by exists rb1].
        + rewrite /vs lookup_insert. simpl. split; [unfold NSTD; lia | by exists rb2].
        + rewrite /vs lookup_insert_ne; [| done]. rewrite lookup_singleton. simpl.
          split; [unfold NSTD; lia | by exists wb].
      - intros d. rewrite /vs dom_insert_L dom_singleton_L elem_of_union !elem_of_singleton.
        split.
        + intros [-> | ->]; [exists 1; apply lookup_insert |].
          exists 0. rewrite /fdm lookup_insert_ne; [| lia]. rewrite lookup_insert_ne; [| lia].
          apply lookup_singleton.
        + intros (fd & Hfd). revert Hfd. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
          intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; [by left | by left | by right]. }
    iIntros "Hstd Hpay Hpool #Hinv Hrt #Hpin #Hlt #Hblk #Hex #HYR HgR HgM".
    rewrite /env_res.
    iDestruct (pif_pool_own_take ∅ w 0%nat with "Hpool") as "[Hpool Htk0]"; [set_solver |].
    iDestruct (pif_pool_own_take ({[0%nat]} ∪ ∅) w 1%nat with "Hpool") as "[Hpool Htk1]";
      [set_solver |].
    rewrite Hw0 Hw1.
    iDestruct (pif_tok_halves with "Htk0") as "[Htk0a Htk0b]".
    iDestruct (pif_tok_halves with "Htk1") as "[Htk1a Htk1b]".
    iPoseProof (pif_env_of_inv with "Hinv") as "#He".
    iSplit.
    { iPureIntro. intros fd d. cbn [cat_env pe_fd].
      rewrite lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
      intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; set_solver. }
    iSplitL "Hstd Hpay Hpool Htk0a Htk1a".
    { rewrite pif_ei_fds. iExists l, vs, w. cbn [cat_env pe_fd].
      iFrame "Hstd Hpay He". iSplit; [by iPureIntro |].
      iSplitL "Hpool".
      { rewrite (pif_pool_ext (dom vs) ({[1%nat]} ∪ ({[0%nat]} ∪ ∅)) w w);
          [iExact "Hpool" | | intros; reflexivity].
        rewrite /vs dom_insert_L dom_singleton_L. set_solver. }
      rewrite /vs big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton. iFrame "Htk0a Htk1a". }
    iSplitR.
    { rewrite pif_ei_files /pif_filesr. cbn [cat_env pe_paths]. by iPureIntro. }
    rewrite /dev_res big_sepS_union; [| set_solver]. rewrite !big_sepS_singleton !pif_dev_of.
    assert (E0 : pe_dev (cat_env 0 1 L [L] files []) 0%nat = DOut [L]) by reflexivity.
    assert (E1 : pe_dev (cat_env 0 1 L [L] files []) 1%nat = DIn L) by reflexivity.
    rewrite E0 E1. cbn [pif_dev]. iSplitL "Htk0b HgR HgM".
    - iLeft. iFrame "Htk0b".
      iDestruct (pcons_dev_of_ch g v I L gL gR gM XL YR (YR_pers := YR_pers) 0 HL
                   with "Hpin Hlt Hblk Hex HYR [HgR HgM]") as "Hd".
      { rewrite /UShPipeCatRound.pcat_ch. simpl. iLeft. iFrame "HgR HgM". }
      rewrite drop_0. iExact "Hd".
    - iFrame "Htk1b". rewrite /pipe_in. iExists 0%nat. iEval (rewrite /rtok) in "Hrt".
      iFrame "Hrt". by iPureIntro.
  Qed.

  Theorem cat_pipe_paid_of_round (l : list fdstate) (wb rb1 rb2 : bool) (w : nat -> pdev) :
    w 0%nat = PDPCons -> w 1%nat = PDRd ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ pif_pay -∗ own γreg (pif_pool ∅ w) -∗
    pipe_inv pn γp L -∗ rtok pn -∗
    era_pin γ (S gen_id) v -∗ pipe_link_taint g -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    □ (XL -∗ YR ={↑pipeN}=∗ False) -∗ YR -∗
    PipeBoth.wcur gR (1/2) 0%nat -∗ PipeBoth.wcur gM (1/2) 0%nat -∗
    tree_pay N P (cat_tree [sb "cat"]).
  Proof using Hcons Heq Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hnd Hwit1 Hwit2 XL_tl YR_tl YR_pers
              Heof_short Hhalt_long Hnil_ro.
    intros Hw0 Hw1 Hl0 Hl1 Hl2 HL.
    iIntros "Hstd Hpay Hpool Hinv Hrt Hpin Hlt Hblk Hex HYR HgR HgM".
    iApply (cat_pipe_paid (fun _ => None)).
    iApply (cat_env_res l wb rb1 rb2 w (fun _ => None) Hw0 Hw1 Hl0 Hl1 Hl2 HL
              with "Hstd Hpay Hpool Hinv Hrt Hpin Hlt Hblk Hex HYR HgR HgM").
  Qed.

  (* ---- what the round lends echo ([UEchoPipe.ep_pay] at [pl_RcL]): fd 1
          the pipe's write end, the payload, the pool with device 0 the
          write end, the protocol, the write permit at 0 with the empty
          lower bound ---- *)
  Lemma echo_env_res (l : list fdstate) (rb : bool) (w : nat -> pdev)
      (files : list (bv 8) -> option (list (bv 8))) :
    w 0%nat = PDWr ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    Z.of_nat (length L) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗ pif_pay -∗ own γreg (pif_pool ∅ w) -∗
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
    iIntros "Hstd Hpay Hpool #Hinv Hw Hlb". rewrite /env_res.
    iDestruct (pif_pool_own_take ∅ w 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    rewrite Hw0. iDestruct (pif_tok_halves with "Htk") as "[Htk1 Htk2]".
    iPoseProof (pif_env_of_inv with "Hinv") as "#He".
    iSplit.
    { iPureIntro. intros fd d. cbn [pipe_env pe_fd].
      rewrite lookup_singleton_Some. intros [_ <-]. set_solver. }
    iSplitL "Hstd Hpay Hpool Htk1".
    { rewrite pif_ei_fds. iExists l, vs, w. cbn [pipe_env pe_fd].
      iFrame "Hstd Hpay He". iSplit; [by iPureIntro |].
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
              Heof_short Hhalt_long Hnil_ro.
    intros Hw0 Hl1 Hne HLw HL. iIntros "Hstd Hpay Hpool Hinv Hw Hlb".
    iApply (echo_pipe_paid argv (fun _ => None) Hne HLw).
    iApply (echo_env_res l rb w (fun _ => None) Hw0 Hl1 HL with "Hstd Hpay Hpool Hinv Hw Hlb").
  Qed.

End UkPipeIface.

(* ===================================================================== *)
(*  3.  THE VACUITY WITNESSES: every hypothesis-free law at cat's         *)
(*      instance, through [UkStub]'s stub laws                            *)
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
  Context (N : uk_names Σ) `{!ukn_const N}.
  Context (γreg : gname).

  Local Instance pif_cat_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  Definition pif_write_cat :=
    pif_write g Hcons v I L gL gR gM XL YR (XL_tl := XL_tl) (YR_tl := YR_tl)
      (YR_pers := YR_pers) Hnd Hwit2 Hwit1 pn γp N (cat_prog N) (cat_stub_write N) γreg.
  Definition pif_write_h_cat :=
    pif_write_h g Hkill L pn γp N (cat_prog N) (cat_stub_write N) γreg.
  Definition pif_read_end_cat :=
    pif_read_end g Hkill L pn γp N (cat_prog N) (cat_stub_read N) γreg.
  Definition pif_close_cat :=
    pif_close g v I L gL gR gM XL YR pn γp N (cat_prog N) (cat_stub_close N) γreg.
  Definition pif_close_shared_cat :=
    pif_close_shared g L pn γp N (cat_prog N) (cat_stub_close N) γreg.
  Definition pif_exit_cat :=
    pif_exit g v I L gL gR gM XL YR pn γp N (cat_prog N) (cat_stub_exit N) γreg.
  Definition pif_taint_pays_cat :=
    pif_taint_pays g N (cat_prog N) (cat_stub_read N) (cat_stub_write N) (cat_stub_open N)
      (cat_stub_close N) (cat_stub_exit N).
End UkPipeIfaceCat.
