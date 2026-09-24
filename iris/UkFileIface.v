(* ===================================================================== *)
(* UkFileIface.v -- THE FILE APPLICATION'S ENDPOINT INTERFACE: one         *)
(* [UkHandler.ep_iface] from the console ([UkConsOut]) and the file        *)
(* ([UkFileDev]), and cat f / echo > f paid end to end through the once-  *)
(* glue [UkHandler.tree_pay_of_conforms] (program-specs cut 4(c)).         *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4b-SS3.4c.             *)
(*                                                                        *)
(* THE REGISTRY IS GHOST STATE.  A device is a natural number in the pure *)
(* layer; what it IS -- the console, the file `f` held at a standard slot *)
(* for writing ([FDFile i γo]), or an input on `f` ([FDIn s i γo]: at a   *)
(* tail handle, or with [s] set at a STANDARD slot the ledger names,      *)
(* where the open of a program that closed a standard stream lands) --   *)
(* is a token [fif_tok d q v] in one camera, a function                   *)
(* from device numbers to a fraction of an agreement.  [ei_fds] holds the *)
(* POOL (the whole token of every number no descriptor names) and HALF of *)
(* the token of every number one does; the device's resource holds the   *)
(* other half.  So a device resource names exactly the kind and the      *)
(* kernel object its descriptors point at, an open mints the token of a  *)
(* fresh number out of the pool (after the kernel named the descriptor:  *)
(* [UkFileDev.file_open_present]'s handle arm ends in an update), and a  *)
(* close of the last descriptor gives it back ([UkHandler.ei_close] hands *)
(* the device over).                                                     *)
(*                                                                        *)
(* WHAT IS PROVED: the console write ([UkConsOut.cons_write]), the file   *)
(* write ([UkFileDev.file_write], chunk [b] of the line at a held ledger  *)
(* slot), the READ ([file_read] at the tail handle the token names,       *)
(* [file_read_std] at a standard slot), the open of `f` present -- the    *)
(* descriptor landing where the LEDGER says ([UserFd.ualloc]: the lowest  *)
(* closed standard slot, else a fresh tail handle) -- and absent at any   *)
(* non-creating mode, EVERY close (an input's, at its handle or its       *)
(* standard slot, with the deed's fraction home and the token back to the *)
(* pool; a standard stream of any kind, its ledger slot to [FdClosed];    *)
(* a shared standard stream keeping its device; a shared tail descriptor  *)
(* is impossible, an input has one), the exit, and the pipe laws          *)
(* (vacuous).  So the ledger's invariant carries closed standard slots    *)
(* and needs no [fd_lowest_closed l = None] (lane leaf-payers).           *)
(*                                                                        *)
(* WHAT IS NOT, as section hypotheses at the narrowest refused case:      *)
(*                                                                        *)
(*   [Hnil_in]  the zero-length write at an INPUT (a tail handle, or the   *)
(*             read-only standard slot of [FDIn true]): row 16 carries no *)
(*             return blanket (design/user-write.md SS3d), and at a        *)
(*             read-only descriptor [SpecFilewrite.filewrite_extra] is    *)
(*             [emp], so the U tier cannot tell 0 or -1 from any other    *)
(*             answer.  (At the console it is proved, [fif_cons_nil]; at  *)
(*             the file held for writing too, [fif_file_nil] over          *)
(*             [UkFileDev.file_write_nil].)                                *)
(*                                                                        *)
(* THE TAINT PAYS ANY DISCIPLINED TREE ([fif_taint_pays]): the free       *)
(* handler at every hole, out of the application's supply (write, read,   *)
(* open rows) and the machine's credential (close), with the ledger and   *)
(* the handles of the held descriptors; the read row's count bound is     *)
(* [UkRunSys.wp_uk_ecall_read]'s (lane rdbound).                           *)
(*                                                                        *)
(* AND AT ECHO: [ep_iface] asks for every law whatever tree it pays, and  *)
(* [UkEchoTree.echo_prog] names all five stubs at echo's own addresses    *)
(* ([UkStub.echo_stub_read] and its siblings, for the three echo never    *)
(* calls), so SS4 instantiates the record and the two echo theorems at   *)
(* echo's program with no stub hypothesis ([file_iface_echo],             *)
(* [echo_f_paid_echo], [echo_f_paid_of_redirect_echo]); the four gaps    *)
(* above remain its hypotheses, by name.                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From Stdlib Require Import FunctionalExtensionality.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import ProgTree UkTree UkStub.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi UserBits.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import FdSlots UserFd UserCwd.
Require Import UserHeap UserPerm UserPtTree.
Require Import ProcGeom.
Require Import CtxIdDefs.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst UexecExecMint.
Require Import UsysMemOk.
Require Import SpecSysRead.            (* [sys_rw_count] *)
Require Import SpecConsolewrite UkWriteLeaf.  (* [cons_out_chain], the console write rows *)
Require Import ConsoleInv.             (* [CONSOLE] *)
Require Import FsCfg.
Require Import AppCfg AppInv.
Require Import FsInitPin FsShPin FsEchoPin FsCatPin.
Require Import EchoDisc EchoOut LineWords.
Require Import FileState.              (* [echo_chunks] *)
Require Import AppFile AppFileCons FileOpen.
Require Import UserOff.
Require Import UkFileOpen.
Require Import FileWrite UEchoFile.
Require Import FsImg FsImgCheck.
Require Import SysOpenDefs.
Require Import LineModel LineModelInst FileDisc GenOut FileOut.
Require Import FileLinks FileLinkGen.       (* [file_links], [file_params] *)
Require Import UkConsOut UkFileDev.
Require Import UkHandler ProgTreeFile.
Require Import UCodeCat UkCatTree.
Require Import UCodeEcho UkEchoTree.   (* echo's instance: [echo_prog] *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE REGISTRY                                                      *)
(* ===================================================================== *)

(* what a device is: the console, `f` held for writing at a standard slot,
   or an input on `f` at a tail handle *)
Inductive fdev := FDCons | FDFile (i : Z) (γo : gname) | FDIn (s : bool) (i : Z) (γo : gname).

Definition fifRegR := discrete_funUR (fun _ : nat => optionUR (dfrac_agreeR (leibnizO fdev))).
Class fifRegG (Σ : gFunctors) := FifRegG { fif_reg_inG :: inG Σ fifRegR }.
Definition fifRegΣ : gFunctors := #[GFunctor fifRegR].
Global Instance subG_fifRegΣ {Σ} : subG fifRegΣ Σ -> fifRegG Σ.
Proof. solve_inG. Qed.

(* the pool: the whole token of every number outside [B], at [w] *)
Definition fif_pool (B : gset nat) (w : nat -> fdev) : fifRegR :=
  fun d => if decide (d ∈ B) then None
           else Some (to_dfrac_agree (DfracOwn 1) (w d : leibnizO fdev)).

Definition fif_single (d : nat) (q : Qp) (v : fdev) : fifRegR :=
  discrete_fun_singleton d (Some (to_dfrac_agree (DfracOwn q) (v : leibnizO fdev))).

Lemma fif_dfa_valid (v : fdev) : ✓ (to_dfrac_agree (DfracOwn 1) (v : leibnizO fdev)).
Proof. split; [apply dfrac_valid_own; reflexivity | done]. Qed.

Lemma fif_pool_valid (B : gset nat) (w : nat -> fdev) : ✓ fif_pool B w.
Proof.
  intros d. rewrite /fif_pool. case_decide; [done |].
  apply Some_valid, fif_dfa_valid.
Qed.

Lemma fif_pool_take (B : gset nat) (w : nat -> fdev) (d : nat) :
  d ∉ B -> fif_pool B w ≡ fif_pool ({[d]} ∪ B) w ⋅ fif_single d 1 (w d).
Proof.
  intros Hd x. rewrite discrete_fun_lookup_op /fif_pool /fif_single.
  destruct (decide (x = d)) as [-> | Hne].
  - rewrite discrete_fun_lookup_singleton.
    rewrite decide_False; [| exact Hd]. rewrite decide_True; [| set_solver].
    by rewrite left_id.
  - rewrite discrete_fun_lookup_singleton_ne; [| congruence]. rewrite right_id.
    destruct (decide (x ∈ B)) as [Hx | Hx];
      [rewrite decide_True; [done | set_solver] | rewrite decide_False; [done | set_solver]].
Qed.

Lemma fif_pool_ext (B B' : gset nat) (w w' : nat -> fdev) :
  B = B' -> (forall x, x ∉ B -> w x = w' x) -> fif_pool B w = fif_pool B' w'.
Proof.
  intros <- Hw.
  assert (H : forall x, fif_pool B w x = fif_pool B w' x).
  { intros x. rewrite /fif_pool. case_decide as Hx; [reflexivity |]. by rewrite (Hw x Hx). }
  exact (functional_extensionality _ _ H).
Qed.

Lemma fif_pool_update (B : gset nat) (w : nat -> fdev) (v : fdev) :
  fif_pool B w ~~> fif_pool B (fun _ => v).
Proof.
  apply discrete_fun_update. intros a. rewrite /fif_pool.
  case_decide; [reflexivity |].
  apply option_update, cmra_update_exclusive, fif_dfa_valid.
Qed.

(* the files the application describes: `f` *)
Definition fif_files (s : option (list (bv 8))) : list (bv 8) -> option (list (bv 8)) :=
  fun p => if decide (p = fname_f) then s else None.

Lemma fif_files_f (s : option (list (bv 8))) : fif_files s fname_f = s.
Proof. unfold fif_files. case_decide; [reflexivity | done]. Qed.

(* the row a descriptor's device demands of it *)
Definition fif_row (ov : option fdev) (fd : Z) (l : list fdstate) : Prop :=
  match ov with
  | Some FDCons => fd < Z.of_nat NSTD
                   /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdDevice CONSOLE))
  | Some (FDFile i γo) => fd < Z.of_nat NSTD
                   /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdInode i γo OffHeld))
  | Some (FDIn true i γo) => fd < Z.of_nat NSTD
                   /\ l !! Z.to_nat fd = Some (FdOpen true false (FdInode i γo OffHeld))
  | Some (FDIn false _ _) => Z.of_nat NSTD <= fd
  | None => False
  end.

(* the slot a descriptor other than [k]'s names is not [k] *)
Lemma fif_slot_ne (k : nat) (fd : Z) : 0 <= fd -> fd <> Z.of_nat k -> k <> Z.to_nat fd.
Proof.
  intros H0 Hne Heq. apply Hne. symmetry. rewrite Heq. apply Z2Nat.id. exact H0.
Qed.

(* THE PURE HALF OF [ei_fds]: the binding against the ledger [l] and the
   registry's values [vs] *)
Definition fif_ok (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) : Prop :=
  (forall fd d, fdm !! fd = Some d -> 0 <= fd < Z.of_nat NOFILE)
  /\ (forall fd d, fdm !! fd = Some d -> fif_row (vs !! d) fd l)
  /\ (forall d, d ∈ dom vs <-> exists fd, fdm !! fd = Some d)
  /\ (forall fd fd' d s i γo, fdm !! fd = Some d -> fdm !! fd' = Some d ->
        vs !! d = Some (FDIn s i γo) -> fd = fd').

Lemma fif_ok_lookup fdm l vs fd d :
  fif_ok fdm l vs -> fdm !! fd = Some d -> exists v, vs !! d = Some v.
Proof.
  intros (_ & _ & H3 & _) Hfd. apply elem_of_dom. apply H3. by exists fd.
Qed.

Lemma fif_ok_open fdm l vs (k : nat) (d : nat) (i : Z) (γo : gname) :
  fif_ok fdm l vs -> (NSTD <= k < NOFILE)%nat ->
  fdm !! Z.of_nat k = None -> (forall fd', fdm !! fd' <> Some d) ->
  fif_ok (<[Z.of_nat k := d]> fdm) l (<[d := FDIn false i γo]> vs).
Proof.
  intros (H1 & H2 & H3 & H4) Hk Hnone Hfr.
  split; [| split; [| split]].
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
    + intros _. lia.
    + rewrite lookup_insert_ne; [| congruence]. apply H1.
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
    + rewrite lookup_insert. intros [= <-]. rewrite lookup_insert. simpl. lia.
    + rewrite (lookup_insert_ne fdm); [| congruence]. intros Hfd.
      rewrite (lookup_insert_ne vs); [| intros ->; exact (Hfr fd Hfd)]. exact (H2 fd d' Hfd).
  - intros d'. rewrite dom_insert_L elem_of_union elem_of_singleton H3. split.
    + intros [-> | (fd & Hfd)].
      * exists (Z.of_nat k). apply lookup_insert.
      * exists fd. rewrite lookup_insert_ne; [exact Hfd |]. intros Heq.
        rewrite <- Heq in Hfd. congruence.
    + intros (fd & Hfd). destruct (decide (fd = Z.of_nat k)) as [-> |].
      * rewrite lookup_insert in Hfd. injection Hfd as <-. by left.
      * rewrite lookup_insert_ne in Hfd; [| congruence]. right. by exists fd.
  - intros fd fd' d' s' i' γo'.
    destruct (decide (d' = d)) as [-> |].
    + intros Ha Hb _.
      destruct (decide (fd = Z.of_nat k)) as [-> |];
        [| rewrite lookup_insert_ne in Ha; [by destruct (Hfr fd) | congruence]].
      destruct (decide (fd' = Z.of_nat k)) as [-> |];
        [done | rewrite lookup_insert_ne in Hb; [by destruct (Hfr fd') | congruence]].
    + rewrite (lookup_insert_ne vs); [| congruence].
      intros Ha Hb.
      destruct (decide (fd = Z.of_nat k)) as [-> |];
        [rewrite lookup_insert in Ha; congruence | rewrite lookup_insert_ne in Ha; [| congruence]].
      destruct (decide (fd' = Z.of_nat k)) as [-> |];
        [rewrite lookup_insert in Hb; congruence | rewrite lookup_insert_ne in Hb; [| congruence]].
      apply (H4 fd fd' d' s' i' γo' Ha Hb).
Qed.

(* every standard slot a descriptor names is OPEN, so a closed one is
   named by none: where the next open lands is free *)
Lemma fif_ok_closed_fresh fdm l vs (k : nat) :
  fif_ok fdm l vs -> length l = NSTD -> l !! k = Some FdClosed ->
  fdm !! Z.of_nat k = None.
Proof.
  intros (_ & H2 & H3 & _) Hlen Hk.
  destruct (fdm !! Z.of_nat k) as [d |] eqn:E; [exfalso | reflexivity].
  assert (Hd : exists v, vs !! d = Some v).
  { apply elem_of_dom. apply H3. by exists (Z.of_nat k). }
  destruct Hd as [v Hv]. specialize (H2 _ _ E). rewrite Hv in H2.
  pose proof (lookup_lt_Some _ _ _ Hk) as Hkl.
  destruct v as [| i γo | [|] i γo]; simpl in H2.
  - destruct H2 as (_ & rb & Hl). rewrite Nat2Z.id in Hl. congruence.
  - destruct H2 as (_ & rb & Hl). rewrite Nat2Z.id in Hl. congruence.
  - destruct H2 as (_ & Hl). rewrite Nat2Z.id in Hl. congruence.
  - lia.
Qed.

(* the binding reads the ledger only at the standard slots the descriptors
   name *)
Lemma fif_ok_ledger fdm l l' vs :
  fif_ok fdm l vs ->
  (forall fd d, fdm !! fd = Some d -> l' !! Z.to_nat fd = l !! Z.to_nat fd) ->
  fif_ok fdm l' vs.
Proof.
  intros (H1 & H2 & H3 & H4) Hl. split; [exact H1 | split; [| exact (conj H3 H4)]].
  intros fd d Hfd. specialize (H2 fd d Hfd). unfold fif_row in *. revert H2.
  destruct (vs !! d) as [[| i γo | [|] i γo] |]; intros H2; rewrite ?(Hl fd d Hfd); exact H2.
Qed.

(* ...and an open landing in the lowest CLOSED standard slot [k]: the new
   descriptor's row is the slot, the others are untouched *)
Lemma fif_ok_open_std fdm l vs (k : nat) (d : nat) (i : Z) (γo : gname) :
  fif_ok fdm l vs -> length l = NSTD -> l !! k = Some FdClosed ->
  (forall fd', fdm !! fd' <> Some d) ->
  fif_ok (<[Z.of_nat k := d]> fdm) (<[k := FdOpen true false (FdInode i γo OffHeld)]> l)
    (<[d := FDIn true i γo]> vs).
Proof.
  intros Hok Hlen Hk Hfr.
  pose proof (fif_ok_closed_fresh fdm l vs k Hok Hlen Hk) as Hnone.
  pose proof (lookup_lt_Some _ _ _ Hk) as Hkl.
  destruct Hok as (H1 & H2 & H3 & H4).
  split; [| split; [| split]].
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
    + intros _. unfold NSTD, NOFILE in *. lia.
    + rewrite lookup_insert_ne; [| congruence]. apply H1.
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> | Hne].
    + rewrite lookup_insert. intros [= <-]. rewrite lookup_insert. simpl.
      split; [unfold NSTD in *; lia |]. rewrite Nat2Z.id. apply list_lookup_insert. exact Hkl.
    + rewrite (lookup_insert_ne fdm); [| congruence]. intros Hfd.
      rewrite (lookup_insert_ne vs); [| intros ->; exact (Hfr fd Hfd)].
      specialize (H2 fd d' Hfd). destruct (H1 fd d' Hfd) as [H0 _].
      pose proof (fif_slot_ne k fd H0 Hne) as Hkne.
      unfold fif_row in *. revert H2.
      destruct (vs !! d') as [[| i' γo' | [|] i' γo'] |]; intros H2;
        rewrite ?(list_lookup_insert_ne l k (Z.to_nat fd)
                    (FdOpen true false (FdInode i γo OffHeld)) Hkne); exact H2.
  - intros d'. rewrite dom_insert_L elem_of_union elem_of_singleton H3. split.
    + intros [-> | (fd & Hfd)].
      * exists (Z.of_nat k). apply lookup_insert.
      * exists fd. rewrite lookup_insert_ne; [exact Hfd |]. intros Heq.
        rewrite <- Heq in Hfd. congruence.
    + intros (fd & Hfd). destruct (decide (fd = Z.of_nat k)) as [-> |].
      * rewrite lookup_insert in Hfd. injection Hfd as <-. by left.
      * rewrite lookup_insert_ne in Hfd; [| congruence]. right. by exists fd.
  - intros fd fd' d' s' i' γo'.
    destruct (decide (d' = d)) as [-> |].
    + intros Ha Hb _.
      destruct (decide (fd = Z.of_nat k)) as [-> |];
        [| rewrite lookup_insert_ne in Ha; [by destruct (Hfr fd) | congruence]].
      destruct (decide (fd' = Z.of_nat k)) as [-> |];
        [done | rewrite lookup_insert_ne in Hb; [by destruct (Hfr fd') | congruence]].
    + rewrite (lookup_insert_ne vs); [| congruence].
      intros Ha Hb.
      destruct (decide (fd = Z.of_nat k)) as [-> |];
        [rewrite lookup_insert in Ha; congruence | rewrite lookup_insert_ne in Ha; [| congruence]].
      destruct (decide (fd' = Z.of_nat k)) as [-> |];
        [rewrite lookup_insert in Hb; congruence | rewrite lookup_insert_ne in Hb; [| congruence]].
      apply (H4 fd fd' d' s' i' γo' Ha Hb).
Qed.

Lemma fif_not_shared fdm fd d :
  ~ fd_shared fdm fd d -> forall fd', fd' <> fd -> fdm !! fd' <> Some d.
Proof.
  intros Hns fd' Hne Hfd'. apply Hns. exists fd'. split; [| exact Hfd'].
  apply elem_of_dom. rewrite lookup_delete_ne; [| congruence]. by eexists.
Qed.

Lemma fif_ok_close fdm l vs fd d :
  fif_ok fdm l vs -> fdm !! fd = Some d -> ~ fd_shared fdm fd d ->
  fif_ok (delete fd fdm) l (delete d vs).
Proof.
  intros (H1 & H2 & H3 & H4) Hfd Hns.
  pose proof (fif_not_shared fdm fd d Hns) as Hn.
  split; [| split; [| split]].
  - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
  - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
    rewrite (lookup_delete_ne vs); [exact (H2 fd' d' Hf) |].
    intros Heq. subst d'. exact (Hn fd' (not_eq_sym Hne) Hf).
  - intros d'. rewrite dom_delete_L elem_of_difference elem_of_singleton H3. split.
    + intros ((fd' & Hfd') & Hne). exists fd'. apply lookup_delete_Some. split; [| exact Hfd'].
      intros Heq. subst fd. rewrite Hfd in Hfd'. injection Hfd' as Hdd. exact (Hne (eq_sym Hdd)).
    + intros (fd' & Hfd'). apply lookup_delete_Some in Hfd' as [Hne Hf].
      split; [by exists fd' |]. intros Heq. subst d'. exact (Hn fd' (not_eq_sym Hne) Hf).
  - intros fa fb d' s' i' γo' Ha Hb Hv.
    apply lookup_delete_Some in Ha as [_ Ha]. apply lookup_delete_Some in Hb as [_ Hb].
    apply lookup_delete_Some in Hv as [_ Hv].
    exact (H4 fa fb d' s' i' γo' Ha Hb Hv).
Qed.

(* ...and of a descriptor another one shares the device of: the registry
   keeps the device *)
Lemma fif_ok_close_shared fdm l vs fd d :
  fif_ok fdm l vs -> fdm !! fd = Some d -> fd_shared fdm fd d ->
  fif_ok (delete fd fdm) l vs.
Proof.
  intros (H1 & H2 & H3 & H4) Hfd Hsh.
  split; [| split; [| split]].
  - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
  - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H2 fd' d' Hf).
  - intros d'. rewrite H3. split.
    + intros (fd' & Hfd'). destruct (decide (fd' = fd)) as [-> | Hne].
      * rewrite Hfd in Hfd'. injection Hfd' as <-.
        destruct Hsh as (fd'' & Hin & Hfd''). exists fd''.
        apply elem_of_dom in Hin as [d'' Hd'']. apply lookup_delete_Some in Hd'' as [Hne _].
        apply lookup_delete_Some. by split.
      * exists fd'. apply lookup_delete_Some. by split.
    + intros (fd' & Hfd'). apply lookup_delete_Some in Hfd' as [_ Hf]. by exists fd'.
  - intros fa fb d' s' i' γo' Ha Hb Hv.
    apply lookup_delete_Some in Ha as [_ Ha]. apply lookup_delete_Some in Hb as [_ Hb].
    exact (H4 fa fb d' s' i' γo' Ha Hb Hv).
Qed.

(* the chunk a write at the line's cursor carries *)
Lemma fif_drop_cons {A : Type} `{!Inhabited A} (xs : list A) (b : nat) (y : A) (ys : list A) :
  drop b xs = y :: ys ->
  (b < length xs)%nat /\ xs !!! b = y /\ ys = drop (S b) xs.
Proof.
  intros Hd.
  assert (Hl : xs !! b = Some y).
  { rewrite <- (Nat.add_0_r b), <- lookup_drop, Hd. reflexivity. }
  split; [exact (lookup_lt_Some _ _ _ Hl) |]. split.
  - by apply list_lookup_total_correct.
  - replace (S b) with (b + 1)%nat by lia. rewrite <- drop_drop, Hd. reflexivity.
Qed.

(* a mode without O_CREATE, as the kernel reads it *)
Lemma fif_om_create (m : Z) :
  ~ mode_create m -> SysOpenDefs.om_create (mword_of_int m : mword 64) = false.
Proof.
  unfold mode_create, SysOpenDefs.om_create, om_arg. intros Hm.
  rewrite moi64_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_pow2_bits_low _ 32 9); [| lia].
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N 64) 9); [| lia].
  assert (Hl : Z.land m 512 = 0) by (destruct (Z.eq_dec (Z.land m 512) 0); [done | tauto]).
  pose proof (Z.land_spec m 512 9) as Hs. rewrite Hl Z.bits_0 in Hs.
  change (Z.testbit 512 9) with true in Hs. rewrite andb_true_r in Hs. by rewrite <- Hs.
Qed.

(* ===================================================================== *)
(*  1.  THE INSTANCE                                                      *)
(* ===================================================================== *)

Section UkFileIface.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !fifRegG Σ}.

  (* the file application: its console claim, its deed *)
  Context (g : file_gn) (r : file_names).
  Local Notation c := (fgn_cl g).
  Context (Heq : file_app = MkAppcfg file_names (file_pred c) r).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

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

  (* ------------------------------------------------------------------- *)
  (*  the registry's tokens                                               *)
  (* ------------------------------------------------------------------- *)

  Definition fif_tok (d : nat) (q : Qp) (v : fdev) : iProp Σ := own γreg (fif_single d q v).

  Lemma fif_tok_agree (d : nat) (q1 q2 : Qp) (v1 v2 : fdev) :
    fif_tok d q1 v1 -∗ fif_tok d q2 v2 -∗ ⌜v1 = v2⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite /fif_single discrete_fun_singleton_op discrete_fun_singleton_valid
      -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    by destruct Hv as [_ ?].
  Qed.

  Lemma fif_tok_halves (d : nat) (v : fdev) :
    fif_tok d 1 v ⊣⊢ fif_tok d (1/2) v ∗ fif_tok d (1/2) v.
  Proof using .
    rewrite /fif_tok -own_op /fif_single. f_equiv.
    rewrite (discrete_fun_singleton_op d). f_equiv.
    rewrite -Some_op /to_dfrac_agree -pair_op agree_idemp dfrac_op_own Qp.half_half //.
  Qed.

  Lemma fif_pool_own_take (B : gset nat) (w : nat -> fdev) (d : nat) :
    d ∉ B -> own γreg (fif_pool B w) ⊣⊢ own γreg (fif_pool ({[d]} ∪ B) w) ∗ fif_tok d 1 (w d).
  Proof using . intros Hd. rewrite /fif_tok -own_op -fif_pool_take //. Qed.

  (* a token of a device a descriptor names comes home to the pool *)
  Lemma fif_pool_give (vs : gmap nat fdev) (w : nat -> fdev) (d : nat) (v : fdev) :
    d ∈ dom vs ->
    own γreg (fif_pool (dom vs) w) -∗ fif_tok d 1 v -∗
    own γreg (fif_pool (dom (delete d vs)) (fun x => if decide (x = d) then v else w x)).
  Proof using .
    iIntros (Hd) "Hp Ht".
    set (w' := fun x => if decide (x = d) then v else w x).
    assert (Hw' : w' d = v) by (rewrite /w'; by case_decide).
    rewrite (fif_pool_own_take (dom (delete d vs)) w' d); [| rewrite dom_delete_L; set_solver].
    rewrite Hw'. iFrame "Ht".
    assert (HB : dom vs = {[d]} ∪ dom (delete d vs)).
    { rewrite dom_delete_L. apply set_eq. intros x. rewrite elem_of_union elem_of_singleton
        elem_of_difference elem_of_singleton. split; [| intros [-> | []]; done].
      intros Hx. destruct (decide (x = d)); [by left | by right]. }
    assert (Hww : forall x, x ∉ dom vs -> w x = w' x).
    { intros x Hx. unfold w'. case_decide as Hxd; [| done]. subst x. done. }
    rewrite (fif_pool_ext (dom vs) ({[d]} ∪ dom (delete d vs)) w w' HB Hww). done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  the resources                                                       *)
  (* ------------------------------------------------------------------- *)

  (* the application's persistent facts the device laws read *)
  Definition fif_env : iProp Σ :=
    (□ (app_taint -∗ file_taint c) ∗ □ (file_taint c -∗ app_taint)
     ∗ app_inv fsc_fs ∗ ∃ jo : option Z, file_cons_cred c r jo)%I.

  Global Instance fif_env_persistent : Persistent fif_env.
  Proof using . rewrite /fif_env. apply _. Qed.

  (* the handle an input's TAIL descriptor holds (a standard slot's row is
     the ledger's) *)
  Definition fif_hdl (fd : Z) (ov : option fdev) : iProp Σ :=
    match ov with
    | Some (FDIn false i γo) =>
        UserFd.ufd γfd (Z.to_nat fd) (FdOpen true false (FdInode i γo OffHeld))
    | _ => emp
    end%I.

  (* [ei_fds], at its ledger, its registry's values and its pool *)
  Definition fif_fds_at (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev)
      (w : nat -> fdev) : iProp Σ :=
    (UserFd.ustd γfd l ∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO ∗ ukn_pay N (-1)
     ∗ ⌜fif_ok fdm l vs⌝
     ∗ own γreg (fif_pool (dom vs) w)
     ∗ ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v)
     ∗ ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))
     ∗ fif_env)%I.

  Definition fif_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (vs : gmap nat fdev) (w : nat -> fdev), fif_fds_at fdm l vs w)%I.

  (* the console, at the generic claim of the file model *)
  Definition fif_out (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    (fif_tok d (1/2) FDCons ∗ cons_dev file_lm (file_params g) (file_links g) alts)%I.

  (* the file a redirect holds: the line's chunks from [b] on are owed *)
  Definition fif_out_ok (i : Z) (ws : wordline) : Prop :=
    i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO /\ i <> CAT_INO
    /\ Forall (fun ch => (length ch <= EchoDisc.line_max)%nat) (echo_chunks ws).

  Definition fif_outm (d : nat) (chunks : list (list (bv 8))) : iProp Σ :=
    (∃ (i : Z) (γo : gname), fif_tok d (1/2) (FDFile i γo)
       ∗ ∃ (ws : wordline) (b : nat),
           ⌜chunks = drop b (echo_chunks ws)⌝ ∗ ⌜fif_out_ok i ws⌝
           ∗ file_out c r i γo ws b)%I.

  (* an input the process opened on `f`, at a tail handle or a standard slot *)
  Definition fif_in (d : nat) (S : list (bv 8)) : iProp Σ :=
    (∃ (s : bool) (i : Z) (γo : gname), fif_tok d (1/2) (FDIn s i γo)
       ∗ ∃ (q : Qp) (content : list (bv 8)), file_in r i γo q content S)%I.

  Definition fif_dev (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DOut alts => fif_out d alts | DOutH _ => False | DOutM cs => fif_outm d cs
    | DHalt => False | DIn Sin => fif_in d Sin | DInE _ => False | DInEnd => False
    | DCopy _ _ _ => False | DCopyEnd _ _ => False | DCopyHalt => False
    end%I.

  (* the deed at `f`, the one path described *)
  Definition fif_filesr (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      : iProp Σ :=
    (⌜forall p, p ∈ paths -> p = fname_f⌝
     ∗ ∃ (s : dst) (q : Qp), ⌜files fname_f = snd <$> s⌝ ∗ fdq r q s)%I.

  (* THE TAINT at the held descriptors: the flag and its credential, the
     payload, the ledger and the handles, with every held descriptor an
     open standard slot or a handle *)
  Definition fif_held_ok (held : gset Z) (l : list fdstate) (hm : gmap Z fdstate) : Prop :=
    forall fd, fd ∈ held -> (0 <= fd < Z.of_nat NOFILE)
      /\ ((fd < Z.of_nat NSTD /\ exists st, l !! Z.to_nat fd = Some st /\ st <> FdClosed)
          \/ (Z.of_nat NSTD <= fd /\ is_Some (hm !! fd))).

  Definition fif_taint (held : gset Z) : iProp Σ :=
    (file_taint c ∗ □ (file_taint c -∗ app_taint) ∗ ukn_pay N (-1)
     ∗ ∃ (l : list fdstate) (hm : gmap Z fdstate),
         UserFd.ustd γfd l ∗ ⌜fif_held_ok held l hm⌝
         ∗ [∗ map] fd ↦ st ∈ hm, UserFd.ufd γfd (Z.to_nat fd) st)%I.

  (* ------------------------------------------------------------------- *)
  (*  small facts                                                         *)
  (* ------------------------------------------------------------------- *)

  Definition fif_hf (vs : gmap nat fdev) (d : nat) : option fdstate :=
    match vs !! d with
    | Some (FDIn false i γo) => Some (FdOpen true false (FdInode i γo OffHeld))
    | _ => None
    end.

  Lemma fif_hdls_hm (fdm : fdmap) (vs : gmap nat fdev) :
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))
    ⊣⊢ [∗ map] fd ↦ st ∈ omap (fif_hf vs) fdm, UserFd.ufd γfd (Z.to_nat fd) st.
  Proof using .
    rewrite big_sepM_omap. apply big_sepM_proper. intros fd d _.
    rewrite /fif_hdl /fif_hf. destruct (vs !! d) as [[| i γo | [|] i γo] |]; done.
  Qed.

  Lemma fif_held_ok_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) :
    fif_ok fdm l vs -> fif_held_ok (dom fdm) l (omap (fif_hf vs) fdm).
  Proof.
    intros Hok fd Hfd. apply elem_of_dom in Hfd as [d Hd].
    pose proof Hok as (H1 & H2 & _). split; [exact (H1 fd d Hd) |].
    pose proof (H2 fd d Hd) as Hr.
    destruct (vs !! d) as [[| i γo | [|] i γo] |] eqn:Ev; simpl in Hr.
    - left. destruct Hr as (Hs & rb & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - left. destruct Hr as (Hs & rb & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - left. destruct Hr as (Hs & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - right. split; [exact Hr |]. rewrite lookup_omap Hd /= /fif_hf Ev. by eexists.
    - done.
  Qed.

  (* the taint, out of what a law holds at a taint arm *)
  Lemma fif_taint_of_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) :
    fif_ok fdm l vs ->
    file_taint c -∗ □ (file_taint c -∗ app_taint) -∗ ukn_pay N (-1) -∗ UserFd.ustd γfd l -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ fif_taint (dom fdm).
  Proof using .
    intros Hok. iIntros "#Ht #Hk Hpay Hstd Hhs". rewrite /fif_taint. iFrame "Ht Hk Hpay".
    iExists l, (omap (fif_hf vs) fdm). iFrame "Hstd". iSplit.
    - iPureIntro. by apply fif_held_ok_fds.
    - by rewrite fif_hdls_hm.
  Qed.

  (* a handle the kernel handed back is none the taint holds *)
  Lemma fif_hm_fresh (hm : gmap Z fdstate) (k : nat) (st : fdstate) :
    ([∗ map] fd ↦ st ∈ hm, UserFd.ufd γfd (Z.to_nat fd) st) -∗ UserFd.ufd γfd k st -∗
    ⌜hm !! Z.of_nat k = None⌝ ∗ ([∗ map] fd ↦ st ∈ hm, UserFd.ufd γfd (Z.to_nat fd) st)
    ∗ UserFd.ufd γfd k st.
  Proof using .
    iIntros "Hm Hh".
    destruct (hm !! Z.of_nat k) as [st' |] eqn:E; [| by iFrame].
    iDestruct (big_sepM_lookup_acc _ _ _ _ E with "Hm") as "[Hx _]".
    rewrite Nat2Z.id. iDestruct "Hx" as "[Hx _]". iDestruct "Hh" as "[Hh _]".
    iDestruct (ghost_map_elem_ne with "Hx Hh") as %Hne. by destruct Hne.
  Qed.

  (* the value the registry holds for a named device, read off its token *)
  Lemma fif_toks_agree (vs : gmap nat fdev) (d : nat) (v v' : fdev) (q : Qp) :
    vs !! d = Some v ->
    ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) -∗ fif_tok d q v' -∗
    ⌜v = v'⌝ ∗ ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) ∗ fif_tok d q v'.
  Proof using .
    iIntros (Hv) "Hm Ht".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hv with "Hm") as "[Hx Hcl]".
    iDestruct (fif_tok_agree with "Hx Ht") as %->.
    iFrame "Ht". iSplit; [done |]. iApply ("Hcl" with "Hx").
  Qed.

  (* a descriptor the kernel just handed back is none the process names *)
  Lemma fif_fresh_fd (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) (k : nat)
      (st : fdstate) :
    fif_ok fdm l vs -> (NSTD <= k)%nat ->
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ UserFd.ufd γfd k st -∗
    ⌜fdm !! Z.of_nat k = None⌝ ∗ ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))
    ∗ UserFd.ufd γfd k st.
  Proof using .
    intros Hok Hk. iIntros "Hm Hh".
    destruct (fdm !! Z.of_nat k) as [d |] eqn:E; [| by iFrame].
    destruct (fif_ok_lookup _ _ _ _ _ Hok E) as [v Hv].
    pose proof Hok as (_ & H2 & _). specialize (H2 _ _ E). rewrite Hv in H2.
    destruct v as [| i γo | [|] i γo];
      [destruct H2 as [Hlt _]; lia | destruct H2 as [Hlt _]; lia
       | destruct H2 as [Hlt _]; lia |].
    iDestruct (big_sepM_lookup_acc _ _ _ _ E with "Hm") as "[Hx _]".
    rewrite /fif_hdl Hv Nat2Z.id.
    iDestruct "Hx" as "[Hx _]". iDestruct "Hh" as "[Hh _]".
    iDestruct (ghost_map_elem_ne with "Hx Hh") as %Hne. by destruct Hne.
  Qed.

  Lemma fif_ans_ok (l : list fdstate) (ret : mword 64) :
    uk_open_taint_fd γfd l ret -∗ ⌜bv_signed ret = -1 \/ 0 <= bv_signed ret⌝.
  Proof using .
    rewrite /uk_open_taint_fd. iIntros "[Hal | [%Hr _]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb _]". destruct Hb as (Hr & Hfdlt & _).
      iPureIntro. right. rewrite Hr bvs_moi_small; [lia |].
      unfold NOFILE in Hfdlt.
      assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia.
    - iPureIntro. left. rewrite Hr. exact fdev_m1.
  Qed.

  Lemma fif_open_taint (l : list fdstate) (ret : mword 64) (fdm : fdmap)
      (vs : gmap nat fdev) :
    length l = NSTD -> fif_ok fdm l vs ->
    file_taint c -∗ □ (file_taint c -∗ app_taint) -∗ ukn_pay N (-1) -∗
    uk_open_taint_fd γfd l ret -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗
    fif_taint (open_held fdm (bv_signed ret)).
  Proof using .
    intros Hlen Hok. iIntros "#Htn #Hk Hpay Hof Hhs".
    rewrite /uk_open_taint_fd.
    iDestruct "Hof" as "[Hal | [%Hr Hstd]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]". destruct Hb as (Hr & Hfdlt & _).
      assert (Hsig : bv_signed ret = Z.of_nat fd).
      { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
        assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia. }
      rewrite Hsig /open_held decide_True; [| lia].
      rewrite fif_hdls_hm.
      pose proof (fif_held_ok_fds fdm l vs Hok) as Hho.
      rewrite /fif_taint. iFrame "Htn Hk Hpay".
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + (* the lowest closed standard slot *)
        iDestruct (ualloc_std γfd l fd k0 _ Elc with "Hal") as "[%Hfk Hstd]". subst fd.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        pose proof (lookup_lt_Some _ _ _ Hk0) as Hk0l.
        iExists (<[k0 := FdOpen rd wr t]> l), (omap (fif_hf vs) fdm). iFrame "Hstd Hhs".
        iPureIntro. intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
        * apply elem_of_singleton in Hx as ->. split; [unfold NSTD, NOFILE in *; lia |].
          left. split; [unfold NSTD in *; lia |]. exists (FdOpen rd wr t).
          rewrite Nat2Z.id list_lookup_insert; [split; [done | discriminate] | exact Hk0l].
        * destruct (Hho x Hx) as [Hb Hc]. split; [exact Hb |].
          destruct Hc as [(Hs' & st' & Hl' & Hne') | Hc]; [left | by right].
          split; [exact Hs' |].
          destruct (decide (Z.to_nat x = k0)) as [-> | Hne].
          -- exists (FdOpen rd wr t). rewrite list_lookup_insert; [split; [done | discriminate] |].
             exact Hk0l.
          -- exists st'. rewrite list_lookup_insert_ne; [split; [exact Hl' | exact Hne'] |].
             congruence.
      + (* a fresh tail handle *)
        iDestruct (ualloc_hi γfd l fd (FdOpen rd wr t) Elc with "Hal")
          as "(%Hhi & Hstd & Hh)".
        iDestruct (fif_hm_fresh with "Hhs Hh") as "(%Hfr & Hhs & Hh)".
        iExists l, (<[Z.of_nat fd := FdOpen rd wr t]> (omap (fif_hf vs) fdm)). iFrame "Hstd".
        iSplit.
        * iPureIntro. intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
          -- apply elem_of_singleton in Hx as ->. split; [lia |]. right.
             split; [lia |]. rewrite lookup_insert. by eexists.
          -- destruct (Hho x Hx) as [Hb Hc]. split; [exact Hb |].
             destruct Hc as [Hc | (Hs & Hsm)]; [by left | right]. split; [exact Hs |].
             destruct (decide (x = Z.of_nat fd)) as [-> | Hne];
               [rewrite lookup_insert; by eexists | rewrite lookup_insert_ne; [exact Hsm | congruence]].
        * rewrite big_sepM_insert; [| exact Hfr]. rewrite Nat2Z.id. iFrame "Hh Hhs".
    - rewrite Hr fdev_m1 /open_held. case_decide; [lia |].
      iApply (fif_taint_of_fds fdm l vs Hok with "Htn Hk Hpay Hstd Hhs").
  Qed.

  (* [ei_exit]: the exit stub law, and the payload *)
  Lemma fif_exit_pay (s : Z) : ukn_pay N (-1) -∗ ex_obl N P s.
  Proof using HNc Hse.
    iIntros "Hpay" (h m avail) "_ Hcode Hrun".
    iPoseProof Hse as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "#Hi Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_exit).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64)).
      vm_compute; reflexivity. }
    iApply (wp_uk_ecall_exit N h1 m1 (mword_of_int (up_exit P + 2)) avail Hnum
              with "Hi [Hpay] Hrun").
    by rewrite (ukn_const_eq (N := N) (uexitst m1) (-1)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE FREE HANDLER: the taint pays any disciplined tree               *)
  (* ------------------------------------------------------------------- *)

  Lemma fif_app_sup : file_taint c -∗ app_sup.
  Proof using Heq.
    iIntros "#HT". rewrite /AppInv.app_sup. rewrite Heq. cbn [app_pred app_run].
    iApply (AppFile.file_sup_of_taint c r with "HT").
  Qed.

  Lemma fif_t_write (held : gset Z) (fd : Z) (bs : list (bv 8)) (K : Z -> iProp Σ) :
    fif_taint held -∗ (∀ x, fif_taint held -∗ K x) -∗ wr_obl N P fd bs K.
  Proof using Heq Hsw.
    iIntros "Ht HK" (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 Hcode Hsrc Hrun Hcont".
    iAssert (file_taint c ∗ □ (file_taint c -∗ app_taint))%I as "[#HT #Hkc]".
    { iDestruct "Ht" as "(#HT & #Hkc & _)". iFrame "HT Hkc". }
    iPoseProof (fif_app_sup with "HT") as "#Hsup".
    iPoseProof ("Hkc" with "HT") as "#Hk".
    iPoseProof (udepw_law_of_sup_write with "Hsup Hk") as "#Hlaw".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Hnum : usysno m1 = 16).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute; reflexivity. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_quiet N h1 m1 (mword_of_int (up_write P + 2)) 16 avail Hnum
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              Hal4 with "Hi Hrun [Hlaw]").
    { iApply (udepw_of_law with "Hlaw"). }
    iIntros (h2 ret) "Hrun". iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Ht] Hsrc Hrun").
    iApply ("HK" with "Ht").
  Qed.

  Lemma fif_t_read (held : gset Z) (fd : Z) (n : nat) (K : rd_ans -> iProp Σ) :
    fif_taint held -∗ (∀ x, fif_taint held -∗ K x) -∗ rd_obl N P fd n K.
  Proof using Heq Hsr.
    iIntros "Ht HK" (h m avail a f) "%Ha0 %Ha1 %Ha2 Hcode Hbuf Hrun Hcont".
    iAssert (file_taint c ∗ □ (file_taint c -∗ app_taint))%I as "[#HT #Hkc]".
    { iDestruct "Ht" as "(#HT & #Hkc & _)". iFrame "HT Hkc". }
    iPoseProof (fif_app_sup with "HT") as "#Hsup".
    iPoseProof ("Hkc" with "HT") as "#Hk".
    iPoseProof (udepw_law_of_sup_read with "Hsup Hk") as "#Hlaw".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_read).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute; reflexivity. }
    assert (Ha1r : m1 !!! Regidx (mword_of_int 11) = (mword_of_int a : mword 64)).
    { rewrite <- Ha1. exact (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 11)) _
                               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : bv_signed (subrange_vec_dec (m1 !!! Regidx (mword_of_int 12)) 31 0
                              : mword 32) = Z.of_nat n).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 12)) _
                            ltac:(vm_compute; discriminate)).
      exact Ha2. }
    iPoseProof Hsr as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_read P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_read N h1 m1 (mword_of_int (up_read P + 2)) a n f avail
              Hnum Ha1r Hcnt Hal4 with "Hi Hbuf Hrun [Hlaw]").
    { iApply (udepw_of_law with "Hlaw"). }
    iIntros (h2 ret gb) "%Hb Hbuf Hrun". iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret gb with "[%] [HK Ht] Hbuf Hrun"); [exact Hb |].
    iApply ("HK" with "Ht").
  Qed.

  Lemma fif_t_close (held : gset Z) (fd : Z) (K : Z -> iProp Σ) :
    fd ∈ held ->
    fif_taint held -∗ (∀ x, fif_taint (held ∖ {[fd]}) -∗ K x) -∗ cl_obl N P fd K.
  Proof using Hsc.
    intros Hin. iIntros "Ht HK" (h m avail) "%Ha0 Hcode Hrun Hcont".
    iDestruct "Ht" as "(#HT & #Hkc & Hpay & %l & %hm & Hstd & %Hok & Hhm)".
    iPoseProof ("Hkc" with "HT") as "#Hk".
    iPoseProof (udepw_law_of_sup_close with "Hk") as "#Hlaw".
    destruct (Hok fd Hin) as [[H0 Hlt] Hc].
    destruct (Z_of_nat_complete fd H0) as [k ->].
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_close).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64)).
      vm_compute; reflexivity. }
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx (mword_of_int 10))) = Z.of_nat k).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 10)) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    iPoseProof Hsc as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_close P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    destruct Hc as [(Hs & st & Hl & Hne) | (Hs & [st Hst])].
    - rewrite Nat2Z.id in Hl.
      iApply (wp_uk_ecall_close_std N h1 m1 (mword_of_int (up_close P + 2)) l k st avail
                Hnum Ha0r ltac:(unfold NSTD in *; lia) Hl Hne Hal4
                with "Hi Hrun [Hlaw] Hstd").
      { iApply udepw_cl_of_udepw. iApply (udepw_of_law with "Hlaw"). }
      iIntros (h2 ret) "_ Hstd Hrun". iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[-Hrun] Hrun").
      iApply "HK". rewrite /fif_taint. iFrame "HT Hkc Hpay".
      iExists (<[k := FdClosed]> l), hm. iFrame "Hstd Hhm". iPureIntro.
      intros x Hx. apply elem_of_difference in Hx as [Hx Hnx].
      destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
      destruct Hc as [(Hs' & st' & Hl' & Hne') | Hc]; [left | by right].
      split; [exact Hs' |]. exists st'. split; [| exact Hne'].
      rewrite list_lookup_insert_ne; [exact Hl' |].
      intros Heq0. apply Hnx. apply elem_of_singleton. lia.
    - iDestruct (big_sepM_delete _ _ _ _ Hst with "Hhm") as "[Hh Hhm]".
      rewrite Nat2Z.id.
      iApply (wp_uk_ecall_close N h1 m1 (mword_of_int (up_close P + 2)) k st avail
                Hnum Ha0r Hal4 with "Hi Hrun [Hlaw] Hh").
      { iApply udepw_cl_of_udepw. iApply (udepw_of_law with "Hlaw"). }
      iIntros (h2 ret) "_ Hrun". iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[-Hrun] Hrun").
      iApply "HK". rewrite /fif_taint. iFrame "HT Hkc Hpay".
      iExists l, (delete (Z.of_nat k) hm). iFrame "Hstd Hhm". iPureIntro.
      intros x Hx. apply elem_of_difference in Hx as [Hx Hnx].
      destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
      destruct Hc as [Hc | (Hs' & Hsm)]; [by left | right]. split; [exact Hs' |].
      rewrite lookup_delete_ne; [exact Hsm |].
      intros Heq0. apply Hnx. apply elem_of_singleton. done.
  Qed.

  Lemma fif_t_open (held : gset Z) (p : list (bv 8)) (mo : Z) (K : Z -> iProp Σ) :
    fif_taint held -∗
    (∀ x, ((⌜x = -1⌝ ∗ fif_taint held) ∨ (⌜0 <= x⌝ ∗ fif_taint ({[x]} ∪ held))) -∗ K x) -∗
    op_obl N P p mo K.
  Proof using Heq Hso.
    iIntros "Ht HK" (h m avail pv tx f) "%Hf %Ha0 %Ha1 Hcode Hp Hrun Hcont".
    iDestruct "Ht" as "(#HT & #Hkc & Hpay & %l & %hm & Hstd & %Hok & Hhm)".
    iPoseProof (fif_app_sup with "HT") as "#Hsup".
    iPoseProof (udepw_law_of_sup 15 ltac:(by left) with "Hsup") as "#Hlaw".
    iAssert (⌜length l = NSTD⌝ ∗ UserFd.ustd γfd l)%I with "[Hstd]" as "[%Hlen Hstd]".
    { rewrite /UserFd.ustd. iDestruct "Hstd" as "[%H $]". done. }
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_open).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64)).
      vm_compute; reflexivity. }
    iPoseProof Hso as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_open P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_open N h1 m1 (mword_of_int (up_open P + 2)) l avail Hnum Hal4
              with "Hi Hrun [Hlaw] Hstd").
    { iApply (udepw_of_law with "Hlaw"). }
    iIntros (h2 ret) "Hans Hrun". iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
    iDestruct "Hans" as "[Hal | [%Hr Hstd]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]". destruct Hb as (Hr & Hfdlt & _).
      assert (Hsig : bv_signed ret = Z.of_nat fd).
      { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
        assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia. }
      iApply ("Hcont" $! h3 ret with "[%] [-Hp Hrun] Hp Hrun").
      { right. split; [rewrite Hsig; unfold NOFILE in *; lia | rewrite Hsig; exact Hr]. }
      rewrite Hsig. iApply "HK". iRight. iSplit; [iPureIntro; lia |].
      rewrite /fif_taint. iFrame "HT Hkc Hpay".
      rewrite /ualloc /ualloc_at /ustd_after.
      iDestruct "Hal" as "[Hstd Hat]".
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + iDestruct "Hat" as %->.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        assert (Hk0l : (k0 < NSTD)%nat)
          by (rewrite <- Hlen; exact (lookup_lt_Some _ _ _ Hk0)).
        iExists (<[k0 := FdOpen rd wr t]> l), hm. iFrame "Hstd Hhm". iPureIntro.
        intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
        * apply elem_of_singleton in Hx as ->. split; [unfold NSTD, NOFILE in *; lia |].
          left. split; [unfold NSTD in *; lia |]. exists (FdOpen rd wr t).
          rewrite Nat2Z.id list_lookup_insert; [split; [done | discriminate] |].
          rewrite <- Hlen in Hk0l. rewrite Hlen. unfold NSTD in *; lia.
        * destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
          destruct Hc as [(Hs' & st' & Hl' & Hne') | Hc]; [left | by right].
          split; [exact Hs' |].
          destruct (decide (Z.to_nat x = k0)) as [-> | Hne].
          -- exists (FdOpen rd wr t). rewrite list_lookup_insert; [split; [done | discriminate] |].
             exact (lookup_lt_Some _ _ _ Hk0).
          -- exists st'. rewrite list_lookup_insert_ne; [split; [exact Hl' | exact Hne'] |].
             congruence.
      + iDestruct "Hat" as "[%Hhi Hh]".
        iDestruct (fif_hm_fresh with "Hhm Hh") as "(%Hfr & Hhm & Hh)".
        iExists l, (<[Z.of_nat fd := FdOpen rd wr t]> hm). iFrame "Hstd". iSplit.
        * iPureIntro. intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
          -- apply elem_of_singleton in Hx as ->. split; [unfold NOFILE in *; lia |].
             right. split; [lia |]. rewrite lookup_insert. by eexists.
          -- destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
             destruct Hc as [Hc | (Hs' & Hsm)]; [by left | right]. split; [exact Hs' |].
             destruct (decide (x = Z.of_nat fd)) as [-> |];
               [rewrite lookup_insert; by eexists | rewrite lookup_insert_ne; [exact Hsm | congruence]].
        * rewrite big_sepM_insert; [| exact Hfr]. rewrite Nat2Z.id. iFrame "Hh Hhm".
    - iApply ("Hcont" $! h3 ret with "[%] [-Hp Hrun] Hp Hrun").
      { left. rewrite Hr. exact fdev_m1. }
      rewrite Hr fdev_m1. iApply "HK". iLeft. iSplit; [done |].
      rewrite /fif_taint. iFrame "HT Hkc Hpay". iExists l, hm. by iFrame.
  Qed.

  (* ...and by coinduction, the whole tree *)
  Definition fif_tinv (t : proc) : iProp Σ :=
    (∃ held : gset Z, ⌜safe_fds held t⌝ ∗ fif_taint held)%I.

  Lemma fif_taint_pays (held : gset Z) (t : proc) :
    safe_fds held t -> fif_taint held -∗ tree_pay N P t.
  Proof using Heq HNc Hsr Hsw Hso Hsc Hse.
    intros Hs. iIntros "Ht".
    iApply (tree_pay_coind N P fif_tinv with "[] [Ht]"); last first.
    { iExists held. by iFrame. }
    iIntros "!>" (t') "(%hd & %Hs' & Ht)".
    apply safe_fds_unfold in Hs'.
    destruct t' as [v | t'' | e k]; [destruct v | |].
    - simpl in Hs' |- *. iExists hd. by iFrame.
    - destruct e as [p mo | fd | fd n | fd bs | s]; simpl in Hs' |- *.
      + destruct Hs' as [Hso' Hsm].
        iApply (fif_t_open hd p mo with "Ht").
        iIntros (x) "[[-> Ht] | [%Hx Ht]]".
        * iExists hd. by iFrame.
        * iExists ({[x]} ∪ hd). iFrame "Ht". iPureIntro. by apply Hso'.
      + destruct Hs' as [Hin Hk].
        iApply (fif_t_close hd fd with "Ht"); [exact Hin |].
        iIntros (x) "Ht". iExists (hd ∖ {[fd]}). iFrame "Ht". iPureIntro. apply Hk.
      + destruct Hs' as [_ Hk].
        iApply (fif_t_read hd fd n with "Ht").
        iIntros (x) "Ht". iExists hd. iFrame "Ht". iPureIntro. apply Hk.
      + iApply (fif_t_write hd fd bs with "Ht").
        iIntros (x) "Ht". iExists hd. iFrame "Ht". iPureIntro. apply Hs'.
      + iDestruct "Ht" as "(_ & _ & Hpay & _)". iApply (fif_exit_pay with "Hpay").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE LAWS                                                            *)
  (* ------------------------------------------------------------------- *)

  (* [ei_write] at the console: the device's slot is a console row *)
  Lemma fif_write (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    fif_fds fdm -∗ fif_out d alts -∗
    ((fif_fds fdm -∗ fif_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, fif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hcons Hsw HPc.
    intros _ Hfd Ha Hpre. iIntros "Hfds [Htk Hout] HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (cons_write_gl file_lm (file_params g) (file_links g)
              (LINKS_pers := file_links_persistent g)
              (file_links_gl_w g) (file_links_gl_blk g) (file_links_gl_taint g)
              N P Hsw l k rb alts a bs K
              ltac:(unfold NSTD in *; lia) Hrow Ha Hpre with "Hstd Hout").
    iIntros "Hstd Hout". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[-Hout Htk] [$Htk $Hout]").
    iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs He". by iPureIntro.
  Qed.

  (* a ZERO-LENGTH write at the console: [UkConsOut.cons_write]'s walk at
     no bytes, where the chain is its own stop and the device comes back
     unnarrowed *)
  Lemma fif_cons_nil (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ cons_dev file_lm (file_params g) (file_links g) alts -∗
    (UserFd.ustd γfd l -∗ cons_dev file_lm (file_params g) (file_links g) alts -∗ K 0) -∗
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
              (xfam_wr (fun _ : nat => (cons_dev file_lm (file_params g) (file_links g) alts ∗ emp)%I)
                 (ukn_pay N))
              l tx dq 0 f Hsys Hal with "Hec Hrun [Hd] Hstd [Hsrc]").
    { iApply (uwrite_chain_sup_ret N (fun _ : nat => cons_dev file_lm (file_params g) (file_links g) alts)
                emp%I _ _ l fd rb CONSOLE Hi0 Hfd Hl).
      iIntros (Mh pm sz) "Hheap". iFrame "Hheap". iSplitR; [done |].
      rewrite Hcnt. cbn [cons_out_chain]. iExact "Hd". }
    { rewrite Ham1. iExact "Hsrc". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun _ : nat => (cons_dev file_lm (file_params g) (file_links g) alts ∗ emp)%I)
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

  (* a ZERO-LENGTH write at the file a redirect holds: the row is the held
     inode slot the registry names, and [UkFileDev.file_write_nil] answers
     0 or -1 with nothing lent -- the cursor is not even looked at *)
  Lemma fif_file_nil (fdm : fdmap) (fd : Z) (d : nat) (cs : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_outm d cs -∗
    ((fif_fds fdm -∗ fif_outm d cs -∗ K 0) ∧ (fif_fds fdm -∗ fif_outm d cs -∗ K (-1))) -∗
    wr_obl N P fd [] K.
  Proof using Hsw.
    intros Hfd. iIntros "Hfds Hout HK".
    iDestruct "Hout" as (i γo) "[Htk Hout]".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (file_write_nil N P Hsw k l rb i γo K ltac:(unfold NSTD in *; lia) Hrow with "Hstd").
    iSplit; iIntros "Hstd".
    - iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hout Htk] [Htk Hout]").
      + iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs He". by iPureIntro.
      + iExists i, γo. iFrame "Htk Hout".
    - iDestruct "HK" as "[_ HK]". iApply ("HK" with "[-Hout Htk] [Htk Hout]").
      + iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs He". by iPureIntro.
      + iExists i, γo. iFrame "Htk Hout".
  Qed.

  (* [ei_write_m] at the file a redirect holds: chunk [b] of the line *)
  Lemma fif_write_m (fdm : fdmap) (fd : Z) (d : nat) (rest : list (list (bv 8)))
      (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_outm d (bs :: rest) -∗
    ((fif_fds fdm -∗ fif_outm d rest -∗ K (Z.of_nat (length bs)))
     ∧ (fif_fds fdm -∗ fif_outm d rest -∗ K (-1))
     ∧ (∀ x, fif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Heq Hsw.
    intros Hne Hfd. iIntros "Hfds Hout HK".
    iDestruct "Hout" as (i γo) "[Htk Hout]".
    iDestruct "Hout" as (ws b) "(%Hch & %Hwok & Hout)".
    destruct (fif_drop_cons _ _ _ _ (eq_sym Hch)) as (Hb & Hbs & Hrest).
    pose proof Hwok as (Hi1 & Hi2 & Hi3 & Hi4 & Hlm).
    assert (Hbl : (length bs <= EchoDisc.line_max)%nat).
    { rewrite <- Hbs. apply (proj1 (Forall_lookup _ _) Hlm b).
      apply list_lookup_lookup_total_lt. exact Hb. }
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & #Hm)".
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (file_write c r Heq N P Hsw k l rb i γo ws b b bs K
              ltac:(unfold NSTD in *; lia) Hrow Hb ltac:(lia) Hbs
              ltac:(destruct bs; [done | simpl; lia]) Hbl Hi1 Hi2 Hi3 Hi4
              with "Hbr Hinv Hstd Hout").
    iSplit.
    - iIntros "Hstd Hout". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[Hstd Hcwd Hpay Hpool Htoks Hhs] [Htk Hout]").
      + iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs Hbr Hrb Hinv Hm". by iPureIntro.
      + iExists i, γo. iFrame "Htk". iExists ws, (S b). iFrame "Hout". by iPureIntro.
    - iIntros "Hstd Hout". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[Hstd Hcwd Hpay Hpool Htoks Hhs] [Htk Hout]").
      + iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs Hbr Hrb Hinv Hm". by iPureIntro.
      + iExists i, γo. iFrame "Htk". iExists ws, (S b). iFrame "Hout". by iPureIntro.
  Qed.

  (* [ei_read] at an input: the token names the inode and the offset, and
     whether the descriptor is a tail handle or a standard slot the ledger
     holds *)
  Lemma fif_read (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        fif_fds fdm -∗ fif_in d S' -∗ K (RdBytes cb))
     ∧ (∀ x, fif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Heq Hsr.
    intros Hn Hfd. iIntros "Hfds Hin HK".
    iDestruct "Hin" as (s i γo) "[Htk Hin]". iDestruct "Hin" as (q content) "Hin".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hs. rewrite Hv in Hs. simpl in Hs.
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & %jo & #Hm)".
    destruct (Z_of_nat_complete fd H0) as [k ->].
    destruct s.
    - (* a standard slot: the ledger is the handle *)
      destruct Hs as (Hsk & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_read_std c r Heq N P Hsr k l false i γo q jo content Sin n K
                ltac:(unfold NSTD in *; lia) Hrow Hn with "Hbr Hrb Hm Hinv Hstd Hin").
      iSplit.
      + iIntros (cb S') "%Hc Hstd Hin". iDestruct "HK" as "[HK _]".
        iApply ("HK" $! cb S' with "[%] [-Hin Htk] [Htk Hin]"); [exact Hc | |].
        * iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs Hbr Hrb Hinv".
          iSplit; [by iPureIntro |]. by iExists jo.
        * iExists true, i, γo. iFrame "Htk". iExists q, content. iExact "Hin".
      + iIntros (x) "#Htn Hstd Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
        iApply (fif_taint_of_fds fdm l vs Hok with "Htn Hrb Hpay Hstd Hhs").
    - (* a tail handle *)
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hfd with "Hhs") as "[Hh Hcl]".
      iEval (rewrite /fif_hdl Hv) in "Hh". iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_read c r Heq N P Hsr k false i γo q jo content Sin n K
                ltac:(lia) Hn with "Hbr Hrb Hm Hinv Hh Hin").
      iSplit.
      + iIntros (cb S') "%Hc Hh Hin". iDestruct "HK" as "[HK _]".
        iApply ("HK" $! cb S' with "[%] [-Hin Htk] [Htk Hin]"); [exact Hc | |].
        * iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hbr Hrb Hinv".
          iSplit; [by iPureIntro |].
          iSplitL; [| by iExists jo].
          iApply "Hcl". rewrite /fif_hdl Hv Nat2Z.id. iExact "Hh".
        * iExists false, i, γo. iFrame "Htk". iExists q, content. iExact "Hin".
      + iIntros (x) "#Htn Hh Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
        iAssert ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))%I with "[Hh Hcl]" as "Hhs".
        { iApply "Hcl". rewrite /fif_hdl Hv Nat2Z.id. iExact "Hh". }
        iApply (fif_taint_of_fds fdm l vs Hok with "Htn Hrb Hpay Hstd Hhs").
  Qed.

  (* [ei_open] for `f` present: the descriptor the LEDGER names -- the
     lowest closed standard slot, else a fresh tail handle -- with the
     token of a fresh device out of the pool; or -1; or the taint *)
  Lemma fif_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path content : list (bv 8)) (K : Z -> iProp Σ) :
    path ∈ paths -> files path = Some content ->
    fif_fds fdm -∗ fif_filesr files paths -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
        (∀ d : nat, ⌜forall fd', fdm !! fd' <> Some d⌝ -∗
           fif_fds (<[fd := d]> fdm) ∗ fif_in d content) -∗
        fif_filesr files paths -∗ K fd)
     ∧ (fif_fds fdm -∗ fif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ fif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path 0 K.
  Proof using Heq Hso.
    intros Hp Hf. iIntros "Hfds Hfiles HK".
    iDestruct "Hfiles" as "[%Hpaths Hfiles]". pose proof (Hpaths path Hp) as ->.
    iDestruct "Hfiles" as (s q) "[%Hfs Hd]".
    rewrite Hf in Hfs.
    destruct s as [[i content'] |]; [| discriminate]. simpl in Hfs. injection Hfs as <-.
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & #Hm)".
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen.
    iAssert (fdq r (q / 2) (Some (i, content)) ∗ fdq r (q / 2) (Some (i, content)))%I
      with "[Hd]" as "[Hd1 Hd2]".
    { iApply fdq_split. by rewrite Qp.div_2. }
    iApply (file_open_present c r Heq N P Hso l FsImg.ROOTINO (q / 2) (q / 2) i content K
              eq_refl with "Hinv Hstd Hcwd Hd1 Hd2").
    iSplit; [| iSplit].
    - (* the handle, where the ledger says the allocation landed *)
      iIntros (fd γo) "%Hfdlt Hal Hcwd Hin Hd1".
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + (* the lowest closed standard slot: its row in the ledger *)
        iDestruct (ualloc_std γfd l fd k0 _ Elc with "Hal") as "[%Hfk Hstd]". subst fd.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        pose proof (fif_ok_closed_fresh fdm l vs k0 Hok Hlen Hk0) as Hnb.
        iMod (own_update with "Hpool") as "Hpool";
          [apply (fif_pool_update _ w (FDIn true i γo)) |].
        iModIntro.
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! (Z.of_nat k0) with "[%] [%] [-Hd1] [Hd1]"); [lia | exact Hnb | |].
        * iIntros (d) "%Hfr".
          assert (Hvd : vs !! d = None).
          { apply not_elem_of_dom. pose proof Hok as (_ & _ & H3 & _).
            rewrite H3. intros (fd' & Hfd'). exact (Hfr fd' Hfd'). }
          assert (Hdn : d ∉ dom vs) by (by apply not_elem_of_dom).
          iEval (rewrite (fif_pool_own_take _ _ d Hdn) fif_tok_halves) in "Hpool".
          iDestruct "Hpool" as "(Hpool & Htk1 & Htk2)".
          iSplitR "Htk2 Hin".
          -- iExists (<[k0 := FdOpen true false (FdInode i γo OffHeld)]> l),
               (<[d := FDIn true i γo]> vs), (fun _ => FDIn true i γo).
             iFrame "Hstd Hcwd Hpay Hbr Hrb Hinv Hm".
             iSplit.
             { iPureIntro. apply fif_ok_open_std; [exact Hok | exact Hlen | exact Hk0 | exact Hfr]. }
             iSplitL "Hpool"; [by rewrite dom_insert_L |].
             iSplitL "Htoks Htk1".
             { rewrite big_sepM_insert; [| exact Hvd]. iFrame "Htk1 Htoks". }
             rewrite big_sepM_insert; [| exact Hnb]. iSplitR.
             { rewrite /fif_hdl lookup_insert. done. }
             iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
             rewrite lookup_insert_ne; [iExact "Hx" |]. intros ->. exact (Hfr fd' Hfd').
          -- iExists true, i, γo. iFrame "Htk2". iExists (q / 2)%Qp, content. iExact "Hin".
        * iSplit; [by iPureIntro |]. iExists (Some (i, content)), (q / 2)%Qp. iFrame "Hd1".
          iPureIntro. rewrite Hf. reflexivity.
      + (* a fresh tail handle *)
        iDestruct (ualloc_hi γfd l fd _ Elc with "Hal") as "(%Hhi & Hstd & Hh)".
        iDestruct (fif_fresh_fd fdm l vs fd with "Hhs Hh") as "(%Hnb & Hhs & Hh)";
          [exact Hok | lia |].
        iMod (own_update with "Hpool") as "Hpool";
          [apply (fif_pool_update _ w (FDIn false i γo)) |].
        iModIntro.
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! (Z.of_nat fd) with "[%] [%] [-Hd1] [Hd1]"); [lia | exact Hnb | |].
        * iIntros (d) "%Hfr".
          assert (Hvd : vs !! d = None).
          { apply not_elem_of_dom. pose proof Hok as (_ & _ & H3 & _).
            rewrite H3. intros (fd' & Hfd'). exact (Hfr fd' Hfd'). }
          assert (Hdn : d ∉ dom vs) by (by apply not_elem_of_dom).
          iEval (rewrite (fif_pool_own_take _ _ d Hdn) fif_tok_halves) in "Hpool".
          iDestruct "Hpool" as "(Hpool & Htk1 & Htk2)".
          iSplitR "Htk2 Hin".
          -- iExists l, (<[d := FDIn false i γo]> vs), (fun _ => FDIn false i γo).
             iFrame "Hstd Hcwd Hpay Hbr Hrb Hinv Hm".
             iSplit.
             { iPureIntro. apply fif_ok_open; [exact Hok | exact (conj Hhi Hfdlt) | exact Hnb | exact Hfr]. }
             iSplitL "Hpool"; [by rewrite dom_insert_L |].
             iSplitL "Htoks Htk1".
             { rewrite big_sepM_insert; [| exact Hvd]. iFrame "Htk1 Htoks". }
             rewrite big_sepM_insert; [| exact Hnb]. iSplitL "Hh".
             { rewrite /fif_hdl lookup_insert Nat2Z.id. iExact "Hh". }
             iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
             rewrite lookup_insert_ne; [iExact "Hx" |]. intros ->. exact (Hfr fd' Hfd').
          -- iExists false, i, γo. iFrame "Htk2". iExists (q / 2)%Qp, content. iExact "Hin".
        * iSplit; [by iPureIntro |]. iExists (Some (i, content)), (q / 2)%Qp. iFrame "Hd1".
          iPureIntro. rewrite Hf. reflexivity.
    - (* -1 *)
      iIntros "Hstd Hcwd Hd1 Hd2". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[Hstd Hcwd Hpay Hpool Htoks Hhs] [Hd1 Hd2]").
      + iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs Hbr Hrb Hinv Hm". by iPureIntro.
      + iSplit; [by iPureIntro |]. iExists (Some (i, content)), (q / 2 + q / 2)%Qp.
        iSplit; [iPureIntro; rewrite Hf; reflexivity |].
        iApply (fdq_join with "Hd1 Hd2").
    - (* the taint *)
      iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ [_ HK]]".
      iDestruct (fif_ans_ok with "Hof") as %Hans.
      iApply ("HK" with "[%]"); [exact Hans |].
      iApply (fif_open_taint l ret fdm vs Hlen Hok with "Htn Hrb Hpay Hof Hhs").
  Qed.

  (* [ei_open_absent] for `f`, at any mode that does not create (the
     truncate's permit at an absent `f` is the dead walk's cursor, paid
     out of the taint: [UkFileDev.file_open_absent], lane TRUNC-PERMIT) *)
  Lemma fif_open_absent_nt (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    fif_fds fdm -∗ fif_filesr files paths -∗
    ((fif_fds fdm -∗ fif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ fif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using Heq Hso.
    intros Hp Hcm Hf. iIntros "Hfds Hfiles HK".
    iDestruct "Hfiles" as "[%Hpaths Hfiles]". pose proof (Hpaths path Hp) as ->.
    iDestruct "Hfiles" as (s q) "[%Hfs Hd]".
    assert (Hs : s = None).
    { rewrite Hf in Hfs. destruct s; [discriminate | reflexivity]. }
    subst s.
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & #Hm)".
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen.
    iApply (file_open_absent c r Heq N P Hso l FsImg.ROOTINO q m K eq_refl
              (fif_om_create m Hcm) with "Hinv Hstd Hcwd Hd").
    iSplit.
    - iIntros "Hstd Hcwd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[Hstd Hcwd Hpay Hpool Htoks Hhs] [Hd]").
      + iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs Hbr Hrb Hinv Hm". by iPureIntro.
      + iSplit; [by iPureIntro |]. iExists None, q. iFrame "Hd". by iPureIntro.
    - iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ HK]".
      iDestruct (fif_ans_ok with "Hof") as %Hans.
      iApply ("HK" with "[%]"); [exact Hans |].
      iApply (fif_open_taint l ret fdm vs Hlen Hok with "Htn Hrb Hpay Hof Hhs").
  Qed.

  (* the ledger after a close of a device's last descriptor, rebuilt: the
     device's token home to the pool, the descriptor's handle (if a tail
     one) gone with it, the ledger [l'] agreeing with [l] at every other
     descriptor's slot (the same [l], or the slot closed) *)
  Lemma fif_fds_close (fdm : fdmap) (fd : Z) (d : nat) (v : fdev) (l l' : list fdstate)
      (vs : gmap nat fdev) (w : nat -> fdev) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> fif_ok fdm l vs -> vs !! d = Some v ->
    (forall fd' d', fd' <> fd -> fdm !! fd' = Some d' ->
       l' !! Z.to_nat fd' = l !! Z.to_nat fd') ->
    UserFd.ustd γfd l' -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    own γreg (fif_pool (dom vs) w) -∗
    ([∗ map] d ↦ v ∈ delete d vs, fif_tok d (1/2) v) -∗ fif_tok d 1 v -∗
    ([∗ map] fd ↦ d ∈ delete fd fdm, fif_hdl fd (vs !! d)) -∗ fif_env -∗
    fif_fds (delete fd fdm).
  Proof using .
    intros Hfd Hns Hok Hv Hl. iIntros "Hstd Hcwd Hpay Hpool Htoks Htk Hhs #He".
    pose proof (fif_ok_close fdm l vs fd d Hok Hfd Hns) as Hok'.
    pose proof (fif_not_shared fdm fd d Hns) as Hn.
    assert (Hdd : d ∈ dom vs) by (apply elem_of_dom; by eexists).
    iDestruct (fif_pool_give vs w d v Hdd with "Hpool Htk") as "Hpool".
    iExists l', (delete d vs), _. iFrame "Hstd Hcwd Hpay Hpool Htoks He".
    iSplit.
    { iPureIntro. apply (fif_ok_ledger (delete fd fdm) l l' (delete d vs) Hok').
      intros fd' d' Hfd'. apply lookup_delete_Some in Hfd' as [Hne Hfd'].
      exact (Hl fd' d' (not_eq_sym Hne) Hfd'). }
    iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
    rewrite lookup_delete_ne; [iExact "Hx" |].
    intros ->. apply lookup_delete_Some in Hfd' as [Hne Hfd'].
    exact (Hn fd' (not_eq_sym Hne) Hfd').
  Qed.

  (* [ei_close] of an input's descriptor: the handle (or the ledger's
     slot), the deed's fraction home to the files, the token home to the
     pool *)
  Lemma fif_close_in (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8))
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d ->
    fif_fds fdm -∗ fif_filesr files paths -∗ fif_in d Sin -∗
    ((fif_fds (delete fd fdm) -∗ fif_filesr files paths -∗ K 0)
     ∧ (∀ y, fif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns. iIntros "Hfds Hfiles Hin HK".
    iDestruct "Hin" as (s i γo) "[Htk Hin]". iDestruct "Hin" as (q content) "Hin".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hs. rewrite Hv in Hs. simpl in Hs.
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[Hh Hhs]".
    iEval (rewrite /fif_hdl Hv) in "Hh".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (fif_tok d 1 (FDIn s i γo)) with "[Htk Htk']" as "Htk".
    { rewrite fif_tok_halves. iFrame "Htk Htk'". }
    destruct (Z_of_nat_complete fd H0) as [k ->].
    iDestruct "Hfiles" as "[%Hpaths Hfiles]". iDestruct "Hfiles" as (s' q') "[%Hfs Hd']".
    iDestruct "HK" as "[HK _]".
    destruct s.
    - (* a standard slot: the ledger's row goes to [FdClosed] *)
      destruct Hs as (Hsk & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_in_std r N P Hsc k l false i γo q content Sin K
                ltac:(unfold NSTD in *; lia) Hrow with "Hstd Hin").
      iIntros "Hstd Hd".
      iApply ("HK" with "[-Hd Hd'] [Hd Hd']").
      + iApply (fif_fds_close fdm (Z.of_nat k) d (FDIn true i γo) l (<[k := FdClosed]> l) vs w
                  Hfd Hns Hok Hv with "Hstd Hcwd Hpay Hpool Htoks Htk Hhs He").
        intros fd' d' Hne Hfd'. destruct (H1 fd' d' Hfd') as [H0' _].
        apply list_lookup_insert_ne. exact (fif_slot_ne k fd' H0' Hne).
      + iSplit; [by iPureIntro |]. iExists s', (q' + q)%Qp. iSplit; [by iPureIntro |].
        iApply (fdq_join with "Hd' Hd").
    - (* a tail handle *)
      iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_close_in r N P Hsc k false i γo q content Sin K with "Hh Hin").
      iIntros "Hd".
      iApply ("HK" with "[-Hd Hd'] [Hd Hd']").
      + iApply (fif_fds_close fdm (Z.of_nat k) d (FDIn false i γo) l l vs w
                  Hfd Hns Hok Hv with "Hstd Hcwd Hpay Hpool Htoks Htk Hhs He").
        intros; reflexivity.
      + iSplit; [by iPureIntro |]. iExists s', (q' + q)%Qp. iSplit; [by iPureIntro |].
        iApply (fdq_join with "Hd' Hd").
  Qed.

  (* ...of a STANDARD stream of any other kind (the console, the file a
     redirect holds): the ledger's slot to [FdClosed], the device dropped,
     the token home *)
  Lemma fif_close_std_dev (fdm : fdmap) (fd : Z) (d : nat) (v : fdev) (l : list fdstate)
      (vs : gmap nat fdev) (w : nat -> fdev) (st : fdstate) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> fif_ok fdm l vs -> vs !! d = Some v ->
    0 <= fd -> fd < Z.of_nat NSTD -> l !! Z.to_nat fd = Some st -> st <> FdClosed ->
    fdst_nopipe st ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    own γreg (fif_pool (dom vs) w) -∗
    ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) -∗ fif_tok d (1/2) v -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ fif_env -∗
    (fif_fds (delete fd fdm) -∗ K 0) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns Hok Hv H0 Hs Hl Hne Hnp.
    iIntros "Hstd Hcwd Hpay Hpool Htoks Htk Hhs #He HK".
    pose proof Hok as (H1 & _).
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[_ Hhs]".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (fif_tok d 1 v) with "[Htk Htk']" as "Htk".
    { rewrite fif_tok_halves. iFrame "Htk Htk'". }
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hl.
    iApply (file_close_std N P Hsc k l st K ltac:(unfold NSTD in *; lia) Hl Hne Hnp
              with "Hstd").
    iIntros "Hstd". iApply "HK".
    iApply (fif_fds_close fdm (Z.of_nat k) d v l (<[k := FdClosed]> l) vs w Hfd Hns Hok Hv
              with "Hstd Hcwd Hpay Hpool Htoks Htk Hhs He").
    intros fd' d' Hne' Hfd'. destruct (H1 fd' d' Hfd') as [H0' _].
    apply list_lookup_insert_ne. exact (fif_slot_ne k fd' H0' Hne').
  Qed.

  Lemma fif_exit (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    (forall fd d, fdm !! fd = Some d -> d ∈ ds) ->
    fif_fds fdm -∗ fif_filesr files paths -∗ ([∗ set] d ∈ ds, fif_dev d (dv d)) -∗
    ex_obl N P s.
  Proof using HNc Hse.
    intros _ _. iIntros "Hfds _ _".
    iDestruct "Hfds" as (l vs w) "(_ & _ & Hpay & _)".
    iApply (fif_exit_pay with "Hpay").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE FIELDS THE KERNEL REFUSES (the header's list)                   *)
  (* ------------------------------------------------------------------- *)

  (* each gap is a NAMED proposition, so that an instance section (SS4,
     echo's) can assume it at its own program by name *)
  Definition fif_nil_in_law : Prop :=
    forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (K : Z -> iProp Σ),
    fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_in d Sin -∗
    ((fif_fds fdm -∗ fif_in d Sin -∗ K 0) ∧ (fif_fds fdm -∗ fif_in d Sin -∗ K (-1))
     ∧ (∀ y, fif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.

  Hypothesis Hnil_in : fif_nil_in_law.


  (* the laws assembled from their cases *)
  Lemma fif_write_nil (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_dev d x -∗
    ((fif_fds fdm -∗ fif_dev d x -∗ K 0) ∧ (fif_fds fdm -∗ fif_dev d x -∗ K (-1))
     ∧ (∀ y, fif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.
  Proof using Hsw HPc Hnil_in.
    intros Hfd. iIntros "Hfds Hd HK".
    destruct x as [alts | | cs | | Sin | | | | |]; simpl; try (iDestruct "Hd" as "[]").
    - (* the console *)
      iDestruct "Hd" as "[Htk Hd]".
      iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
      destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
      iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst v.
      pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
      pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
      destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
      iApply (fif_cons_nil l k rb alts K ltac:(unfold NSTD in *; lia) Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [$Htk $Hd]").
      iExists l, vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs He". by iPureIntro.
    - (* the file held for writing *)
      iApply (fif_file_nil fdm fd d cs K Hfd with "Hfds Hd").
      iSplit; [iDestruct "HK" as "[HK _]" | iDestruct "HK" as "[_ [HK _]]"]; iExact "HK".
    - (* an input: the header's list *)
      iApply (Hnil_in fdm fd d Sin K Hfd with "Hfds Hd HK").
  Qed.

  Lemma fif_open_absent (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    fif_fds fdm -∗ fif_filesr files paths -∗
    ((fif_fds fdm -∗ fif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ fif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using Heq Hso.
    exact (fif_open_absent_nt fdm files paths path m K).
  Qed.

  Lemma fif_close (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d ->
    fif_fds fdm -∗ fif_filesr files paths -∗ fif_dev d x -∗
    ((fif_fds (delete fd fdm) -∗ fif_filesr files paths -∗ K 0)
     ∧ (∀ y, fif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns.
    iIntros "Hfds Hfiles Hdev HK".
    destruct x as [alts | alts | cs | | Sin | Sin | | | |]; simpl;
      try (iDestruct "Hdev" as "[]").
    - (* the console: a standard slot, its row a console row *)
      iDestruct "Hdev" as "[Htk _]".
      iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
      destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
      iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst v. pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 _].
      pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
      iApply (fif_close_std_dev fdm fd d FDCons l vs w _ K Hfd Hns Hok Hv H0 Hs Hrow
                ltac:(discriminate) I with "Hstd Hcwd Hpay Hpool Htoks Htk Hhs He").
      iIntros "Hfds". iDestruct "HK" as "[HK _]". iApply ("HK" with "Hfds Hfiles").
    - (* the file a redirect holds: a standard slot, its row the held one *)
      iDestruct "Hdev" as (i γo) "[Htk _]".
      iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
      destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
      iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst v. pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 _].
      pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
      iApply (fif_close_std_dev fdm fd d (FDFile i γo) l vs w _ K Hfd Hns Hok Hv H0 Hs Hrow
                ltac:(discriminate) I with "Hstd Hcwd Hpay Hpool Htoks Htk Hhs He").
      iIntros "Hfds". iDestruct "HK" as "[HK _]". iApply ("HK" with "Hfds Hfiles").
    - iApply (fif_close_in fdm fd d Sin files paths K Hfd Hns with "Hfds Hfiles Hdev HK").
  Qed.

  Lemma fif_close_shared (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> fd_shared fdm fd d ->
    fif_fds fdm -∗
    ((fif_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, fif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hsh. iIntros "Hfds HK".
    iDestruct "Hfds" as (l vs w) "(Hstd & Hcwd & Hpay & %Hok & Hpool & Htoks & Hhs & #He)".
    destruct (fif_ok_lookup _ _ _ _ _ Hok Hfd) as [v Hv].
    pose proof Hok as (H1 & H2 & _ & H4). destruct (H1 fd d Hfd) as [H0 _].
    pose proof (H2 fd d Hfd) as Hr. rewrite Hv in Hr.
    pose proof (fif_ok_close_shared fdm l vs fd d Hok Hfd Hsh) as Hok'.
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[_ Hhs]".
    (* a shared descriptor is a standard stream of any kind but a tail
       input, which has one descriptor *)
    assert (Hrow : exists st, fd < Z.of_nat NSTD /\ l !! Z.to_nat fd = Some st
                              /\ st <> FdClosed /\ fdst_nopipe st).
    { destruct v as [| i γo | [|] i γo].
      - destruct Hr as (Hs & rb & Hl). exists (FdOpen rb true (FdDevice CONSOLE)).
        split_and!; [exact Hs | exact Hl | discriminate | exact I].
      - destruct Hr as (Hs & rb & Hl). exists (FdOpen rb true (FdInode i γo OffHeld)).
        split_and!; [exact Hs | exact Hl | discriminate | exact I].
      - destruct Hr as (Hs & Hl). exists (FdOpen true false (FdInode i γo OffHeld)).
        split_and!; [exact Hs | exact Hl | discriminate | exact I].
      - exfalso. destruct Hsh as (fd' & Hin' & Hfd').
        apply elem_of_dom in Hin' as [d'' Hd'']. apply lookup_delete_Some in Hd'' as [Hne _].
        exact (Hne (H4 fd fd' d false i γo Hfd Hfd' Hv)). }
    destruct Hrow as (st & Hs & Hl & Hne & Hnp).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hl.
    iApply (file_close_std N P Hsc k l st K ltac:(unfold NSTD in *; lia) Hl Hne Hnp
              with "Hstd").
    iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
    iExists (<[k := FdClosed]> l), vs, w. iFrame "Hstd Hcwd Hpay Hpool Htoks Hhs He".
    iPureIntro. apply (fif_ok_ledger (delete (Z.of_nat k) fdm) l _ vs Hok').
    intros fd' d' Hfd'. apply lookup_delete_Some in Hfd' as [Hne' Hfd'].
    destruct (H1 fd' d' Hfd') as [H0' _].
    apply list_lookup_insert_ne. exact (fif_slot_ne k fd' H0' (not_eq_sym Hne')).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE RECORD                                                          *)
  (* ------------------------------------------------------------------- *)

  Definition file_iface : ep_iface N P.
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    refine (MkEI N P fif_fds fif_out (fun _ _ => False%I) (fun _ => False%I) fif_outm
              fif_in (fun _ _ => False%I) (fun _ => False%I)
              (fun _ _ _ _ => False%I) (fun _ _ _ => False%I) (fun _ => False%I)
              fif_filesr fif_taint fif_taint_pays
              fif_write _ fif_write_m _ fif_write_nil fif_read _ _ _ _ _ _ _ _ _ fif_open fif_open_absent
              fif_close fif_close_shared fif_exit).
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    (* the copy device (design SS3.4f): no copy device in the file application *)
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
  Defined.

  Lemma fif_ei_fds : ei_fds N P file_iface = fif_fds.
  Proof. reflexivity. Qed.
  Lemma fif_ei_files : ei_files N P file_iface = fif_filesr.
  Proof. reflexivity. Qed.
  Lemma fif_dev_of (d : nat) (x : dspec) : dev_of N P file_iface d x = fif_dev d x.
  Proof. by destruct x. Qed.

  (* =================================================================== *)
  (*  2.  END TO END: cat f and echo > f                                  *)
  (* =================================================================== *)

  Theorem cat_f_paid (content : list (bv 8)) (files : list (bv 8) -> option (list (bv 8))) :
    files fname_f = Some content ->
    env_res N P file_iface (cat_env0 [content; cat_dg_open fname_f] files [fname_f]) {[0%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    intros Hf. iIntros "H".
    iApply (tree_pay_of_conforms N P file_iface _ _ _
              (cat_file_conforms fname_f content files Hf) (cat_tree_safe _ _) with "H").
  Qed.

  Theorem cat_f_absent_paid (files : list (bv 8) -> option (list (bv 8))) :
    files fname_f = None ->
    env_res N P file_iface (cat_env0 [cat_dg_open fname_f] files [fname_f]) {[0%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    intros Hf. iIntros "H".
    iApply (tree_pay_of_conforms N P file_iface _ _ _
              (cat_file_absent_conforms fname_f files Hf) (cat_tree_safe _ _) with "H").
  Qed.

  Theorem echo_f_paid (argv : list (list (bv 8))) (files : list (bv 8) -> option (list (bv 8))) :
    drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
    env_res N P file_iface (pipe_env (DOutM (echo_chunks argv)) files) {[0%nat]} -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    intros Hne Hnn. iIntros "H".
    iApply (tree_pay_of_conforms N P file_iface _ _ _
              (echo_file_conforms argv files Hne Hnn) (echo_tree_safe _ _) with "H").
  Qed.

  (* ---- what the round lends cat: the ledger with fds 1 and 2 the console
          and every standard stream open, the cwd, the payload, the
          application's facts, the deed at `f`, the registry's pool with
          device 0 the console, and the console owing [alts] ---- *)
  Lemma cat_env_res (l : list fdstate) (rb1 rb2 : bool) (s : dst) (q : Qp)
      (w : nat -> fdev) (alts : list (list (bv 8))) :
    w 0%nat = FDCons ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q s -∗ own γreg (fif_pool ∅ w) -∗
    cons_dev file_lm (file_params g) (file_links g) alts -∗
    env_res N P file_iface (cat_env0 alts (fif_files (snd <$> s)) [fname_f]) {[0%nat]}.
  Proof using .
    intros Hw Hl1 Hl2.
    set (fdm := (<[1 := 0%nat]> {[2 := 0%nat]} : fdmap)).
    assert (Hok : fif_ok fdm l {[0%nat := FDCons]}).
    { split; [| split; [| split]].
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_singleton_Some.
        unfold NOFILE. intros [[<- _] | (_ & <- & _)]; lia.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_singleton_Some.
        intros [[<- <-] | (_ & <- & <-)]; rewrite lookup_singleton; simpl;
          (split; [unfold NSTD; lia |]); [by exists rb1 | by exists rb2].
      - intros d. rewrite dom_singleton_L elem_of_singleton. split.
        + intros ->. exists 1. apply lookup_insert.
        + intros (fd & Hfd). revert Hfd. rewrite /fdm lookup_insert_Some lookup_singleton_Some.
          intros [[_ <-] | (_ & _ & <-)]; done.
      - intros fd fd' d s' i γo _ _ Hv. apply lookup_singleton_Some in Hv as [_ Hv]. discriminate. }
    iIntros "Hstd Hcwd Hpay #He Hd Hpool Hc". rewrite /env_res.
    iDestruct (fif_pool_own_take ∅ w 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    rewrite Hw. iDestruct (fif_tok_halves with "Htk") as "[Htk1 Htk2]".
    iSplit.
    { iPureIntro. intros fd d. cbn [cat_env0 pe_fd].
      rewrite lookup_insert_Some lookup_singleton_Some. intros [[_ <-] | (_ & _ & <-)]; set_solver. }
    iSplitL "Hstd Hcwd Hpay Hpool Htk1".
    { rewrite fif_ei_fds. iExists l, {[0%nat := FDCons]}, w. cbn [cat_env0 pe_fd].
      iFrame "Hstd Hcwd Hpay He". iSplit; [by iPureIntro |].
      iSplitL "Hpool"; [by rewrite dom_singleton_L right_id_L |].
      iSplitL "Htk1"; [by rewrite big_sepM_singleton |].
      rewrite big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton lookup_singleton /fif_hdl. done. }
    iSplitL "Hd".
    { rewrite fif_ei_files. cbn [cat_env0 pe_files pe_paths]. iSplit.
      - iPureIntro. intros p. rewrite elem_of_list_singleton. done.
      - iExists s, q. iFrame "Hd". iPureIntro. apply fif_files_f. }
    rewrite /dev_res big_sepS_singleton fif_dev_of. cbn [cat_env0 pe_dev].
    case_decide as Hc0; [| done]. simpl. iFrame "Htk2 Hc".
  Qed.

  Theorem cat_f_paid_of_round (l : list fdstate) (rb1 rb2 : bool) (q : Qp) (w : nat -> fdev)
      (i : Z) (content : list (bv 8)) :
    w 0%nat = FDCons ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q (Some (i, content)) -∗ own γreg (fif_pool ∅ w) -∗
    cons_dev file_lm (file_params g) (file_links g) [content; cat_dg_open fname_f] -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    intros Hw Hl1 Hl2. iIntros "Hstd Hcwd Hpay He Hd Hp Hc".
    iApply (cat_f_paid content _ (fif_files_f _)).
    iApply (cat_env_res l rb1 rb2 (Some (i, content)) q w with "Hstd Hcwd Hpay He Hd Hp Hc");
      assumption.
  Qed.

  Theorem cat_f_absent_paid_of_round (l : list fdstate) (rb1 rb2 : bool) (q : Qp)
      (w : nat -> fdev) :
    w 0%nat = FDCons ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q None -∗ own γreg (fif_pool ∅ w) -∗
    cons_dev file_lm (file_params g) (file_links g) [cat_dg_open fname_f] -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    intros Hw Hl1 Hl2. iIntros "Hstd Hcwd Hpay He Hd Hp Hc".
    iApply (cat_f_absent_paid _ (fif_files_f None)).
    iApply (cat_env_res l rb1 rb2 None q w with "Hstd Hcwd Hpay He Hd Hp Hc"); assumption.
  Qed.

  (* ---- what the redirect lends echo: fd 1 at the held row on `f`, every
          standard stream open, the pool with device 0 the file, and the
          line's cursor at chunk 0 ---- *)
  Lemma echo_env_res (l : list fdstate) (rb : bool) (i : Z) (γo : gname) (s : dst)
      (q : Qp) (w : nat -> fdev) (argv : list (list (bv 8))) :
    w 0%nat = FDFile i γo ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    fif_out_ok i argv ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q s -∗ own γreg (fif_pool ∅ w) -∗ file_out c r i γo argv 0 -∗
    env_res N P file_iface (pipe_env (DOutM (echo_chunks argv)) (fif_files (snd <$> s)))
      {[0%nat]}.
  Proof using .
    intros Hw Hl1 Hwok.
    set (fdm := ({[1 := 0%nat]} : fdmap)).
    assert (Hok : fif_ok fdm l {[0%nat := FDFile i γo]}).
    { split; [| split; [| split]].
      - intros fd d. rewrite /fdm lookup_singleton_Some. unfold NOFILE. intros [<- _]. lia.
      - intros fd d. rewrite /fdm lookup_singleton_Some. intros [<- <-].
        rewrite lookup_singleton. simpl. split; [unfold NSTD; lia | by exists rb].
      - intros d. rewrite dom_singleton_L elem_of_singleton. split.
        + intros ->. exists 1. apply lookup_singleton.
        + intros (fd & Hfd). revert Hfd. rewrite /fdm lookup_singleton_Some. by intros [_ <-].
      - intros fd fd' d s' i' γo' _ _ Hv. apply lookup_singleton_Some in Hv as [_ Hv]. discriminate. }
    iIntros "Hstd Hcwd Hpay #He Hd Hpool Hc". rewrite /env_res.
    iDestruct (fif_pool_own_take ∅ w 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    rewrite Hw. iDestruct (fif_tok_halves with "Htk") as "[Htk1 Htk2]".
    iSplit.
    { iPureIntro. intros fd d. cbn [pipe_env pe_fd].
      rewrite lookup_singleton_Some. intros [_ <-]. set_solver. }
    iSplitL "Hstd Hcwd Hpay Hpool Htk1".
    { rewrite fif_ei_fds. iExists l, {[0%nat := FDFile i γo]}, w. cbn [pipe_env pe_fd].
      iFrame "Hstd Hcwd Hpay He". iSplit; [by iPureIntro |].
      iSplitL "Hpool"; [by rewrite dom_singleton_L right_id_L |].
      iSplitL "Htk1"; [by rewrite big_sepM_singleton |].
      rewrite big_sepM_singleton lookup_singleton /fif_hdl. done. }
    iSplitL "Hd".
    { rewrite fif_ei_files. cbn [pipe_env pe_files pe_paths]. iSplit.
      - iPureIntro. intros p Hp. by apply elem_of_nil in Hp.
      - iExists s, q. iFrame "Hd". iPureIntro. apply fif_files_f. }
    rewrite /dev_res big_sepS_singleton fif_dev_of. cbn [pipe_env pe_dev].
    case_decide as Hc0; [| done]. simpl.
    iExists i, γo. iFrame "Htk2". iExists argv, 0%nat. iFrame "Hc". iPureIntro.
    split; [done | exact Hwok].
  Qed.

  Theorem echo_f_paid_of_redirect (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
      (s : dst) (q : Qp) (w : nat -> fdev) (argv : list (list (bv 8))) :
    w 0%nat = FDFile i γo ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    fif_out_ok i argv ->
    drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q s -∗ own γreg (fif_pool ∅ w) -∗ file_out c r i γo argv 0 -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse Hnil_in.
    intros Hw Hl1 Hwok Hne Hnn. iIntros "Hstd Hcwd Hpay He Hd Hp Hc".
    iApply (echo_f_paid argv _ Hne Hnn).
    iApply (echo_env_res l rb i γo s q w argv with "Hstd Hcwd Hpay He Hd Hp Hc"); assumption.
  Qed.

End UkFileIface.

(* the registry's birth: the whole pool, at any values *)
Lemma fif_reg_alloc `{!fifRegG Σ} (w : nat -> fdev) : ⊢ |==> ∃ γ, own γ (fif_pool ∅ w).
Proof. iApply own_alloc. apply fif_pool_valid. Qed.

(* ===================================================================== *)
(*  3.  THE VACUITY WITNESSES: every proved law at cat's instance         *)
(* ===================================================================== *)

Section UkFileIfaceCat.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !fifRegG Σ}.
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (N : uk_names Σ) `{!ukn_const N}.
  Context (γreg : gname).

  Local Instance fif_cat_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  Definition fif_write_cat :=
    fif_write g r Hcons N (cat_prog N) (cat_stub_write N) γreg.
  Definition fif_write_m_cat :=
    fif_write_m g r Heq N (cat_prog N) (cat_stub_write N) γreg.
  Definition fif_read_cat :=
    fif_read g r Heq N (cat_prog N) (cat_stub_read N) γreg.
  Definition fif_open_cat :=
    fif_open g r Heq N (cat_prog N) (cat_stub_open N) γreg.
  Definition fif_open_absent_nt_cat :=
    fif_open_absent_nt g r Heq N (cat_prog N) (cat_stub_open N) γreg.
  Definition fif_close_in_cat :=
    fif_close_in g r N (cat_prog N) (cat_stub_close N) γreg.
  Definition fif_exit_cat :=
    fif_exit g r N (cat_prog N) (cat_stub_exit N) γreg.
End UkFileIfaceCat.

(* ===================================================================== *)
(*  4.  ECHO'S INSTANCE: the record and the two theorems at [echo_prog],  *)
(*      no stub hypothesis (the four gaps by name)                        *)
(* ===================================================================== *)

Section UkFileIfaceEcho.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !fifRegG Σ}.
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (N : uk_names Σ) `{!ukn_const N}.
  Context (γreg : gname).
  Hypothesis Hnil_in : fif_nil_in_law g r N (echo_prog N) γreg.

  Definition file_iface_echo : ep_iface N (echo_prog N) :=
    file_iface g r Heq Hcons N (echo_prog N) (echo_stub_read N) (echo_stub_write N)
      (echo_stub_open N) (echo_stub_close N) (echo_stub_exit N) γreg
      Hnil_in.

  Definition echo_f_paid_echo (argv : list (list (bv 8)))
      (files : list (bv 8) -> option (list (bv 8))) :
    drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
    env_res N (echo_prog N) file_iface_echo (pipe_env (DOutM (echo_chunks argv)) files) {[0%nat]}
    -∗ tree_pay N (echo_prog N) (echo_tree argv) :=
    echo_f_paid g r Heq Hcons N (echo_prog N) (echo_stub_read N) (echo_stub_write N)
      (echo_stub_open N) (echo_stub_close N) (echo_stub_exit N) γreg
      Hnil_in argv files.

  Definition echo_f_paid_of_redirect_echo (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
      (s : dst) (q : Qp) (w : nat -> fdev) (argv : list (list (bv 8))) :
    w 0%nat = FDFile i γo ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    fif_out_ok i argv ->
    drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
    UserFd.ustd (ukn_fd N) l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env g r -∗ fdq r q s -∗ own γreg (fif_pool ∅ w) -∗
    file_out (fgn_cl g) r i γo argv 0 -∗
    tree_pay N (echo_prog N) (echo_tree argv) :=
    echo_f_paid_of_redirect g r Heq Hcons N (echo_prog N) (echo_stub_read N)
      (echo_stub_write N) (echo_stub_open N) (echo_stub_close N) (echo_stub_exit N)
      γreg Hnil_in l rb i γo s q w argv.
End UkFileIfaceEcho.
