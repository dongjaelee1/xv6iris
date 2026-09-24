(* ===================================================================== *)
(* UkFileIface.v -- THE FILE APPLICATION'S ENDPOINT INTERFACE: one         *)
(* [UkHandler.ep_iface] from the console ([UkConsOut]) and the file        *)
(* ([UkFileDev]), and cat f / echo > f paid end to end through the once-  *)
(* glue [UkHandler.tree_pay_of_conforms] (program-specs cut 4(c)).         *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4b-SS3.4c.             *)
(*                                                                        *)
(* THE REGISTRY.  A device is a natural number in the pure layer.  The    *)
(* devices a line shape binds BEFORE the process runs -- the console, the *)
(* file a redirect holds at a standard slot -- are named by a registry    *)
(* [reg : nat -> option fdev] that is a PARAMETER of the instance (the    *)
(* glue never sees it); every device the process itself opens (an input   *)
(* on `f`, at a tail handle) is UNREGISTERED and carries its own inode    *)
(* and offset name.  [fif_ok] is the pure half of [ei_fds]: a bound       *)
(* standard slot names a registered device at the row its kind demands,   *)
(* a bound tail slot names an unregistered one and holds its handle, and  *)
(* a registered device stays bound (so a device the glue calls fresh is   *)
(* never a registered one).                                               *)
(*                                                                        *)
(* WHAT IS PROVED, AND WHAT IS NOT.  The laws proved here are the console *)
(* write ([UkConsOut.cons_write]), the file write ([UkFileDev.file_write], *)
(* chunk [b] of the line at a held ledger slot), the open of `f` present   *)
(* and absent ([file_open_present] / [file_open_absent]), the close of a  *)
(* tail handle ([file_close]), the exit (the exit stub law and the        *)
(* payload), and the four pipe laws (vacuous: no pipe here).  FIVE fields *)
(* are section hypotheses, each at the narrowest case the kernel or the   *)
(* interface refuses (see the report at each):                             *)
(*                                                                        *)
(*   [Hread]   the read law.  DEVICE NUMBERS ARE REUSED: [ei_open] gives   *)
(*             the fresh device only [forall fd, fdm fd <> Some d], so a   *)
(*             closed input device (whose resource the glue still holds)   *)
(*             and a new one may share a number, and no resource can tell  *)
(*             the stale one from the live one -- the read at the live     *)
(*             handle cannot answer the stale device's stream.  Proved     *)
(*             when the handle and the device agree: [fif_read_linked].    *)
(*   [Hnil]    the zero-length write: [cons_write] needs the console       *)
(*             device and [ei_write_nil] hands only [ei_fds];              *)
(*             [file_write] needs [0 < |bs|].                              *)
(*   [Hclose_std] the close of a standard slot: the ledger then has a      *)
(*             closed slot, and the open of `f` ([file_open_present])      *)
(*             needs [fd_lowest_closed l = None] (an open into a standard  *)
(*             slot, and a read there, have no leaf).                     *)
(*   [Hopen_other] the open of an absent path that is not `f`, or at a    *)
(*             creating or truncating mode: the application's claim covers *)
(*             `f` only, and a creating open of an absent file CREATES.   *)
(*   [Htaint]  the taint pays any tree: the free handler needs a close of  *)
(*             a descriptor the process holds no handle for and the read   *)
(*             row's count bound, neither of which the tier exports.      *)
(*                                                                        *)
(* AND ONE LIMIT OF THE RECORD AT ECHO: [ep_iface] asks for every law      *)
(* whatever tree it pays, and [UkEchoTree.echo_prog] names no read, open   *)
(* or close stub (address 0), so [file_iface] has no instance at echo's    *)
(* program; [echo_f_paid] is stated at ANY program with the five stubs.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
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
Require Import UexecExecInst.
Require Import UsysMemOk.
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
Require Import UkConsOut UkFileDev.
Require Import UkHandler ProgTreeFile.
Require Import UCodeCat UkCatTree.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE REGISTRY AND THE FILES                                        *)
(* ===================================================================== *)

(* a device bound before the process runs: the console, or the file `f`
   at inode [i] with offset name [γo] (held at a standard slot, written) *)
Inductive fdev := FDCons | FDFile (i : Z) (γo : gname).

(* the application's files: `f`, and nothing else *)
Definition fif_files (s : option (list (bv 8))) : list (bv 8) -> option (list (bv 8)) :=
  fun p => if decide (p = fname_f) then s else None.

Lemma fif_files_f (s : option (list (bv 8))) : fif_files s fname_f = s.
Proof. unfold fif_files. case_decide; [reflexivity | done]. Qed.

Lemma fif_files_some (s : option (list (bv 8))) (p content : list (bv 8)) :
  fif_files s p = Some content -> p = fname_f /\ s = Some content.
Proof.
  unfold fif_files. case_decide as Hp; [subst p; by intros -> | done].
Qed.

(* the row a registered device's standard slot holds *)
Definition fif_row (x : option fdev) (st : option fdstate) : Prop :=
  match x with
  | Some FDCons => exists rb, st = Some (FdOpen rb true (FdDevice CONSOLE))
  | Some (FDFile i γo) => exists rb, st = Some (FdOpen rb true (FdInode i γo OffHeld))
  | None => False
  end.

(* THE PURE HALF OF [ei_fds]: the binding against the ledger [l] and the
   tail handles [hm] *)
Definition fif_ok (reg : nat -> option fdev) (fdm : fdmap) (l : list fdstate)
    (hm : gmap nat (Z * gname)) : Prop :=
  (forall fd d, fdm fd = Some d -> 0 <= fd < Z.of_nat NOFILE)
  /\ (forall fd d, fdm fd = Some d -> fd < Z.of_nat NSTD ->
        fif_row (reg d) (l !! Z.to_nat fd))
  /\ (forall fd d, fdm fd = Some d -> Z.of_nat NSTD <= fd -> reg d = None)
  /\ (forall k : nat, is_Some (hm !! k) <->
        ((NSTD <= k)%nat /\ exists d, fdm (Z.of_nat k) = Some d))
  /\ (forall d, reg d <> None -> exists fd, fdm fd = Some d).

(* a device a descriptor binds after an open is unregistered *)
Lemma fif_ok_fresh_unreg reg fdm l hm (d : nat) :
  fif_ok reg fdm l hm -> (forall fd', fdm fd' <> Some d) -> reg d = None.
Proof.
  intros (_ & _ & _ & _ & Hb) Hfr.
  destruct (reg d) eqn:E; [| reflexivity].
  destruct (Hb d ltac:(by rewrite E)) as (fd & Hfd). by destruct (Hfr fd).
Qed.

(* ...the open binds a fresh tail descriptor to it *)
Lemma fif_ok_open reg fdm l hm (k : nat) (d : nat) (x : Z * gname) :
  fif_ok reg fdm l hm -> (NSTD <= k < NOFILE)%nat ->
  fdm (Z.of_nat k) = None -> (forall fd', fdm fd' <> Some d) ->
  fif_ok reg (fdm_bind fdm (Z.of_nat k) (Some d)) l (<[k := x]> hm).
Proof.
  intros Hok Hk Hnone Hfr.
  pose proof (fif_ok_fresh_unreg reg fdm l hm d Hok Hfr) as Hd.
  destruct Hok as (H1 & H2 & H3 & H4 & H5).
  unfold fdm_bind. split; [| split; [| split; [| split]]].
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
    + intros _. lia.
    + apply H1.
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
    + intros _ Hlt. lia.
    + apply H2.
  - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
    + intros [= <-] _. exact Hd.
    + apply H3.
  - intros k'. destruct (decide (k' = k)) as [-> |].
    + rewrite lookup_insert. split; [| done]. intros _.
      split; [lia |]. exists d. by rewrite decide_True.
    + rewrite lookup_insert_ne; [| congruence]. rewrite H4.
      rewrite decide_False; [done |]. intros Heq. apply Nat2Z.inj in Heq. done.
  - intros d' Hd'. destruct (H5 d' Hd') as (fd & Hfd).
    exists fd. destruct (decide (fd = Z.of_nat k)) as [-> |]; [| exact Hfd].
    rewrite Hnone in Hfd. discriminate.
Qed.

(* ...and the close of a tail descriptor unbinds it *)
Lemma fif_ok_close reg fdm l hm (fd : Z) (d : nat) :
  fif_ok reg fdm l hm -> fdm fd = Some d -> Z.of_nat NSTD <= fd ->
  fif_ok reg (fdm_bind fdm fd None) l (delete (Z.to_nat fd) hm).
Proof.
  intros Hok Hfd Hs.
  destruct Hok as (H1 & H2 & H3 & H4 & H5).
  pose proof (H1 fd d Hfd) as Hr.
  assert (Hdn : reg d = None) by exact (H3 fd d Hfd Hs).
  unfold fdm_bind. split; [| split; [| split; [| split]]].
  - intros fd' d'. destruct (decide (fd' = fd)); [done | apply H1].
  - intros fd' d'. destruct (decide (fd' = fd)); [done | apply H2].
  - intros fd' d'. destruct (decide (fd' = fd)); [done | apply H3].
  - intros k'. destruct (decide (k' = Z.to_nat fd)) as [-> | Hk'].
    + rewrite lookup_delete. rewrite Z2Nat.id; [| lia].
      rewrite decide_True; [| done].
      split; [intros [? ?]; discriminate | intros (_ & ? & ?); discriminate].
    + rewrite lookup_delete_ne; [| congruence]. rewrite H4.
      rewrite decide_False; [done |]. intros Heq. apply Hk'. rewrite <- Heq.
      by rewrite Nat2Z.id.
  - intros d' Hd'. destruct (H5 d' Hd') as (fd' & Hfd').
    exists fd'. destruct (decide (fd' = fd)) as [-> |]; [| exact Hfd'].
    rewrite Hfd in Hfd'. injection Hfd' as <-. by rewrite Hdn in Hd'.
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
            !fileOutG Σ}.

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

  (* the registry of the devices the line binds before the process runs *)
  Context (reg : nat -> option fdev).

  Local Notation γfd := (ukn_fd N).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ------------------------------------------------------------------- *)
  (*  the resources                                                       *)
  (* ------------------------------------------------------------------- *)

  (* the application's persistent facts the device laws read *)
  Definition fif_env : iProp Σ :=
    (□ (app_taint -∗ file_taint c) ∗ □ (file_taint c -∗ app_taint)
     ∗ app_inv fsc_fs ∗ ∃ jo : option Z, file_cons_cred c r jo)%I.

  Global Instance fif_env_persistent : Persistent fif_env.
  Proof using . rewrite /fif_env. apply _. Qed.

  (* the tail handles: an input on `f` at each *)
  Definition fif_tail (hm : gmap nat (Z * gname)) : iProp Σ :=
    ([∗ map] k ↦ x ∈ hm, UserFd.ufd γfd k (FdOpen true false (FdInode x.1 x.2 OffHeld)))%I.

  (* [ei_fds], at its ledger and its handles *)
  Definition fif_fds_at (fdm : fdmap) (l : list fdstate) (hm : gmap nat (Z * gname))
      : iProp Σ :=
    (UserFd.ustd γfd l ∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO ∗ ukn_pay N (-1)
     ∗ ⌜fd_lowest_closed l = None⌝ ∗ ⌜fif_ok reg fdm l hm⌝ ∗ fif_tail hm ∗ fif_env)%I.

  Definition fif_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (hm : gmap nat (Z * gname)), fif_fds_at fdm l hm)%I.

  (* the console, at the generic claim of the file model *)
  Definition fif_out (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    match reg d with
    | Some FDCons => cons_dev file_lm (file_cparams g) alts
    | _ => False
    end%I.

  (* the file a redirect holds: the line's chunks from [b] on are owed *)
  Definition fif_out_ok (i : Z) (ws : wordline) : Prop :=
    i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO /\ i <> CAT_INO
    /\ Forall (fun ch => (length ch <= EchoDisc.line_max)%nat) (echo_chunks ws).

  Definition fif_outm (d : nat) (chunks : list (list (bv 8))) : iProp Σ :=
    match reg d with
    | Some (FDFile i γo) =>
        ∃ (ws : wordline) (b : nat),
          ⌜chunks = drop b (echo_chunks ws)⌝ ∗ ⌜fif_out_ok i ws⌝
          ∗ file_out c r i γo ws b
    | _ => False
    end%I.

  (* an input the process opened on `f` *)
  Definition fif_in (d : nat) (S : list (bv 8)) : iProp Σ :=
    match reg d with
    | None => ∃ (i : Z) (γo : gname) (q : Qp) (content : list (bv 8)),
                file_in r i γo q content S
    | Some _ => False
    end%I.

  (* the deed at `f` *)
  Definition fif_filesr (files : list (bv 8) -> option (list (bv 8))) : iProp Σ :=
    (∃ (s : dst) (q : Qp), ⌜files = fif_files (snd <$> s)⌝ ∗ fdq r q s)%I.

  (* THE TAINT, with everything the process still owns beside it *)
  Definition fif_taint : iProp Σ :=
    (file_taint c ∗ ukn_pay N (-1) ∗ (∃ l : list fdstate, UserFd.ustd γfd l)
     ∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO
     ∗ ∃ hl : list (nat * fdstate), [∗ list] p ∈ hl, UserFd.ufd γfd p.1 p.2)%I.

  (* ------------------------------------------------------------------- *)
  (*  small facts                                                         *)
  (* ------------------------------------------------------------------- *)

  (* a handle the kernel just handed back is none the process held *)
  Lemma fif_tail_fresh (hm : gmap nat (Z * gname)) (k : nat) (st : fdstate) :
    fif_tail hm -∗ UserFd.ufd γfd k st -∗
    ⌜hm !! k = None⌝ ∗ fif_tail hm ∗ UserFd.ufd γfd k st.
  Proof using .
    iIntros "Hm Hk". destruct (hm !! k) as [x |] eqn:E; [| by iFrame].
    iDestruct (big_sepM_lookup_acc _ _ _ _ E with "Hm") as "[[Hx _] _]".
    iDestruct "Hk" as "[Hk _]".
    iDestruct (ghost_map_elem_ne with "Hx Hk") as %Hne. by destruct Hne.
  Qed.

  Lemma fif_tail_list (hm : gmap nat (Z * gname)) :
    fif_tail hm -∗ ∃ hl : list (nat * fdstate), [∗ list] p ∈ hl, UserFd.ufd γfd p.1 p.2.
  Proof using .
    iIntros "Hm". rewrite /fif_tail big_sepM_map_to_list.
    iExists ((fun p => (p.1, FdOpen true false (FdInode p.2.1 p.2.2 OffHeld))) <$> map_to_list hm).
    rewrite big_sepL_fmap. iExact "Hm".
  Qed.

  (* the taint, out of what a law holds at a taint arm *)
  Lemma fif_taint_intro (l : list fdstate) (hl : list (nat * fdstate)) :
    file_taint c -∗ ukn_pay N (-1) -∗ UserFd.ustd γfd l -∗
    UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
    ([∗ list] p ∈ hl, UserFd.ufd γfd p.1 p.2) -∗ fif_taint.
  Proof using .
    iIntros "Ht Hp Hl Hc Hh". rewrite /fif_taint. iFrame "Ht Hp Hc".
    iSplitL "Hl"; [by iExists l |]. by iExists hl.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE LAWS                                                            *)
  (* ------------------------------------------------------------------- *)

  (* [ei_write] at the console: the device's slot is a console row *)
  Lemma fif_write (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    fif_fds fdm -∗ fif_out d alts -∗
    ((fif_fds fdm -∗ fif_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, fif_taint -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hcons Hsw HPc.
    intros _ Hfd Ha Hpre. iIntros "Hfds Hout HK".
    rewrite /fif_out. destruct (reg d) as [[| i γo] |] eqn:Er;
      [| iDestruct "Hout" as "[]" | iDestruct "Hout" as "[]"].
    iDestruct "Hfds" as (l hm) "(Hstd & Hcwd & Hpay & %Hnone & %Hok & Ht & #He)".
    pose proof Hok as (H1 & H2 & H3 & _).
    destruct (H1 fd d Hfd) as [H0 Hlt].
    assert (Hs : fd < Z.of_nat NSTD).
    { destruct (decide (fd < Z.of_nat NSTD)) as [| Hn]; [done |].
      rewrite (H3 fd d Hfd ltac:(lia)) in Er. discriminate. }
    pose proof (H2 fd d Hfd Hs) as Hrow. rewrite Er in Hrow.
    destruct Hrow as (rb & Hrow).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (cons_write file_lm (file_cparams g) file_lm_byte_laws None (file_wa g)
              Hcons N P Hsw l k rb alts a bs K
              ltac:(unfold NSTD in *; lia) Hrow Ha Hpre with "Hstd Hout").
    iIntros "Hstd Hout". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[Hstd Hcwd Hpay Ht] [Hout]").
    - iExists l, hm. iFrame "Hstd Hcwd Hpay Ht He". by iPureIntro.
    - iExact "Hout".
  Qed.

  (* [ei_write_m] at the file a redirect holds: chunk [b] of the line *)
  Lemma fif_write_m (fdm : fdmap) (fd : Z) (d : nat) (rest : list (list (bv 8)))
      (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm fd = Some d ->
    fif_fds fdm -∗ fif_outm d (bs :: rest) -∗
    ((fif_fds fdm -∗ fif_outm d rest -∗ K (Z.of_nat (length bs)))
     ∧ (fif_fds fdm -∗ fif_outm d rest -∗ K (-1))
     ∧ (∀ x, fif_taint -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Heq Hsw.
    intros Hne Hfd. iIntros "Hfds Hout HK".
    rewrite /fif_outm. destruct (reg d) as [[| i γo] |] eqn:Er;
      [iDestruct "Hout" as "[]" | | iDestruct "Hout" as "[]"].
    iDestruct "Hout" as (ws b) "(%Hch & %Hwok & Hout)".
    destruct (fif_drop_cons _ _ _ _ (eq_sym Hch)) as (Hb & Hbs & Hrest).
    destruct Hwok as (Hi1 & Hi2 & Hi3 & Hi4 & Hlm).
    assert (Hbl : (length bs <= EchoDisc.line_max)%nat).
    { rewrite <- Hbs. apply (proj1 (Forall_lookup _ _) Hlm b).
      apply list_lookup_lookup_total_lt. exact Hb. }
    iDestruct "Hfds" as (l hm) "(Hstd & Hcwd & Hpay & %Hnone & %Hok & Ht & #He)".
    pose proof Hok as (H1 & H2 & H3 & _).
    destruct (H1 fd d Hfd) as [H0 Hlt].
    assert (Hs : fd < Z.of_nat NSTD).
    { destruct (decide (fd < Z.of_nat NSTD)) as [| Hn]; [done |].
      rewrite (H3 fd d Hfd ltac:(lia)) in Er. discriminate. }
    pose proof (H2 fd d Hfd Hs) as Hrow. rewrite Er in Hrow.
    destruct Hrow as (rb & Hrow).
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & #Hm)".
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (file_write c r Heq N P Hsw k l rb i γo ws b b bs K
              ltac:(unfold NSTD in *; lia) Hrow Hb ltac:(lia) Hbs
              ltac:(destruct bs; [done | simpl; lia]) Hbl Hi1 Hi2 Hi3 Hi4
              with "Hbr Hinv Hstd Hout").
    iSplit.
    - iIntros "Hstd Hout". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[Hstd Hcwd Hpay Ht] [Hout]").
      + iExists l, hm. iFrame "Hstd Hcwd Hpay Ht Hbr Hrb Hinv Hm". by iPureIntro.
      + iExists ws, (S b). iFrame "Hout". iPureIntro.
        split; [exact Hrest | repeat split; assumption].
    - iIntros "Hstd Hout". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[Hstd Hcwd Hpay Ht] [Hout]").
      + iExists l, hm. iFrame "Hstd Hcwd Hpay Ht Hbr Hrb Hinv Hm". by iPureIntro.
      + iExists ws, (S b). iFrame "Hout". iPureIntro.
        split; [exact Hrest | repeat split; assumption].
  Qed.

  (* [ei_read] WHEN THE HANDLE AND THE DEVICE AGREE: the tail handle at
     [fd] is on the device's inode with its offset name.  This is
     [UkFileDev.file_read]; what the record's law lacks is only the
     agreement (the header's [Hread]). *)
  Lemma fif_read_linked (fdm : fdmap) (l : list fdstate) (hm : gmap nat (Z * gname))
      (fd : Z) (d : nat) (i : Z) (γo : gname) (q : Qp) (content Sin : list (bv 8))
      (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm fd = Some d -> Z.of_nat NSTD <= fd ->
    hm !! Z.to_nat fd = Some (i, γo) ->
    fif_fds_at fdm l hm -∗ file_in r i γo q content Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        fif_fds fdm -∗ file_in r i γo q content S' -∗ K (RdBytes cb))
     ∧ (∀ x, fif_taint -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Heq Hsr.
    intros Hn Hfd Hs Hh. iIntros "Hfds Hin HK".
    iDestruct "Hfds" as "(Hstd & Hcwd & Hpay & %Hnone & %Hok & Ht & #He)".
    pose proof Hok as (H1 & _).
    destruct (H1 fd d Hfd) as [H0 Hlt].
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & %jo & #Hm)".
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hh.
    rewrite /fif_tail.
    iDestruct (big_sepM_delete _ _ _ _ Hh with "Ht") as "[Hh Ht]".
    iApply (file_read c r Heq N P Hsr k false i γo q jo content Sin n K
              ltac:(lia) Hn with "Hbr Hrb Hm Hinv Hh Hin").
    iSplit.
    - iIntros (cb S') "%Hc Hh Hin". iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb S' with "[%] [-Hin] Hin"); [exact Hc |].
      iExists l, hm. iFrame "Hstd Hcwd Hpay". iSplit; [by iPureIntro |].
      iSplit; [by iPureIntro |].
      iSplitL; [| iFrame "Hbr Hrb Hinv"; by iExists jo].
      iApply (big_sepM_delete _ _ _ _ Hh). iSplitL "Hh"; [iExact "Hh" | iExact "Ht"].
    - iIntros (x) "#Htn Hh Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
      iAssert (fif_tail hm) with "[Hh Ht]" as "Ht".
      { rewrite /fif_tail. iApply (big_sepM_delete _ _ _ _ Hh).
        iSplitL "Hh"; [iExact "Hh" | iExact "Ht"]. }
      iDestruct (fif_tail_list with "Ht") as (hl) "Hhl".
      iApply (fif_taint_intro l hl with "Htn Hpay Hstd Hcwd Hhl").
  Qed.

  (* [ei_open] for `f` present: a fresh tail handle, the input device at
     the whole content; or -1; or the taint *)
  Lemma fif_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (path content : list (bv 8)) (K : Z -> iProp Σ) :
    files path = Some content ->
    fif_fds fdm -∗ fif_filesr files -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm fd = None⌝ -∗
        (∀ d : nat, ⌜forall fd', fdm fd' <> Some d⌝ -∗
           fif_fds (fdm_bind fdm fd (Some d)) ∗ fif_in d content) -∗
        fif_filesr files -∗ K fd)
     ∧ (fif_fds fdm -∗ fif_filesr files -∗ K (-1))
     ∧ (∀ x, fif_taint -∗ K x)) -∗
    op_obl N P path 0 K.
  Proof using Heq Hso.
    intros Hf. iIntros "Hfds Hfiles HK".
    iDestruct "Hfiles" as (s q) "[%Hfs Hd]".
    rewrite Hfs in Hf. apply fif_files_some in Hf as [-> Hs].
    destruct s as [[i content'] |]; [| discriminate]. simpl in Hs. injection Hs as ->.
    iDestruct "Hfds" as (l hm) "(Hstd & Hcwd & Hpay & %Hnone & %Hok & Ht & #He)".
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & #Hm)".
    iAssert (fdq r (q / 2) (Some (i, content)) ∗ fdq r (q / 2) (Some (i, content)))%I
      with "[Hd]" as "[Hd1 Hd2]".
    { iApply fdq_split. by rewrite Qp.div_2. }
    iApply (file_open_present c r Heq N P Hso l FsImg.ROOTINO (q / 2) (q / 2) i content K
              Hnone eq_refl with "Hinv Hstd Hcwd Hd1 Hd2").
    iSplit; [| iSplit].
    - (* the handle *)
      iIntros (fd γo) "%Hfdr Hstd Hcwd Hh Hin Hd1".
      iDestruct (fif_tail_fresh with "Ht Hh") as "(%Hhm & Ht & Hh)".
      assert (Hnb : fdm (Z.of_nat fd) = None).
      { destruct (fdm (Z.of_nat fd)) as [d' |] eqn:E; [| reflexivity].
        pose proof Hok as (_ & _ & _ & H4 & _).
        destruct (proj2 (H4 fd) (conj (proj1 Hfdr) (ex_intro _ d' E))) as [x Hx].
        rewrite Hhm in Hx. discriminate. }
      iDestruct "HK" as "[HK _]".
      iApply ("HK" $! (Z.of_nat fd) with "[%] [%] [-Hd1] [Hd1]"); [lia | exact Hnb | |].
      + iIntros (d) "%Hfr".
        pose proof (fif_ok_fresh_unreg reg fdm l hm d Hok Hfr) as Hd.
        iSplitR "Hin".
        * iExists l, (<[fd := (i, γo)]> hm). iFrame "Hstd Hcwd Hpay".
          iSplit; [by iPureIntro |]. iSplit.
          { iPureIntro. apply fif_ok_open; [exact Hok | exact Hfdr | exact Hnb | exact Hfr]. }
          iSplitL; [| iFrame "Hbr Hrb Hinv Hm"].
          rewrite /fif_tail big_sepM_insert; [| exact Hhm]. iFrame "Hh Ht".
        * rewrite /fif_in Hd. iExists i, γo, (q / 2)%Qp, content. iExact "Hin".
      + iExists (Some (i, content)), (q / 2)%Qp. iFrame "Hd1". iPureIntro. exact Hfs.
    - (* -1 *)
      iIntros "Hstd Hcwd Hd1 Hd2". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[Hstd Hcwd Hpay Ht] [Hd1 Hd2]").
      + iExists l, hm. iFrame "Hstd Hcwd Hpay Ht Hbr Hrb Hinv Hm". by iPureIntro.
      + iExists (Some (i, content)), (q / 2 + q / 2)%Qp. iSplit; [by iPureIntro |].
        iApply (fdq_join with "Hd1 Hd2").
    - (* the taint *)
      iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iDestruct (fif_tail_list with "Ht") as (hl) "Hhl".
      rewrite /uk_open_taint_fd.
      iDestruct "Hof" as "[Hal | [_ Hstd]]".
      + iDestruct "Hal" as (fd rd wr t) "[_ Hal]".
        iDestruct (ualloc_hi γfd l fd (FdOpen rd wr t) Hnone with "Hal")
          as "(_ & Hstd & Hh)".
        iApply (fif_taint_intro l ((fd, FdOpen rd wr t) :: hl)
                  with "Htn Hpay Hstd Hcwd [Hh Hhl]").
        rewrite big_sepL_cons. iFrame "Hh Hhl".
      + iApply (fif_taint_intro l hl with "Htn Hpay Hstd Hcwd Hhl").
  Qed.

  (* [ei_open_absent] for `f`, at a mode that neither creates nor
     truncates *)
  Lemma fif_open_absent_f (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (m : Z) (K : Z -> iProp Σ) :
    files fname_f = None ->
    SysOpenDefs.om_create (mword_of_int m : mword 64) = false ->
    SysOpenDefs.om_trunc (mword_of_int m : mword 64) = false ->
    fif_fds fdm -∗ fif_filesr files -∗
    ((fif_fds fdm -∗ fif_filesr files -∗ K (-1)) ∧ (∀ x, fif_taint -∗ K x)) -∗
    op_obl N P fname_f m K.
  Proof using Heq Hso.
    intros Hf Hcr Htr. iIntros "Hfds Hfiles HK".
    iDestruct "Hfiles" as (s q) "[%Hfs Hd]".
    assert (Hs : s = None).
    { rewrite Hfs fif_files_f in Hf. destruct s; [discriminate | reflexivity]. }
    subst s.
    iDestruct "Hfds" as (l hm) "(Hstd & Hcwd & Hpay & %Hnone & %Hok & Ht & #He)".
    iDestruct "He" as "(#Hbr & #Hrb & #Hinv & #Hm)".
    iApply (file_open_absent c r Heq N P Hso l FsImg.ROOTINO q m K eq_refl Hcr Htr
              with "Hinv Hstd Hcwd Hd").
    iSplit.
    - iIntros "Hstd Hcwd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[Hstd Hcwd Hpay Ht] [Hd]").
      + iExists l, hm. iFrame "Hstd Hcwd Hpay Ht Hbr Hrb Hinv Hm". by iPureIntro.
      + iExists None, q. iFrame "Hd". by iPureIntro.
    - iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ HK]". iApply "HK".
      iDestruct (fif_tail_list with "Ht") as (hl) "Hhl".
      rewrite /uk_open_taint_fd.
      iDestruct "Hof" as "[Hal | [_ Hstd]]".
      + iDestruct "Hal" as (fd rd wr t) "[_ Hal]".
        iDestruct (ualloc_hi γfd l fd (FdOpen rd wr t) Hnone with "Hal")
          as "(_ & Hstd & Hh)".
        iApply (fif_taint_intro l ((fd, FdOpen rd wr t) :: hl)
                  with "Htn Hpay Hstd Hcwd [Hh Hhl]").
        rewrite big_sepL_cons. iFrame "Hh Hhl".
      + iApply (fif_taint_intro l hl with "Htn Hpay Hstd Hcwd Hhl").
  Qed.

  (* [ei_close] at a tail handle *)
  Lemma fif_close_tail (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm fd = Some d -> Z.of_nat NSTD <= fd ->
    fif_fds fdm -∗
    ((fif_fds (fdm_bind fdm fd None) -∗ K 0) ∧ (∀ x, fif_taint -∗ K x)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hs. iIntros "Hfds HK".
    iDestruct "Hfds" as (l hm) "(Hstd & Hcwd & Hpay & %Hnone & %Hok & Ht & #He)".
    pose proof Hok as (H1 & _ & _ & H4 & _).
    destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (fif_ok_close reg fdm l hm fd d Hok Hfd Hs) as Hok'.
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hok'.
    assert (Hk : (NSTD <= k)%nat) by lia.
    destruct (proj2 (H4 k) (conj Hk (ex_intro _ d Hfd))) as [x Hx].
    rewrite /fif_tail.
    iDestruct (big_sepM_delete _ _ _ _ Hx with "Ht") as "[Hh Ht]".
    iApply (file_close N P Hsc k (FdOpen true false (FdInode x.1 x.2 OffHeld))
              K I with "Hh").
    iDestruct "HK" as "[HK _]". iApply "HK".
    iExists l, (delete k hm). iFrame "Hstd Hcwd Hpay Ht He".
    iSplit; [by iPureIntro |]. by iPureIntro.
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

  Lemma fif_exit (s : Z) (fdm : fdmap) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    fif_fds fdm -∗
    ([∗ set] d ∈ ds, match dv d with
                     | DOut alts => fif_out d alts
                     | DOutH alts => False
                     | DOutM alts => fif_outm d alts
                     | DHalt => False
                     | DIn Sin => fif_in d Sin
                     | DInE Sin => False
                     | DInEnd => False
                     end) -∗
    ex_obl N P s.
  Proof using HNc Hse.
    intros _. iIntros "Hfds _".
    iDestruct "Hfds" as (l hm) "(_ & _ & Hpay & _)".
    iApply (fif_exit_pay with "Hpay").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE FIELDS THE KERNEL OR THE INTERFACE REFUSES (the header's list)  *)
  (* ------------------------------------------------------------------- *)

  Hypothesis Hread : forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8))
      (n : nat) (K : rd_ans -> iProp Σ),
    (0 < n)%nat -> fdm fd = Some d ->
    fif_fds fdm -∗ fif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        fif_fds fdm -∗ fif_in d S' -∗ K (RdBytes cb))
     ∧ (∀ x, fif_taint -∗ K x)) -∗
    rd_obl N P fd n K.

  Hypothesis Hnil : forall (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ),
    fdm fd = Some d ->
    fif_fds fdm -∗
    ((fif_fds fdm -∗ K 0) ∧ (fif_fds fdm -∗ K (-1)) ∧ (∀ x, fif_taint -∗ K x)) -∗
    wr_obl N P fd [] K.

  Hypothesis Hclose_std : forall (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ),
    fdm fd = Some d -> fd < Z.of_nat NSTD ->
    fif_fds fdm -∗
    ((fif_fds (fdm_bind fdm fd None) -∗ K 0) ∧ (∀ x, fif_taint -∗ K x)) -∗
    cl_obl N P fd K.

  Hypothesis Hopen_other : forall (fdm : fdmap)
      (files : list (bv 8) -> option (list (bv 8))) (path : list (bv 8)) (m : Z)
      (K : Z -> iProp Σ),
    files path = None ->
    (path <> fname_f
     \/ SysOpenDefs.om_create (mword_of_int m : mword 64) = true
     \/ SysOpenDefs.om_trunc (mword_of_int m : mword 64) = true) ->
    fif_fds fdm -∗ fif_filesr files -∗
    ((fif_fds fdm -∗ fif_filesr files -∗ K (-1)) ∧ (∀ x, fif_taint -∗ K x)) -∗
    op_obl N P path m K.

  Hypothesis Htaint : forall t : proc, fif_taint -∗ tree_pay N P t.

  (* the two laws assembled from their cases *)
  Lemma fif_open_absent (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    files path = None ->
    fif_fds fdm -∗ fif_filesr files -∗
    ((fif_fds fdm -∗ fif_filesr files -∗ K (-1)) ∧ (∀ x, fif_taint -∗ K x)) -∗
    op_obl N P path m K.
  Proof using Heq Hso Hopen_other.
    intros Hf.
    destruct (decide (path = fname_f)) as [-> |]; last first.
    { apply (Hopen_other fdm files path m K Hf). by left. }
    destruct (SysOpenDefs.om_create (mword_of_int m : mword 64)) eqn:Ecr.
    { apply (Hopen_other fdm files fname_f m K Hf). by right; left. }
    destruct (SysOpenDefs.om_trunc (mword_of_int m : mword 64)) eqn:Etr.
    { apply (Hopen_other fdm files fname_f m K Hf). by right; right. }
    exact (fif_open_absent_f fdm files m K Hf Ecr Etr).
  Qed.

  Lemma fif_close (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm fd = Some d ->
    fif_fds fdm -∗
    ((fif_fds (fdm_bind fdm fd None) -∗ K 0) ∧ (∀ x, fif_taint -∗ K x)) -∗
    cl_obl N P fd K.
  Proof using Hsc Hclose_std.
    intros Hfd. destruct (decide (fd < Z.of_nat NSTD)).
    - exact (Hclose_std fdm fd d K Hfd ltac:(assumption)).
    - exact (fif_close_tail fdm fd d K Hfd ltac:(lia)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE RECORD                                                          *)
  (* ------------------------------------------------------------------- *)

  Definition file_iface : ep_iface N P.
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    refine (MkEI N P fif_fds fif_out (fun _ _ => False%I) (fun _ => False%I) fif_outm
              (fun _ _ => False%I) (fun _ => False%I) fif_taint _ fif_in fif_filesr
              _ _ _ _ _ _ _ _ _ _ _ _).
    - exact Htaint.
    - exact fif_write.
    - intros. iIntros "_ []".
    - exact fif_write_m.
    - intros. iIntros "_ []".
    - exact Hnil.
    - exact Hread.
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - exact fif_open.
    - exact fif_open_absent.
    - exact fif_close.
    - exact fif_exit.
  Defined.

  Lemma fif_ei_fds : ei_fds N P file_iface = fif_fds.
  Proof. reflexivity. Qed.
  Lemma fif_ei_out : ei_out N P file_iface = fif_out.
  Proof. reflexivity. Qed.
  Lemma fif_ei_outm : ei_outm N P file_iface = fif_outm.
  Proof. reflexivity. Qed.
  Lemma fif_ei_in : ei_in N P file_iface = fif_in.
  Proof. reflexivity. Qed.
  Lemma fif_ei_files : ei_files N P file_iface = fif_filesr.
  Proof. reflexivity. Qed.

  (* =================================================================== *)
  (*  2.  END TO END: cat f and echo > f                                  *)
  (* =================================================================== *)

  (* ---- cat f: fds 1 and 2 the console (device 0), owing the content or
          the diagnostic, which is [UkConsOut.cons_dev]'s unfiled arm at
          the two codes the round admits ---- *)
  Definition cat_reg : nat -> option fdev :=
    fun d => if decide (d = 0%nat) then Some FDCons else None.

  Theorem cat_f_paid (content : list (bv 8)) :
    env_res N P file_iface
      (cat_env0 [content; cat_dg_open fname_f] (fif_files (Some content))) {[0%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    iIntros "H".
    iApply (tree_pay_of_conforms N P file_iface _ _ _
              (cat_file_conforms fname_f content _ (fif_files_f _)) with "H").
  Qed.

  Theorem cat_f_absent_paid :
    env_res N P file_iface (cat_env0 [cat_dg_open fname_f] (fif_files None)) {[0%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    iIntros "H".
    iApply (tree_pay_of_conforms N P file_iface _ _ _
              (cat_file_absent_conforms fname_f _ (fif_files_f _)) with "H").
  Qed.

  (* what the round lends cat: the ledger with fds 1 and 2 the console and
     every standard stream open, the cwd, the payload, the application's
     facts, the deed at `f`, and the console owing [alts] *)
  Lemma cat_env_res (l : list fdstate) (rb1 rb2 : bool) (s : dst) (q : Qp)
      (alts : list (list (bv 8))) :
    (forall d, reg d = cat_reg d) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed l = None ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q s -∗ cons_dev file_lm (file_cparams g) alts -∗
    env_res N P file_iface (cat_env0 alts (fif_files (snd <$> s))) {[0%nat]}.
  Proof using .
    intros Hreg Hl1 Hl2 Hnone.
    assert (Hok : fif_ok reg (pe_fd (cat_env0 alts (fif_files (snd <$> s)))) l ∅).
    { cbv [cat_env0 pe_fd]. split; [| split; [| split; [| split]]].
      - intros fd d. destruct (decide (fd = 1 \/ fd = 2)) as [Hf |]; [| discriminate].
        intros _. unfold NOFILE. lia.
      - intros fd d. destruct (decide (fd = 1 \/ fd = 2)) as [Hf |]; [| discriminate].
        intros [= <-] _. rewrite Hreg /cat_reg. case_decide as Hc0; [| exfalso; by apply Hc0].
        destruct Hf as [-> | ->]; [exists rb1; exact Hl1 | exists rb2; exact Hl2].
      - intros fd d. destruct (decide (fd = 1 \/ fd = 2)) as [Hf |]; [| discriminate].
        intros _ Hs. unfold NSTD in Hs. lia.
      - intros k. rewrite lookup_empty. split; [intros [? ?]; discriminate |].
        intros (Hk & d & Hd).
        destruct (decide (Z.of_nat k = 1 \/ Z.of_nat k = 2)) as [Hf |];
          [unfold NSTD in Hk; lia | discriminate].
      - intros d. rewrite Hreg /cat_reg. destruct (decide (d = 0%nat)) as [-> |];
          [| intros Hc; exfalso; by apply Hc].
        intros _. exists 1. case_decide as Hc0; [reflexivity | exfalso; apply Hc0; by left]. }
    iIntros "Hstd Hcwd Hpay #He Hd Hc". rewrite /env_res.
    iSplit.
    { iPureIntro. intros fd d. cbv [cat_env0 pe_fd].
      destruct (decide (fd = 1 \/ fd = 2)); [intros [= <-]; set_solver | discriminate]. }
    iSplitL "Hstd Hcwd Hpay".
    { rewrite fif_ei_fds /fif_fds /fif_fds_at. iExists l, ∅. iFrame "Hstd Hcwd Hpay He".
      iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
      by rewrite /fif_tail big_sepM_empty. }
    iSplitL "Hd".
    { rewrite fif_ei_files /fif_filesr. iExists s, q. iFrame "Hd". by iPureIntro. }
    rewrite /dev_res big_sepS_singleton. cbv [cat_env0 pe_dev].
    case_decide as Hc0; [| exfalso; by apply Hc0]. cbv beta iota.
    rewrite fif_ei_out /fif_out Hreg /cat_reg. case_decide as Hc1; [| exfalso; by apply Hc1].
    iExact "Hc".
  Qed.

  Theorem cat_f_paid_of_round (l : list fdstate) (rb1 rb2 : bool) (q : Qp)
      (i : Z) (content : list (bv 8)) :
    (forall d, reg d = cat_reg d) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed l = None ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q (Some (i, content)) -∗
    cons_dev file_lm (file_cparams g) [content; cat_dg_open fname_f] -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    intros Hreg Hl1 Hl2 Hnone. iIntros "Hstd Hcwd Hpay He Hd Hc".
    iApply (cat_f_paid content).
    iApply (cat_env_res l rb1 rb2 (Some (i, content)) q with "Hstd Hcwd Hpay He Hd Hc");
      assumption.
  Qed.

  Theorem cat_f_absent_paid_of_round (l : list fdstate) (rb1 rb2 : bool) (q : Qp) :
    (forall d, reg d = cat_reg d) ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed l = None ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q None -∗
    cons_dev file_lm (file_cparams g) [cat_dg_open fname_f] -∗
    tree_pay N P (cat_tree [sb "cat"; fname_f]).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    intros Hreg Hl1 Hl2 Hnone. iIntros "Hstd Hcwd Hpay He Hd Hc".
    iApply cat_f_absent_paid.
    iApply (cat_env_res l rb1 rb2 None q with "Hstd Hcwd Hpay He Hd Hc"); assumption.
  Qed.

  (* ---- echo > f: fd 1 the held descriptor on `f` (device 0), owing the
          line's chunks ([UEchoFile]'s cursor at chunk 0) ---- *)
  Definition echo_reg (i : Z) (γo : gname) : nat -> option fdev :=
    fun d => if decide (d = 0%nat) then Some (FDFile i γo) else None.

  Theorem echo_f_paid (argv : list (list (bv 8))) (files : list (bv 8) -> option (list (bv 8))) :
    drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
    env_res N P file_iface (pipe_env (DOutM (echo_chunks argv)) files) {[0%nat]} -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    intros Hne Hnn. iIntros "H".
    iApply (tree_pay_of_conforms N P file_iface _ _ _
              (echo_file_conforms argv files Hne Hnn) with "H").
  Qed.

  (* what the redirect lends echo: fd 1 at the held row on `f`, every
     standard stream open, and the line's cursor at chunk 0 *)
  Lemma echo_env_res (l : list fdstate) (rb : bool) (i : Z) (γo : gname) (s : dst)
      (q : Qp) (argv : list (list (bv 8))) :
    (forall d, reg d = echo_reg i γo d) ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    fd_lowest_closed l = None ->
    fif_out_ok i argv ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q s -∗ file_out c r i γo argv 0 -∗
    env_res N P file_iface (pipe_env (DOutM (echo_chunks argv)) (fif_files (snd <$> s)))
      {[0%nat]}.
  Proof using .
    intros Hreg Hl1 Hnone Hwok.
    assert (Hok : fif_ok reg (pe_fd (pipe_env (DOutM (echo_chunks argv))
                                     (fif_files (snd <$> s)))) l ∅).
    { cbv [pipe_env pe_fd]. split; [| split; [| split; [| split]]].
      - intros fd d. destruct (decide (fd = 1)) as [-> |]; [| discriminate].
        intros _. unfold NOFILE. lia.
      - intros fd d. destruct (decide (fd = 1)) as [-> |]; [| discriminate].
        intros [= <-] _. rewrite Hreg /echo_reg. case_decide as Hc0; [| exfalso; by apply Hc0].
        exists rb. exact Hl1.
      - intros fd d. destruct (decide (fd = 1)) as [-> |]; [| discriminate].
        intros _ Hs. unfold NSTD in Hs. lia.
      - intros k. rewrite lookup_empty. split; [intros [? ?]; discriminate |].
        intros (Hk & d & Hd). destruct (decide (Z.of_nat k = 1)) as [Hf |];
          [unfold NSTD in Hk; lia | discriminate].
      - intros d. rewrite Hreg /echo_reg. destruct (decide (d = 0%nat)) as [-> |];
          [| intros Hc; exfalso; by apply Hc].
        intros _. exists 1. case_decide as Hc0; [reflexivity | exfalso; by apply Hc0]. }
    iIntros "Hstd Hcwd Hpay #He Hd Hc". rewrite /env_res.
    iSplit.
    { iPureIntro. intros fd d. cbv [pipe_env pe_fd].
      destruct (decide (fd = 1)); [intros [= <-]; set_solver | discriminate]. }
    iSplitL "Hstd Hcwd Hpay".
    { rewrite fif_ei_fds /fif_fds /fif_fds_at. iExists l, ∅. iFrame "Hstd Hcwd Hpay He".
      iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
      by rewrite /fif_tail big_sepM_empty. }
    iSplitL "Hd".
    { rewrite fif_ei_files /fif_filesr. iExists s, q. iFrame "Hd". by iPureIntro. }
    rewrite /dev_res big_sepS_singleton. cbv [pipe_env pe_dev].
    case_decide as Hc0; [| exfalso; by apply Hc0]. cbv beta iota.
    rewrite fif_ei_outm /fif_outm Hreg /echo_reg. case_decide as Hc1; [| exfalso; by apply Hc1].
    iExists argv, 0%nat. iFrame "Hc". iPureIntro. split; [done | exact Hwok].
  Qed.

  Theorem echo_f_paid_of_redirect (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
      (s : dst) (q : Qp) (argv : list (list (bv 8))) :
    (forall d, reg d = echo_reg i γo d) ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    fd_lowest_closed l = None ->
    fif_out_ok i argv ->
    drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ ukn_pay N (-1) -∗
    fif_env -∗ fdq r q s -∗ file_out c r i γo argv 0 -∗
    tree_pay N P (echo_tree argv).
  Proof using Hcons Heq HPc HNc Hsr Hsw Hso Hsc Hse
              Hread Hnil Hclose_std Hopen_other Htaint.
    intros Hreg Hl1 Hnone Hwok Hne Hnn. iIntros "Hstd Hcwd Hpay He Hd Hc".
    iApply (echo_f_paid argv _ Hne Hnn).
    iApply (echo_env_res l rb i γo s q argv with "Hstd Hcwd Hpay He Hd Hc"); assumption.
  Qed.

End UkFileIface.

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
            !fileOutG Σ}.
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (N : uk_names Σ) `{!ukn_const N}.
  Context (reg : nat -> option fdev).

  Local Instance fif_cat_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  Definition fif_write_cat :=
    fif_write g r Hcons N (cat_prog N) (cat_stub_write N) reg.
  Definition fif_write_m_cat :=
    fif_write_m g r Heq N (cat_prog N) (cat_stub_write N) reg.
  Definition fif_read_linked_cat :=
    fif_read_linked g r Heq N (cat_prog N) (cat_stub_read N) reg.
  Definition fif_open_cat :=
    fif_open g r Heq N (cat_prog N) (cat_stub_open N) reg.
  Definition fif_open_absent_f_cat :=
    fif_open_absent_f g r Heq N (cat_prog N) (cat_stub_open N) reg.
  Definition fif_close_tail_cat :=
    fif_close_tail g r N (cat_prog N) (cat_stub_close N) reg.
  Definition fif_exit_cat :=
    fif_exit g r N (cat_prog N) (cat_stub_exit N) reg.
End UkFileIfaceCat.
