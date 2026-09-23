(* ===================================================================== *)
(* UkHandler.v -- THE ENDPOINT INTERFACE AND THE ONCE-GLUE: a conforming   *)
(* tree is paid from its environment's resources, once, by coinduction.  *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.3-3.4.  [ProgTree.     *)
(* conforms E t] is the pure half: every path of [t] writes a prefix of   *)
(* one of its device's alternatives, reads any chunking of its input, is  *)
(* ready for either answer of an open, and exits drained.  This file is   *)
(* the logic's half:                                                      *)
(*                                                                        *)
(*   [ep_iface]   what a destination provides -- a resource per binding   *)
(*                of descriptors to devices ([ei_fds]), per output device *)
(*                at what it still owes ([ei_out d alts]), per input       *)
(*                device at what is left to read ([ei_in d S]), for the   *)
(*                files ([ei_files]) -- and its LAWS AT THE HOLES of       *)
(*                [UkTree]: an output device funds a write of a chunk one  *)
(*                of its alternatives begins with, answers the count and   *)
(*                keeps the rest; an input device funds a read with a     *)
(*                [chunk_ok] answer; the files fund an open with a         *)
(*                descriptor the process did not hold, or -1; a binding    *)
(*                funds a close; the devices, drained, fund the exit.      *)
(*   [env_res]    the environment's resources, one per device of a finite *)
(*                set that every bound descriptor's device belongs to.    *)
(*   [tree_pay_of_conforms]  conforms E t -> env_res E ds -| tree_pay t.   *)
(*                                                                        *)
(* The instances (the console from the claim's cursor, the file from the  *)
(* deed, the pipe from its protocol) are cut 4(c); a program at a line     *)
(* shape is then its pure conformance theorem and nothing else.           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import ProcGeom.
Require Import FdSlots UserFd.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ProgTree UkTree.
Local Open Scope Z_scope.
Import Defs.

(* descriptors to devices, and the one update the rules make *)
Definition fdmap := Z -> option nat.
Definition fdm_bind (fdm : fdmap) (fd : Z) (d : option nat) : fdmap :=
  fun fd' => if decide (fd' = fd) then d else fdm fd'.

Section UkHandler.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).
  Context (P : uprog Σ).

  (* ------------------------------------------------------------------- *)
  (*  1.  THE INTERFACE                                                   *)
  (* ------------------------------------------------------------------- *)

  Record ep_iface := MkEI {
    ei_fds : fdmap -> iProp Σ;
    ei_out : nat -> list bytes -> iProp Σ;
    ei_outh : nat -> list bytes -> iProp Σ;    (* an output that may halt *)
    ei_halt : nat -> iProp Σ;                  (* ...and has *)
    ei_outm : nat -> list bytes -> iProp Σ;    (* an output where a write may miss *)
    ei_in_e : nat -> bytes -> iProp Σ;         (* an input that may end early *)
    ei_in_end : nat -> iProp Σ;                (* ...and has *)
    (* THE TAINT: the application's, which the kernel's leaves may hand a
       payer in place of an answer; it pays any tree *)
    ei_taint : iProp Σ;
    ei_taint_pays : forall (t : proc), ei_taint -∗ tree_pay N P t;
    ei_in : nat -> bytes -> iProp Σ;
    ei_files : (bytes -> option bytes) -> iProp Σ;
    (* a write of a chunk the chosen alternative begins with: the count
       comes back exactly, the device owes that alternative's rest *)
    ei_write : forall (fdm : fdmap) (fd : Z) (d : nat) (alts : list bytes)
                 (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_out d alts -∗
        ((ei_fds fdm -∗ ei_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* at a haltable device the payer answers the count, or -1 and halts *)
    ei_write_h : forall (fdm : fdmap) (fd : Z) (d : nat) (alts : list bytes)
                   (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_outh d alts -∗
        ((ei_fds fdm -∗ ei_outh d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_halt d -∗ K (-1))
         ∧ (∀ x, ei_taint -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* at a device where a write may miss: the count, or -1, the device
       owing the rest either way *)
    ei_write_m : forall (fdm : fdmap) (fd : Z) (d : nat) (alts : list bytes)
                   (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_outm d alts -∗
        ((ei_fds fdm -∗ ei_outm d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_outm d [drop (length bs) a] -∗ K (-1))
         ∧ (∀ x, ei_taint -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_halt : forall (fdm : fdmap) (fd : Z) (d : nat) (bs : bytes)
                      (K : Z -> iProp Σ),
        bs <> [] -> fdm fd = Some d ->
        ei_fds fdm -∗ ei_halt d -∗
        ((ei_fds fdm -∗ ei_halt d -∗ K (-1)) ∧ (∀ x, ei_taint -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* a zero-length write: 0 or -1, nothing moves *)
    ei_write_nil : forall (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ),
        fdm fd = Some d ->
        ei_fds fdm -∗
        ((ei_fds fdm -∗ K 0) ∧ (ei_fds fdm -∗ K (-1)) ∧ (∀ x, ei_taint -∗ K x)) -∗
        wr_obl N P fd [] K;
    (* a read of at least one byte: some chunk of what is left, empty only
       at end of file *)
    ei_read : forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : bytes) (n : nat)
                (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm fd = Some d ->
        ei_fds fdm -∗ ei_in d Sin -∗
        ((∀ (c S' : bytes), ⌜chunk_ok n Sin c S'⌝ -∗
            ei_fds fdm -∗ ei_in d S' -∗ K (RdBytes c))
         ∧ (∀ x, ei_taint -∗ K x)) -∗
        rd_obl N P fd n K;
    (* ...at an input that may end early: a chunk, or end of file *)
    ei_read_e : forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : bytes) (n : nat)
                  (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm fd = Some d ->
        ei_fds fdm -∗ ei_in_e d Sin -∗
        ((∀ (c S' : bytes), ⌜chunk_ok n Sin c S'⌝ -∗
            ei_fds fdm -∗ ei_in_e d S' -∗ K (RdBytes c))
         ∧ (ei_fds fdm -∗ ei_in_end d -∗ K (RdBytes []))
         ∧ (∀ x, ei_taint -∗ K x)) -∗
        rd_obl N P fd n K;
    ei_read_end : forall (fdm : fdmap) (fd : Z) (d : nat) (n : nat)
                    (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm fd = Some d ->
        ei_fds fdm -∗ ei_in_end d -∗
        ((ei_fds fdm -∗ ei_in_end d -∗ K (RdBytes [])) ∧ (∀ x, ei_taint -∗ K x)) -∗
        rd_obl N P fd n K;
    (* an open of a present file: a descriptor the process did not hold,
       bound to a device of the glue's choosing at the content -- or the
       kernel's -1 *)
    ei_open : forall (fdm : fdmap) (files : bytes -> option bytes)
                (path content : bytes) (K : Z -> iProp Σ),
        files path = Some content ->
        ei_fds fdm -∗ ei_files files -∗
        ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm fd = None⌝ -∗
            (∀ d : nat, ⌜forall fd', fdm fd' <> Some d⌝ -∗
               ei_fds (fdm_bind fdm fd (Some d)) ∗ ei_in d content) -∗
            ei_files files -∗ K fd)
         ∧ (ei_fds fdm -∗ ei_files files -∗ K (-1))
         ∧ (∀ x, ei_taint -∗ K x)) -∗
        op_obl N P path 0 K;
    ei_open_absent : forall (fdm : fdmap) (files : bytes -> option bytes)
                       (path : bytes) (m : Z) (K : Z -> iProp Σ),
        files path = None ->
        ei_fds fdm -∗ ei_files files -∗
        ((ei_fds fdm -∗ ei_files files -∗ K (-1)) ∧ (∀ x, ei_taint -∗ K x)) -∗
        op_obl N P path m K;
    ei_close : forall (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ),
        fdm fd = Some d ->
        ei_fds fdm -∗
        ((ei_fds (fdm_bind fdm fd None) -∗ K 0) ∧ (∀ x, ei_taint -∗ K x)) -∗
        cl_obl N P fd K;
    (* the exit, with every device drained *)
    ei_exit : forall (s : Z) (fdm : fdmap) (dv : nat -> dspec) (ds : gset nat),
        (forall d alts, d ∈ ds -> dv d = DOut alts \/ dv d = DOutH alts \/ dv d = DOutM alts
                        -> [] ∈ alts) ->
        ei_fds fdm -∗
        ([∗ set] d ∈ ds, match dv d with
                         | DOut alts => ei_out d alts
                         | DOutH alts => ei_outh d alts
                         | DOutM alts => ei_outm d alts
                         | DHalt => ei_halt d
                         | DIn Sin => ei_in d Sin
                         | DInE Sin => ei_in_e d Sin
                         | DInEnd => ei_in_end d
                         end) -∗
        ex_obl N P s;
  }.

  (* ------------------------------------------------------------------- *)
  (*  2.  THE ENVIRONMENT'S RESOURCES                                     *)
  (* ------------------------------------------------------------------- *)

  Definition dev_res (I : ep_iface) (dv : nat -> dspec) (ds : gset nat) : iProp Σ :=
    ([∗ set] d ∈ ds, match dv d with
                     | DOut alts => ei_out I d alts
                     | DOutH alts => ei_outh I d alts
                     | DOutM alts => ei_outm I d alts
                     | DHalt => ei_halt I d
                     | DIn Sin => ei_in I d Sin
                     | DInE Sin => ei_in_e I d Sin
                     | DInEnd => ei_in_end I d
                     end)%I.

  Definition env_res (I : ep_iface) (E : penv) (ds : gset nat) : iProp Σ :=
    (⌜forall fd d, pe_fd E fd = Some d -> d ∈ ds⌝
     ∗ ei_fds I (pe_fd E) ∗ ei_files I (pe_files E) ∗ dev_res I (pe_dev E) ds)%I.

  Lemma dev_res_take (I : ep_iface) (dv : nat -> dspec) (ds : gset nat) (d : nat) :
    d ∈ ds ->
    dev_res I dv ds ⊣⊢
    (match dv d with
     | DOut alts => ei_out I d alts
     | DOutH alts => ei_outh I d alts
     | DOutM alts => ei_outm I d alts
     | DHalt => ei_halt I d
     | DIn Sin => ei_in I d Sin
     | DInE Sin => ei_in_e I d Sin
     | DInEnd => ei_in_end I d
     end)
    ∗ dev_res I dv (ds ∖ {[d]}).
  Proof using . intros Hd. unfold dev_res. by apply big_sepS_delete. Qed.

  (* changing one device's spec changes nothing outside it *)
  Lemma dev_res_set (I : ep_iface) (dv : nat -> dspec) (ds : gset nat) (d : nat)
      (x : dspec) :
    d ∉ ds ->
    dev_res I (fun d' => if decide (d' = d) then x else dv d') ds ⊣⊢ dev_res I dv ds.
  Proof using .
    intros Hd. unfold dev_res. apply big_sepS_proper. intros d' Hd'.
    rewrite decide_False; [reflexivity |]. intros ->. done.
  Qed.

  Lemma env_set_dev_pe_dev (E : penv) (d : nat) (x : dspec) :
    pe_dev (env_set_dev E d x) = fun d' => if decide (d' = d) then x else pe_dev E d'.
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  THE ONCE-GLUE                                                   *)
  (* ------------------------------------------------------------------- *)

  (* the invariant: a conforming tree at its environment, or a tree the
     taint already pays *)
  Definition cf_inv (I : ep_iface) (t : proc) : iProp Σ :=
    ((∃ (E : penv) (ds : gset nat), ⌜conforms E t⌝ ∗ env_res I E ds)
     ∨ tree_pay N P t)%I.

  Lemma cf_inv_taint (I : ep_iface) (t : proc) : ei_taint I -∗ cf_inv I t.
  Proof using . iIntros "Ht". iRight. iApply (ei_taint_pays I with "Ht"). Qed.

  (* a taint arm of a law, at the invariant *)
  Local Ltac taint_arm I := iIntros (x) "Ht"; iApply (cf_inv_taint I with "Ht").

  (* the invariant rebuilt after one device moved to a new spec, the rest
     of the environment unchanged *)
  Lemma cf_inv_move (I : ep_iface) (E : penv) (ds : gset nat) (d : nat)
      (x : dspec) (t : proc) :
    d ∈ ds ->
    conforms (env_set_dev E d x) t ->
    (forall fd d', pe_fd E fd = Some d' -> d' ∈ ds) ->
    ei_fds I (pe_fd E) -∗ ei_files I (pe_files E) -∗
    (match x with
     | DOut alts => ei_out I d alts
     | DOutH alts => ei_outh I d alts
     | DOutM alts => ei_outm I d alts
     | DHalt => ei_halt I d
     | DIn Sin => ei_in I d Sin
     | DInE Sin => ei_in_e I d Sin
     | DInEnd => ei_in_end I d
     end) -∗
    dev_res I (pe_dev E) (ds ∖ {[d]}) -∗
    cf_inv I t.
  Proof using .
    intros Hin Hc Hdom. iIntros "Hfds Hfiles Hx Hrest".
    iLeft. iExists (env_set_dev E d x), ds.
    iSplit; [done |]. iSplit; [done |]. iFrame "Hfds Hfiles".
    rewrite (dev_res_take I _ ds d Hin). iSplitL "Hx".
    { rewrite env_set_dev_pe_dev decide_True; [| reflexivity]. iExact "Hx". }
    assert (Hnot : d ∉ ds ∖ {[d]}) by set_solver.
    rewrite env_set_dev_pe_dev (dev_res_set I (pe_dev E) (ds ∖ {[d]}) d _ Hnot).
    iExact "Hrest".
  Qed.

  Lemma cf_inv_step (I : ep_iface) :
    ⊢ □ (∀ t, cf_inv I t -∗ tree_F N P (cf_inv I) t).
  Proof using .
    iIntros "!>" (t) "[(%E & %ds & %Hc & %Hdom & Hfds & Hfiles & Hdev) | Hpay]"; last first.
    { (* the taint pays: unfold, and every subtree is paid *)
      rewrite tree_pay_unfold.
      iApply (tree_F_mono_law N P (tree_pay N P) (cf_inv I) with "[] Hpay").
      iIntros "!>" (t') "Ht'". iRight. iExact "Ht'". }
    apply conforms_unfold in Hc. destruct t as [v | t' | e k].
    - destruct v.
    - (* Tau *)
      simpl in Hc. simpl. iLeft. iExists E, ds. iFrame. done.
    - destruct e as [path mode | fd | fd n | fd bs | s]; simpl in Hc; simpl.
      + (* EOpen *)
        destruct Hc as [(-> & content & Hfile & Hk & Hk1) | (Hfile & Hk1)].
        * (* present *)
          iApply (ei_open I (pe_fd E) (pe_files E) path content with "Hfds Hfiles");
            [exact Hfile |].
          iSplit; [| iSplit; [| taint_arm I]].
          { iIntros (fd) "%Hfd0 %Hnone Hbind Hfiles".
            (* a device no descriptor names *)
            set (d := fresh ds).
            assert (Hfr : forall fd', pe_fd E fd' <> Some d).
            { intros fd' Heq. apply Hdom in Heq. apply (is_fresh ds Heq). }
            iDestruct ("Hbind" $! d with "[%]") as "[Hfds Hin]"; [exact Hfr |].
            iLeft. iExists (env_set_dev (env_bind E fd (Some d)) d (DIn content)), ({[d]} ∪ ds).
            iSplit.
            { iPureIntro. apply Hk; [lia | exact Hnone | exact Hfr]. }
            iSplit.
            { iPureIntro. intros fd' d'. cbv [env_set_dev env_bind pe_fd].
              destruct (decide (fd' = fd)) as [-> | Hne].
              - intros [= ->]. set_solver.
              - intros Hin. apply Hdom in Hin. set_solver. }
            iFrame "Hfds Hfiles".
            assert (Hnot : d ∉ ds) by apply is_fresh.
            rewrite (dev_res_take I _ ({[d]} ∪ ds) d ltac:(set_solver)).
            iSplitL "Hin".
            { rewrite env_set_dev_pe_dev decide_True; [| reflexivity]. simpl. iExact "Hin". }
            assert (({[d]} ∪ ds) ∖ {[d]} = ds) as -> by set_solver.
            rewrite env_set_dev_pe_dev (dev_res_set I (pe_dev E) ds d _ Hnot).
            iExact "Hdev". }
          { iIntros "Hfds Hfiles". iLeft. iExists E, ds. iFrame. done. }
        * (* absent *)
          iApply (ei_open_absent I (pe_fd E) (pe_files E) path mode with "Hfds Hfiles");
            [exact Hfile |].
          iSplit; [| taint_arm I].
          iIntros "Hfds Hfiles". iLeft. iExists E, ds. iFrame. done.
      + (* EClose *)
        destruct Hc as (d & Hfd & Hk).
        iApply (ei_close I (pe_fd E) fd d with "Hfds"); [exact Hfd |].
        iSplit; [| taint_arm I].
        iIntros "Hfds". iLeft. iExists (env_bind E fd None), ds. iFrame "Hfds Hfiles Hdev".
        iPureIntro. split; [exact Hk |].
        intros fd' d'. cbv [env_bind pe_fd]. destruct (decide (fd' = fd)); [discriminate |].
        apply Hdom.
      + (* ERead *)
        destruct Hc as (d & Hfd & Hn & Hc).
        assert (Hin : d ∈ ds) by (apply (Hdom fd); exact Hfd).
        iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]".
        destruct Hc as [(Sin & Hd & Hk) | [(Sin & Hd & Hk & Hke) | (Hd & Hk)]]; rewrite Hd.
        * iApply (ei_read I (pe_fd E) fd d Sin n with "Hfds Hdr"); [exact Hn | exact Hfd |].
          iSplit; [| taint_arm I].
          iIntros (c S') "%Hchunk Hfds Hin'".
          iApply (cf_inv_move I E ds d (DIn S') with "Hfds Hfiles Hin' Hrest");
            [exact Hin | by apply Hk | exact Hdom].
        * iApply (ei_read_e I (pe_fd E) fd d Sin n with "Hfds Hdr"); [exact Hn | exact Hfd |].
          iSplit; [| iSplit; [| taint_arm I]].
          { iIntros (c S') "%Hchunk Hfds Hin'".
            iApply (cf_inv_move I E ds d (DInE S') with "Hfds Hfiles Hin' Hrest");
              [exact Hin | by apply Hk | exact Hdom]. }
          { iIntros "Hfds Hend".
            iApply (cf_inv_move I E ds d DInEnd with "Hfds Hfiles Hend Hrest");
              [exact Hin | exact Hke | exact Hdom]. }
        * iApply (ei_read_end I (pe_fd E) fd d n with "Hfds Hdr"); [exact Hn | exact Hfd |].
          iSplit; [| taint_arm I].
          iIntros "Hfds Hend".
          iApply (cf_inv_move I E ds d DInEnd with "Hfds Hfiles Hend Hrest");
            [exact Hin | by rewrite -Hd; destruct E | exact Hdom].
      + (* EWrite *)
        destruct Hc as (d & Hfd & Hc).
        assert (Hin : d ∈ ds) by (apply (Hdom fd); exact Hfd).
        destruct Hc as [(-> & Hk0 & Hk1)
                       | [(Hne & alts & a & Hd & Ha & Hpre & Hk)
                       | [(Hne & alts & a & Hd & Ha & Hpre & Hk & Hkh)
                       | [(Hne & alts & a & Hd & Ha & Hpre & Hk & Hkm)
                       | (Hne & Hd & Hk)]]]].
        * iApply (ei_write_nil I (pe_fd E) fd d with "Hfds"); [exact Hfd |].
          iSplit; [| iSplit; [| taint_arm I]].
          { iIntros "Hfds". iLeft. iExists E, ds. iFrame. done. }
          { iIntros "Hfds". iLeft. iExists E, ds. iFrame. done. }
        * iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]". rewrite Hd.
          iApply (ei_write I (pe_fd E) fd d alts a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Ha | exact Hpre |].
          iSplit; [| taint_arm I].
          iIntros "Hfds Hout".
          iApply (cf_inv_move I E ds d (DOut [drop (length bs) a]) with "Hfds Hfiles Hout Hrest");
            [exact Hin | exact Hk | exact Hdom].
        * iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]". rewrite Hd.
          iApply (ei_write_h I (pe_fd E) fd d alts a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Ha | exact Hpre |].
          iSplit; [| iSplit; [| taint_arm I]].
          { iIntros "Hfds Hout".
            iApply (cf_inv_move I E ds d (DOutH [drop (length bs) a]) with "Hfds Hfiles Hout Hrest");
              [exact Hin | exact Hk | exact Hdom]. }
          { iIntros "Hfds Hh".
            iApply (cf_inv_move I E ds d DHalt with "Hfds Hfiles Hh Hrest");
              [exact Hin | exact Hkh | exact Hdom]. }
        * iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]". rewrite Hd.
          iApply (ei_write_m I (pe_fd E) fd d alts a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Ha | exact Hpre |].
          iSplit; [| iSplit; [| taint_arm I]].
          { iIntros "Hfds Hout".
            iApply (cf_inv_move I E ds d (DOutM [drop (length bs) a]) with "Hfds Hfiles Hout Hrest");
              [exact Hin | exact Hk | exact Hdom]. }
          { iIntros "Hfds Hout".
            iApply (cf_inv_move I E ds d (DOutM [drop (length bs) a]) with "Hfds Hfiles Hout Hrest");
              [exact Hin | exact Hkm | exact Hdom]. }
        * iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]". rewrite Hd.
          iApply (ei_write_halt I (pe_fd E) fd d bs with "Hfds Hdr"); [exact Hne | exact Hfd |].
          iSplit; [| taint_arm I].
          iIntros "Hfds Hh".
          iApply (cf_inv_move I E ds d DHalt with "Hfds Hfiles Hh Hrest");
            [exact Hin | by rewrite -Hd; destruct E | exact Hdom].
      + (* EExit *)
        iApply (ei_exit I s (pe_fd E) (pe_dev E) ds with "Hfds Hdev").
        intros d alts _ Hd'. exact (Hc d alts Hd').
  Qed.

  Theorem tree_pay_of_conforms (I : ep_iface) (E : penv) (ds : gset nat) (t : proc) :
    conforms E t ->
    env_res I E ds -∗ tree_pay N P t.
  Proof using .
    intros Hc. iIntros "Hres".
    iApply (tree_pay_coind N P (cf_inv I) with "[]").
    { iApply cf_inv_step. }
    iLeft. iExists E, ds. by iFrame.
  Qed.

End UkHandler.
