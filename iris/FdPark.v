(* FdPark.v -- THE BOUNDARY PARK: what a process SURRENDERS when its
   descriptor table crosses fork or exec, and what the kernel does with it.

   design/user-read.md SS8.3 is the design of record; SS8.1 is why it
   exists.  The one-sentence version: HELD MODE MEANS "NOBODY ELSE MOVES
   MY OFFSET", so a descriptor that reaches code outside the owner's WP --
   a forked child, an exec'd image -- is precisely one whose offset the
   owner no longer controls.  The two crossings are therefore where a held
   half has to go back to being anybody's.

   THREE PIECES, in the order a boundary uses them:

   1. [fdst_park] / [fdv_park] -- the PURE park of a state and of a table:
      a held inode row becomes its parked twin, everything else is itself.
      [fdv_park_id] says the function is the identity on an all-parked
      table, which is what makes every lemma below VACUOUS today
      ([FileInvDefs.fdstate_ok] pins every live inode row at [OffParked],
      so no table in the tree has a held row to park).

   2. [uoff_surr] / [uoff_surrs] -- the SURRENDER: one [UserOff.uoff] per
      HELD row and nothing at all elsewhere.  Stated as a big-op over the
      table so that it QUANTIFIES over the held subset rather than naming
      it, and degenerates to [emp] at an all-parked table
      ([uoff_surrs_parked]) -- which is what lets today's callers of the
      fork and exec rows discharge the new premise by [emp]-introduction.

   3. [foff_rows_park] / [fd_frags_park] -- the KERNEL'S STEP: rebuild the
      descriptor bundle's offset row from each surrendered half
      ([UserOff.uoff_park] into [FdSlots.foff_row_inode], which is
      SS8.3's "one step") and retype the state held -> parked
      ([FdSlots.fd_st_move], which needs both halves -- the authority the
      process block keeps beside the [ofile] cell and the fragment the
      bundle carries).

   WHAT IS NOT HERE, AND WHY IT CANNOT BE (RA-3's finding).  The retype
   above moves the fd-state ghost and NOT [ProcInv.ofile_slot]'s file
   disjunct, whose [st] is shared with [FileInvDefs.file_ref γf k q st] --
   and [file_ref] carries [fdstate_ok], which PINS [OffParked].  So under
   the pin a held row cannot appear in a live [ofile_slot] at all: the
   array-level half of the retype is not merely vacuous, it is
   uninhabited, and writing it means moving [file_ref]'s state, which is
   the same act as relaxing the pin.  That is RA-2's commit by
   construction (design/user-read.md SS8.1's AS-LANDED block: "wiring mode
   [hand] is exactly the act of relaxing that conjunct").  Everything in
   this file is stated at the ghost level the pin does not reach, so it
   lands now and activates then.  (* RA-2: held case here *)

   Design of record: claude-notes/design/user-read.md SS8.3 (the boundary
   parks), SS8.1 (the all-parked discipline the crossings maintain), SS4
   (the PARK ruling these enforce by construction rather than by
   politeness). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvPtsto.    (* [riscvGS] -- the [invGS] the parked row lives at *)
Require Import Xv6Cameras.    (* [offboxG] / [fdslotG] -- the two pinned classes  *)
Require Import OffGv.         (* [off_user_inv]                                   *)
Require Import UserOff.       (* [uoff], [uoff_park]                              *)
Require Import FdSlots.       (* [fdstate], [foff_row], [fd_frags], [fd_st_move]  *)

(* ===================================================================== *)
(*  1.  THE PARK OF A STATE, AND OF A TABLE (pure)                        *)
(* ===================================================================== *)

(* A held inode row's parked twin; every other row is its own.  Note it is
   a TOTAL function of the state and not a relation: the boundary does not
   get to choose which rows it parks, it parks all of them. *)
Definition fdst_park (st : fdstate) : fdstate :=
  match st with
  | FdOpen r w (FdInode i γo _) => FdOpen r w (FdInode i γo OffParked)
  | _ => st
  end.

Definition fdv_park (sts : list fdstate) : list fdstate := fdst_park <$> sts.

Lemma fdst_park_parked (st : fdstate) : fdst_parked (fdst_park st).
Proof. destruct st as [| r w [i g [|] | | mj]]; exact I. Qed.

(* ...AND IT IS THE IDENTITY WHERE THE DISCIPLINE ALREADY HOLDS.  This is
   the vacuity, in one line: with [FileInvDefs.fdstate_ok] pinning every
   live inode row at [OffParked], every table the kernel meets is
   all-parked, so every park below is a no-op on the table it moves. *)
Lemma fdst_park_id (st : fdstate) : fdst_parked st -> fdst_park st = st.
Proof. destruct st as [| r w [i g [|] | | mj]]; [done | done | done | done | done]. Qed.

Lemma fdv_park_id (sts : list fdstate) :
  fdv_all_parked sts -> fdv_park sts = sts.
Proof.
  intros H. unfold fdv_park. induction sts as [| st sts IH]; [reflexivity |].
  apply Forall_cons in H as [Hst Hsts].
  cbn [fmap list_fmap]. rewrite (fdst_park_id st Hst) (IH Hsts). reflexivity.
Qed.

Lemma fdv_all_parked_park (sts : list fdstate) : fdv_all_parked (fdv_park sts).
Proof.
  unfold fdv_all_parked, fdv_park. apply Forall_lookup.
  intros j y Hy. apply list_lookup_fmap_Some in Hy as (st & _ & ->).
  apply fdst_park_parked.
Qed.

Lemma fdv_park_length (sts : list fdstate) :
  length (fdv_park sts) = length sts.
Proof. apply length_fmap. Qed.

Lemma fdv_park_lookup (sts : list fdstate) (fd : nat) (st : fdstate) :
  sts !! fd = Some st -> fdv_park sts !! fd = Some (fdst_park st).
Proof. intros H. unfold fdv_park. rewrite list_lookup_fmap H. reflexivity. Qed.

Lemma fdv_park_insert (sts : list fdstate) (fd : nat) (st : fdstate) :
  fdv_park (<[fd := st]> sts) = <[fd := fdst_park st]> (fdv_park sts).
Proof. unfold fdv_park. apply list_fmap_insert. Qed.

(* ---- the discipline's list kit, in the two shapes a CROSSING wants:
   fork's child table is built by splicing the parent's prefix onto a
   fresh all-closed tail ([ProofKforkB3.kfk_at]), and exec's is the
   caller's own, handed over whole. ---- *)
Lemma fdv_all_parked_app (l1 l2 : list fdstate) :
  fdv_all_parked l1 -> fdv_all_parked l2 -> fdv_all_parked (l1 ++ l2).
Proof. intros H1 H2. unfold fdv_all_parked. by apply Forall_app. Qed.

Lemma fdv_all_parked_take (l : list fdstate) (i : nat) :
  fdv_all_parked l -> fdv_all_parked (take i l).
Proof. intros H. unfold fdv_all_parked. by apply Forall_take. Qed.

Lemma fdv_all_parked_drop (l : list fdstate) (i : nat) :
  fdv_all_parked l -> fdv_all_parked (drop i l).
Proof. intros H. unfold fdv_all_parked. by apply Forall_drop. Qed.

Section FdPark.
  Context `{!riscvGS Σ, !offboxG Σ}.

  (* =================================================================== *)
  (*  2.  THE SURRENDER                                                   *)
  (* =================================================================== *)

  (* WHAT ONE ROW COSTS ITS OWNER AT A BOUNDARY: its half, at whatever
     position the program had reached -- the value is existential because
     the boundary does not care and the program should not have to say.
     A row that is not a HELD inode costs nothing, and that is not a
     special case but the whole content of the discipline: only a held
     row has a half outside the kernel. *)
  Definition uoff_surr (st : fdstate) : iProp Σ :=
    match st with
    | FdOpen _ _ (FdInode _ γo OffHeld) => (∃ off : nat, uoff γo off)%I
    | _ => emp%I
    end.

  (* ...AND THE WHOLE TABLE'S, which is what a boundary row asks for.  It
     QUANTIFIES over the held subset rather than naming it: neither the
     program (whose table lives inside [UkRun.urun]'s existential) nor the
     kernel (whose [sts] is universally quantified) can name that subset,
     and neither has to. *)
  Definition uoff_surrs (sts : list fdstate) : iProp Σ :=
    ([∗ list] st ∈ sts, uoff_surr st)%I.

  (* ...and at the shape a U-TIER row has its descriptors in: the caller's
     own handle map ([UserFd.ufd] per descriptor), not a list. *)
  Definition uoff_surrs_map (D : gmap nat fdstate) : iProp Σ :=
    ([∗ map] _ ↦ st ∈ D, uoff_surr st)%I.

  (* THE DEGENERATION, and it is what makes this lane cheap: at an
     all-parked table the surrender is [emp], so every caller that exists
     today pays it by [emp]-introduction and no existing proof moves. *)
  Lemma uoff_surr_parked (st : fdstate) : fdst_parked st -> ⊢ uoff_surr st.
  Proof.
    intros H. destruct st as [| r w [i g [|] | | mj]]; try (iEmpIntro).
    destruct H.
  Qed.

  Lemma uoff_surrs_parked (sts : list fdstate) :
    fdv_all_parked sts -> ⊢ uoff_surrs sts.
  Proof.
    intros H. rewrite /uoff_surrs. iApply big_sepL_intro.
    iIntros "!>" (k st Hk). iApply uoff_surr_parked.
    exact (fdv_all_parked_lookup sts k st H Hk).
  Qed.

  Lemma uoff_surrs_map_parked (D : gmap nat fdstate) :
    map_Forall (fun _ st => fdst_parked st) D -> ⊢ uoff_surrs_map D.
  Proof.
    intros H. rewrite /uoff_surrs_map. iApply big_sepM_intro.
    iIntros "!>" (fd st Hfd). iApply uoff_surr_parked. exact (H fd st Hfd).
  Qed.

  (* ...AND THE HELD ROW ITSELF, named: what a program that owns an offset
     hands over when it forks or execs.  RA-2's open at mode [hand] is
     what first makes this inhabited. *)
  Lemma uoff_surr_held (r w : bool) (i : Z) (γo : gname) (off : nat) :
    uoff γo off -∗ uoff_surr (FdOpen r w (FdInode i γo OffHeld)).
  Proof. iIntros "H". by iExists off. Qed.

  (* =================================================================== *)
  (*  3.  THE KERNEL'S STEP: the row family, rebuilt                      *)
  (* =================================================================== *)

  (* ONE ROW.  At a held row the surrendered half is parked into the
     invariant and the row's parked twin claims it ([FdSlots.foff_row_inode]
     -- SS8.3's "one step"); at every other row the park is the identity
     and the row that comes back is the row that went in.  Note the mask:
     [UserOff.uoff_park] allocates an invariant and needs no side
     condition, so a boundary may run this at whatever mask it holds. *)
  Lemma foff_row_park (E : coPset) (st : fdstate) :
    foff_row st -∗ uoff_surr st ={E}=∗ foff_row (fdst_park st).
  Proof.
    destruct st as [| r w [i g [|] | | mj]]; cbn [fdst_park uoff_surr].
    - iIntros "$ _". done.
    - iIntros "$ _". done.
    - iIntros "_ Hs". iDestruct "Hs" as (off) "Hu".
      iMod (uoff_park E g off with "Hu") as "#Hinv". iModIntro.
      iApply (foff_row_inode r w i g with "Hinv").
    - iIntros "$ _". done.
    - iIntros "$ _". done.
  Qed.

  (* ...AND THE WHOLE FAMILY.  [foff_rows] is persistent, so what the
     boundary really does is MINT the missing invariants: the rows that
     were already parked come back unchanged and the held ones come back
     as rows at all. *)
  Lemma foff_rows_park (E : coPset) (sts : list fdstate) :
    foff_rows sts -∗ uoff_surrs sts ={E}=∗ foff_rows (fdv_park sts).
  Proof.
    iIntros "#Hrows Hsurr".
    rewrite /foff_rows /uoff_surrs /fdv_park big_sepL_fmap.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hsurr").
    iIntros "!>" (k st Hk) "Hs".
    iApply (foff_row_park E st with "[] Hs").
    iApply (big_sepL_lookup _ _ _ _ Hk with "Hrows").
  Qed.

  (* =================================================================== *)
  (*  4.  THE KERNEL'S STEP: the descriptor states, retyped               *)
  (* =================================================================== *)
  Context `{!fdslotG Σ}.

  (* THE AUTHORITY SIDE OF A WHOLE TABLE.  [ProcInv.ofile_slot] keeps one
     of these per slot beside the [ofile] cell; the bundle
     ([FdSlots.fd_frags]) keeps the matching fragments.  A retype needs
     both ([FdSlots.fd_st_move]), which is SS8.3's "parking is a kernel
     step" in one line. *)
  Definition fd_auths (γ : gname) (sts : list fdstate) : iProp Σ :=
    ([∗ list] fd ↦ st ∈ sts, fd_st_auth γ fd st)%I.

  Lemma fd_auths_parked_id (γ : gname) (sts : list fdstate) :
    fdv_all_parked sts -> fd_auths γ (fdv_park sts) ⊣⊢ fd_auths γ sts.
  Proof. intros H. by rewrite (fdv_park_id sts H). Qed.

  (* THE BOUNDARY PARK, ASSEMBLED: the surrendered halves in, a table
     every one of whose rows is parked out, with the bundle and the
     authorities agreeing on it.  This is the step SS8.3 places BEFORE
     [ProofKforkB3]'s descriptor scan, so that the scan copies parked rows
     only -- which is what dissolves RD-2's consequence (b) ("kfork cannot
     copy a held row": there is nothing persistent to hand the child at a
     held row, and after this step there is no held row).

     UNDER THE PIN IT IS A NO-OP ON THE TABLE ([fdv_park_id]) and the
     surrender is [emp] ([uoff_surrs_parked]); what it costs then is one
     [fd_st_move] per slot at a state equal to itself.  A caller that
     wants even that to disappear takes [fd_frags_park_parked] below. *)
  Lemma fd_frags_park (E : coPset) (γ : gname) (sts : list fdstate) :
    fd_auths γ sts -∗ fd_frags γ sts -∗ uoff_surrs sts ={E}=∗
      fd_auths γ (fdv_park sts) ∗ fd_frags γ (fdv_park sts).
  Proof.
    iIntros "Ha Hb Hs".
    iDestruct "Hb" as "(%Hlen & Hfr & #Hrows)".
    iMod (foff_rows_park E sts with "Hrows Hs") as "#Hrows'".
    rewrite /fd_auths /fd_frags /fdv_park !big_sepL_fmap.
    iAssert ([∗ list] fd ↦ st ∈ sts, (fd_st_auth γ fd st ∗ fd_st γ fd st))%I
      with "[Ha Hfr]" as "Hb2"; [ rewrite big_sepL_sep; iFrame "Ha Hfr" | ].
    iAssert (|==> [∗ list] fd ↦ st ∈ sts,
               (fd_st_auth γ fd (fdst_park st) ∗ fd_st γ fd (fdst_park st)))%I
      with "[Hb2]" as ">Hboth".
    { iApply big_sepL_bupd. iApply (big_sepL_impl with "Hb2").
      iIntros "!>" (fd st Hfd) "[Hau Hfg]".
      iApply (fd_st_move γ fd st st (fdst_park st) with "Hau Hfg"). }
    iModIntro. iEval (rewrite big_sepL_sep) in "Hboth".
    iDestruct "Hboth" as "[$ Hfr']".
    iSplitR; [ iPureIntro; rewrite length_fmap; exact Hlen | ].
    iFrame "Hfr'". rewrite /foff_rows big_sepL_fmap. iExact "Hrows'".
  Qed.

  (* ...and the shape EVERY CALLER IN THE TREE IS AT TODAY: the table is
     already all-parked, so the boundary hands back exactly what it was
     given and no ghost moves at all.  This is the corollary a proof
     applies while the pin stands; RA-2 replaces the application with the
     lemma above, at the surrender its row now carries. *)
  Lemma fd_frags_park_parked (E : coPset) (γ : gname) (sts : list fdstate) :
    fdv_all_parked sts ->
    fd_auths γ sts -∗ fd_frags γ sts ={E}=∗
      fd_auths γ sts ∗ fd_frags γ sts.
  Proof.
    iIntros (Hpk) "Ha Hb". iModIntro. iFrame "Ha Hb".
  Qed.

  (* =================================================================== *)
  (*  5.  THE BOUNDARY SLOT: one step, two suppliers                      *)
  (* =================================================================== *)

  (* WHAT A BOUNDARY ASKS OF THE PROCESS WHOSE TABLE IS CROSSING, in the
     one form BOTH TIERS can pay -- which is the console arm's disjunctive
     precedent (design/user-read.md SS8.1) at fork and exec:

       GENERIC TIER: the left disjunct, a PURE fact -- its table is
         all-parked, which is the discipline that tier maintains as an
         invariant of its own ([UsysMemOk.usys_fd_ok_parked] is the
         maintenance, row by row).  It owns no offset and surrenders
         nothing.
       ENRICHED TIER: the right disjunct, the halves themselves.

     A DISJUNCTION RATHER THAN THE HALVES ALONE, for exactly the reason
     [ConsoleInv.cons_acc] is one: the generic supply is PERSISTENT and
     can never present an exclusive resource, so a slot that demanded the
     halves outright would make the supply law unprovable -- which is what
     [UexecSG.sbundle_of_supply_ne] would have to answer for at fork.

     WHERE IT PLUGS IN, AND WHY NOT YET (RA-3's finding, the mirror of
     RA-1's).  The slot's home is the fork/exec DEPOSIT, stated at the
     key's own table [UexecSlot.uvis_fd W] -- the only carrier that names
     every held row, since a U-tier row sees its caller's handles and not
     its table.  But the generic supply can only pay the LEFT disjunct
     once [sbundle_of_supply_ne] takes the all-parked premise, and that
     premise is RA-2's (it is the same commit as the arm split, for RA-1's
     reason).  So the slot lands HERE, proved and ready, and is plugged
     into the deposit in the commit that first makes a held descriptor
     exist.  (* RA-2: held case here *) *)
  Definition uoff_surr_at (sts : list fdstate) : iProp Σ :=
    (⌜fdv_all_parked sts⌝ ∨ uoff_surrs sts)%I.

  (* SUPPLIER 1 -- the generic tier's, and it is what the narrowed class
     field will hand over: a pure fact, free and persistent. *)
  Lemma uoff_surr_at_parked (sts : list fdstate) :
    fdv_all_parked sts -> ⊢ uoff_surr_at sts.
  Proof. intros H. iLeft. iPureIntro. exact H. Qed.

  (* SUPPLIER 2 -- an owner's: the halves, one per held row. *)
  Lemma uoff_surr_at_held (sts : list fdstate) :
    uoff_surrs sts -∗ uoff_surr_at sts.
  Proof. iIntros "H". by iRight. Qed.

  (* THE STEP, TOTAL: whichever disjunct answered, the table that comes
     out is all-parked and its bundle and authorities agree on it.  This
     is what a boundary proof applies -- fork's, before
     [ProofKforkB3]'s descriptor scan, and exec's, at the table handover
     -- and it never has to know which tier its caller was. *)
  Lemma fd_frags_park_at (E : coPset) (γ : gname) (sts : list fdstate) :
    fd_auths γ sts -∗ fd_frags γ sts -∗ uoff_surr_at sts ={E}=∗
      ∃ sts' : list fdstate,
        ⌜sts' = fdv_park sts⌝ ∗ ⌜fdv_all_parked sts'⌝ ∗
        fd_auths γ sts' ∗ fd_frags γ sts'.
  Proof.
    iIntros "Ha Hb [%Hpk | Hs]".
    - (* the generic tier: the table is already parked, so the park is the
         identity and not one ghost moves ([fdv_park_id]). *)
      iModIntro. iExists (fdv_park sts).
      iSplitR; [done |]. iSplitR; [iPureIntro; apply fdv_all_parked_park |].
      rewrite (fdv_park_id sts Hpk). iFrame "Ha Hb".
    - iMod (fd_frags_park E γ sts with "Ha Hb Hs") as "[Ha Hb]".
      iModIntro. iExists (fdv_park sts).
      iSplitR; [done |]. iSplitR; [iPureIntro; apply fdv_all_parked_park |].
      iFrame "Ha Hb".
  Qed.

  (* =================================================================== *)
  (*  6.  THE ARM'S SUPPLIER AND ITS RECEIPT (SS8.2's kernel half)         *)
  (* =================================================================== *)

  (* WHAT A HELD ROW'S READ OR WRITE GIVES BACK, keyed on the same state
     the payment is keyed on: the half, ADVANCED.  At every other row it
     is the unit, which is what [UserOff.off_supply_parked] leaves behind
     ([R = True]) -- so ONE receipt serves both modes and the arms below
     differ in the state and in nothing else.

     NOTE WHAT THE PAYMENT IS: [uoff_surr] above, unchanged.  The resource
     SS8.2's held arm asks of its caller and the one SS8.3's boundary asks
     of a crossing process are the SAME PROPOSITION at one row -- the
     half, at a position the row does not name -- which is why the two
     halves of RA-2 share this file's vocabulary rather than each growing
     their own.  (The kernel learns the position from its OWN half, by
     agreement, inside the supplier below; neither the payment nor the
     boundary has to say it.) *)
  Definition uoff_rcpt (st : fdstate) (o : nat) : iProp Σ :=
    match st with
    | FdOpen _ _ (FdInode _ γo OffHeld) => uoff γo o
    | _ => True
    end%I.

  Lemma uoff_rcpt_parked (st : fdstate) (o : nat) :
    fdst_parked st -> ⊢ uoff_rcpt st o.
  Proof.
    intros H. destruct st as [| r w [i g [|] | | mj]]; done.
  Qed.

  Lemma uoff_rcpt_held (r w : bool) (i : Z) (γo : gname) (o : nat) :
    uoff γo o -∗ uoff_rcpt (FdOpen r w (FdInode i γo OffHeld)) o.
  Proof. by iIntros "$". Qed.

  (* ...AND THE RECEIPT IS A PAYMENT AGAIN.  This is the one step that
     makes a held descriptor USABLE rather than merely servable: what
     comes back off a read is what the next read -- or the next boundary
     crossing -- is paid with.  "read, read, fork" is this lemma twice and
     [fd_frags_park_at] once. *)
  Lemma uoff_rcpt_surr (st : fdstate) (o : nat) :
    uoff_rcpt st o -∗ uoff_surr st.
  Proof.
    destruct st as [| r w [i g [|] | | mj]]; cbn;
      try (iIntros "_"; by iEmpIntro).
    iIntros "H". by iExists o.
  Qed.

  (* THE SUPPLIER, ASSEMBLED FROM THE ROW AND THE ARM'S PAYMENT, AND IT IS
     WHAT THE MODE-SPLIT ARMS SPEND (design/user-read.md SS8.2).  The two
     fires ([FsAbsReadFire.arf_read_fire_gen],
     [FsAbsWriteFire.wrf_awrite_fire_gen] / [wrf_apart_fire_gen]) each take
     ONE [UserOff.off_supply] and hand back its [R]; this lemma is the
     state-keyed way to build one, so a kernel proof that has branched on
     nothing at all -- it holds the row it always held and the payment its
     contract's inode arm now carries -- gets its supplier and its receipt
     from the descriptor, exactly as [FdSlots.foff_row_inode_of] used to
     give it the invariant.

     THE POSITION IS THE KERNEL'S.  A held payment names its offset under
     an existential and the kernel matches it against its OWN half
     ([UserOff.uoff_agree_k]) rather than against [f->off] -- the two are
     the same value by the off box's own invariant, and this way the arm
     costs the caller no equation.

     WHY IT IS HERE AND NOT IN [SpecFileread]: stating the arms is RA-2's
     one commit, and an import of [UserOff] into the fileread contract
     invalidates its whole cone.  This lemma is the part that can be
     proved without the arms, and it is proved at the GENERAL case -- both
     modes, one statement -- so the arm split spends it instead of
     building it. *)
  Lemma off_supply_of_st (E : coPset) (r w : bool) (i : Z) (γo : gname)
      (m : offmode) (off d : nat) :
    ↑foffN ⊆ E ->
    foff_row (FdOpen r w (FdInode i γo m)) -∗
    uoff_surr (FdOpen r w (FdInode i γo m)) -∗
    off_gv γo (1/2) (Z.of_nat off) -∗
      off_gv γo (1/2) (Z.of_nat off)
      ∗ off_supply γo E off d
          (uoff_rcpt (FdOpen r w (FdInode i γo m)) (off + d)).
  Proof.
    intros HE. destruct m; cbn [foff_row uoff_surr uoff_rcpt].
    - iIntros "#Hinv _ $". iApply (off_supply_parked E γo off d HE with "Hinv").
    - iIntros "_ Hs Hk". iDestruct "Hs" as (o) "Hu".
      iDestruct (uoff_agree_k γo o (Z.of_nat off) with "Hu Hk") as %Heq.
      assert (Ho : o = off) by (apply Nat2Z.inj; symmetry; exact Heq).
      rewrite Ho. iFrame "Hk".
      iApply (off_supply_held E γo off d with "Hu").
  Qed.

  (* ...and the reading a kernel proof actually holds its state at: an
     EQUATION, never a match ([FdSlots.foff_row_inode_of]'s convention, and
     [SpecFileread]'s two [_of] lemmas'). *)
  Lemma off_supply_of_st_eq (E : coPset) (st : fdstate) (r w : bool) (i : Z)
      (γo : gname) (m : offmode) (off d : nat) :
    st = FdOpen r w (FdInode i γo m) ->
    ↑foffN ⊆ E ->
    foff_row st -∗ uoff_surr st -∗ off_gv γo (1/2) (Z.of_nat off) -∗
      off_gv γo (1/2) (Z.of_nat off)
      ∗ off_supply γo E off d (uoff_rcpt st (off + d)).
  Proof.
    intros -> HE. exact (off_supply_of_st E r w i γo m off d HE).
  Qed.

End FdPark.

(* ===================================================================== *)
(*  WHAT RA-2 INHERITS (the held case, in one place)                      *)
(* ===================================================================== *)
(* Every lemma above is stated at the held subset and proved at the
   general case, so the pin's relaxation ACTIVATES them rather than
   changing them.  What RA-2 has to add, and nothing else:
   - the ARRAY half of the retype ([ProcInv.ofile_slot]'s file disjunct
     and [FileInvDefs.file_ref]'s [st], which [fdstate_ok] pins -- see
     this file's header);
   - the PLUG: [uoff_surr_at] into the fork and exec deposits, at the
     key's own table, and the two class fields' all-parked premise that
     lets the generic supply answer its left disjunct.  Those are ONE
     change and not two -- which is RA-3's finding and the exact mirror of
     RA-1's (the arm split and the premise were one change too).  Until
     then no boundary row's STATEMENT moves, and that is why nothing in
     the tree had to be re-proved for this file;
   - at the U tier, the fact that a program's handle map COVERS the held
     subset of its table.  It is true by construction once mode [hand]
     exists -- a held row is born at an open the program asked for, which
     hands it the handle and the half together -- but no row says so
     today, and no U-tier row CAN carry the surrender before it does: a
     [UserFd.ufd] at a held state is not refutable at that tier (the pin
     lives in the file invariant, which the U tier cannot see), so every
     polymorphic wrapper between a program and the fork leaf -- which
     quantifies its descriptor map universally -- would be left holding a
     premise it cannot discharge.  (* RA-2: held case here *) *)

(* ===================================================================== *)
(*  ...AND WHAT RA-2 FOUND WHEN IT RAN (design/user-read.md SS8.4)        *)
(* ===================================================================== *)
(* THE COMMIT DID NOT CLOSE, AND THE THREE LINKS THAT STOPPED IT ARE NOT
   IN THIS FILE -- every lemma above still stands and is still what the
   held case will spend.  In one line each, with SS8.4 as the record:

   1. [hand] AT OPEN IS REFUTED BY THE OPEN-ROW CONJUNCT THIS CAMPAIGN
      ITSELF LANDED.  [UsysMemOk.usys_fd_ok]'s open arm pins
      [fdst_parked] on the ACTUAL successor table, and that relation is
      threaded for BOTH tiers with no tier index ([SpecSyscall.sysc_fd_ok],
      [SpecUsertrap]) -- so a held open kills [ProofSyscall]'s arm 15.  The
      conjunct cannot come off until the generic tier's Loeb step reads
      successor-parkedness somewhere else; the one candidate is the slot's
      own post ([UexecSG.spost_at]'s [fdv'], which the FAMILY chooses).

   2. RELAXING THE PIN DELETES THE ONLY SUPPLIER OF SS8.3's EXEC PREMISE.
      [ProcInv.proc_priv_parked] IS the pin, in three steps
      ([FileInvDefs.fdstate_ok_parked] -> [file_ref_parked] -> the export),
      and SS8.3's finding C discharges [SpecKexec.exec_slot_pre]'s wands
      with it.  The replacement is [fd_frags_park_at]'s own output --
      [fdv_all_parked sts'] at the table exec HANDS OVER -- which restates
      the wands rather than inheriting them.

   3. THE SURRENDER SLOT AT FORK HAS NO PAYER.  fork is a FREE number
      ([UexecSG.free_num]), so its [UexecExecInst.xv6_sbundle] arm is [emp]
      and every verified forker pays through [UkRun.udepw_of_psok] -- whose
      [udepw] quantifies the table UNIVERSALLY and whose left disjunct is a
      pure fact with no table in it.  The class premise does not reach that
      disjunct: it lands on the supply law, which is the GENERIC tier's
      route.  What would reach it is a U-tier HALF OF THE PROCESS'S HELD
      SET -- the third sibling of [UserCwd.ucwd] and [UserChildren.uch] --
      and that is an owner decision (SS8.4). *)
