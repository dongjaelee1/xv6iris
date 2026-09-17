(* AppFile.v -- THE FILE APPLICATION, THE CLAIM (layer A): what the file
   [f] may hold, as a resource over the abstract view, with the DEED the
   shell's process chain holds against it.

   Design of record: claude-notes/design/app-file.md (section 2 is this
   file; section 3 is the deed's life, which the program lanes prove).

   THE CLAIM.  [file_pred c r av] is the echo application's predicate
   ([AppEcho.echo_pred]: the taint, or the pins beside the console's state)
   with a FOURTH conjunct, [f_state]: the file [f] in the root directory is
   in the state the deed says -- absent, or present with exactly these
   bytes -- and, when present, its bytes are a chunk subset of an
   [echo … > f] line the console has seen (a lower bound of the ledger's
   line list says which lines those are).

   THE DEED is a [ghost_var] over [FileState.fst] in two halves: the claim
   keeps one, the process chain (sh, its forked child, the exec'd echo or
   cat) the other, beside a TICKET of the same shape.  Agreement makes the
   claim's state KNOWN to the holder -- that is how a write step knows the
   row it appends to is its line's, and how cat knows the bytes it prints
   are the file's.

   A MOVE IS TWO PHASES, exactly the tree layer's ([AppTree] section 7.2 of
   design/user-tree.md), and for the same structural reason: the step a
   fire takes ([AppInv.app_step]) is a wand INTO the claim, so it can park
   the holder's half but cannot hand anything back.  Phase 1
   ([file_step_park], update-free) parks the deed half: the claim's arm
   goes from EXACT (one half, the content at the deed's value) to IN
   FLIGHT (the whole deed at the OLD value, the content at the NEW one).
   Phase 2 ([file_resync], a fancy update at a mask holding [appN], where
   the fire's own phase 2 runs) opens the invariant with the TICKET: the
   in-flight arm is the only one it can meet -- the exact arm is refuted by
   the ticket's agreement against the view's content, the taint arm hands
   the ticket back beside the taint -- and both ghosts move to the new
   value, one half of each returning to the holder.  A READER holding a
   deed half refutes the in-flight arm outright (the whole deed is in it),
   so the deed law reads the exact arm and nothing weakens.

   THE STATE IS THE CONTENT ([FileState.v]'s note): [f_ok av s] determines
   [s] from the view ([f_ok_fcontent]), so the transport allocates the
   copy's fresh ghosts at [fcontent_of av] OUTSIDE the later, exactly as
   [AppEcho.echo_xfer] allocates its flag at [cons_inum av] -- and an
   in-flight original copies to an EXACT copy at the view's content.  The
   pins and the console state ride at the projections, so every console
   lemma of [AppEcho] applies here through [file_pred_cons].

   WHAT IS HERE: the fixed part and the instance names; the line list's
   two shapes; the deed and ticket algebra; [f_ok] and its reading; the
   claim, its timelessness, the deed law; the free step, the two phases,
   the tainted step; the supply off the taint and its converse; the two
   transports (commit and boot); the era-0 claim at the image.  WHAT IS
   NOT HERE (layer B, lane STAGE): the record [app_file], its ledger, tag
   and console interface, which need the stage grown by design section 4. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map invariants.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang RiscvPtsto.
Require Import ObsTrace.
Require Import Xv6Cameras.         (* [bioslotG] *)
Require Import Xv6G.               (* [xv6G] *)
Require Import FdSlots.            (* [fdslotG] *)
Require Import IrefSlots.          (* [irefslotG] *)
Require Import ProcAvail.          (* [pavG] *)
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsImgDisk.
Require Import SystemAdequacy.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsState.
Require Import FsAbsDefs.
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import FsShPin.
Require Import FsEchoPin.
Require Import FsTree.
Require Import FsAbsDelta.
Require Import ConsoleInv.
Require Import FsConsPin.
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import FsBlocks.           (* [fs_names], [fs_top] *)
Require Import FsNode.             (* [fs_node] *)
Require Import FileInvDefs.        (* [fileG] / [file_app]: the era's record *)
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import EchoOut.
Require Import AppEcho.            (* [echo_taint], [echo_cl], [cons_state],
                                      [echo_boot], [echo_pred]'s pieces *)
Require Export FileState.          (* [fst], [echo_chunks], [subseq], [sel_ok] *)
Require Import FileFsPure.         (* [file_fs_pure] = echo's pins and cat's *)
Require Import FsFPin.             (* [f_absent], [era0_recovery_f_absent] *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  NAMES: THE FIXED PART AND THE INSTANCE                             *)
(* ====================================================================== *)

(* a typed line, as the console sees it: the words of one [echo … > f] *)
Definition wordline : Type := list (list (bv 8)).

(* THE FIXED PART: echo's (the taint counter and the era map) beside the
   LINE LIST's name -- a [mono_list] of the [echo … > f] word lists the
   console has received, in order, whose authority the ledger keeps and
   whose lower bounds ride the input tag (design section 4). *)
Definition file_fixed : Type := echo_fixed * gname.

(* THE INSTANCE: echo's console pair beside THE DEED's and THE TICKET's
   names *)
Record file_names := MkFileNames {
  fn_cons : echo_names;
  fn_deed : gname;
  fn_tkt  : gname;
}.

Class fileAppG (Σ : gFunctors) := FileAppG {
  fa_deed : ghost_varG Σ fst;
  fa_fl   : inG Σ (mono_listR (leibnizO wordline));
}.
#[global] Existing Instances fa_deed fa_fl.

Definition fileAppΣ : gFunctors :=
  #[ ghost_varΣ fst; GFunctor (mono_listR (leibnizO wordline)) ].

Global Instance subG_fileAppΣ {Σ} : subG fileAppΣ Σ -> fileAppG Σ.
Proof. solve_inG. Qed.

Section FileClaim.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* ---------------------------------------------------------------- *)
  (*  1a.  THE TAINT, AT THE PROJECTION                                 *)
  (* ---------------------------------------------------------------- *)

  Definition file_taint (c : file_fixed) : iProp Σ := echo_taint c.1.

  Global Instance file_taint_persistent c : Persistent (file_taint c).
  Proof using . rewrite /file_taint. apply _. Qed.
  Global Instance file_taint_timeless c : Timeless (file_taint c).
  Proof using . rewrite /file_taint. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  1b.  THE LINE LIST: authority (the ledger's) and lower bounds     *)
  (* ---------------------------------------------------------------- *)

  Definition fl_auth (c : file_fixed) (ls : list wordline) : iProp Σ :=
    own c.2 (●ML (ls : list (leibnizO wordline))).

  Definition fl_lb (c : file_fixed) (ls : list wordline) : iProp Σ :=
    own c.2 (◯ML (ls : list (leibnizO wordline))).

  Global Instance fl_lb_persistent c ls : Persistent (fl_lb c ls).
  Proof using . rewrite /fl_lb. apply _. Qed.
  Global Instance fl_lb_timeless c ls : Timeless (fl_lb c ls).
  Proof using . rewrite /fl_lb. apply _. Qed.
  Global Instance fl_auth_timeless c ls : Timeless (fl_auth c ls).
  Proof using . rewrite /fl_auth. apply _. Qed.

  Lemma fl_auth_lb (c : file_fixed) (ls : list wordline) :
    fl_auth c ls -∗ fl_auth c ls ∗ fl_lb c ls.
  Proof using .
    rewrite /fl_auth /fl_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML (ls : list (leibnizO wordline))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  Lemma fl_lb_prefix (c : file_fixed) (ls ls' : list wordline) :
    fl_auth c ls -∗ fl_lb c ls' -∗ ⌜ls' `prefix_of` ls⌝.
  Proof using .
    rewrite /fl_auth /fl_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    by iPureIntro.
  Qed.

  (* two lower bounds of one list are comparable *)
  Lemma fl_lb_lb (c : file_fixed) (ls ls' : list wordline) :
    fl_lb c ls -∗ fl_lb c ls' -∗ ⌜ls `prefix_of` ls' \/ ls' `prefix_of` ls⌝.
  Proof using .
    rewrite /fl_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    by iPureIntro.
  Qed.

  Lemma fl_auth_grow (c : file_fixed) (ls : list wordline) (ws : wordline) :
    fl_auth c ls ==∗ fl_auth c (ls ++ [ws]) ∗ fl_lb c (ls ++ [ws]).
  Proof using .
    rewrite /fl_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((ls ++ [ws]) : list (leibnizO wordline)))
            with "Ha") as "Ha".
    { apply mono_list_update. by exists [ws]. }
    iModIntro. iApply (fl_auth_lb with "Ha").
  Qed.

  (* THE BIRTH: echo's counter and era map, and the line list empty *)
  Definition file_cl (c : file_fixed) : iProp Σ :=
    (echo_cl c.1 ∗ fl_auth c [])%I.

  Lemma file_birth : ⊢ |==> ∃ c : file_fixed, file_cl c.
  Proof using .
    iMod echo_birth as (γ) "He".
    iMod (own_alloc (●ML ([] : list (leibnizO wordline)))) as (g) "Hl";
      [ apply mono_list_auth_valid |].
    iModIntro. iExists (γ, g). rewrite /file_cl /fl_auth /=. iFrame "He Hl".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2.  THE DEED AND THE TICKET                                       *)
  (* ---------------------------------------------------------------- *)

  Definition fdeed (r : file_names) (s : fst) : iProp Σ :=
    ghost_var (fn_deed r) (1/2) s.
  Definition fdeed_whole (r : file_names) (s : fst) : iProp Σ :=
    ghost_var (fn_deed r) 1 s.
  Definition ftkt (r : file_names) (s : fst) : iProp Σ :=
    ghost_var (fn_tkt r) (1/2) s.

  (* what a holder normally has: both halves, at one value *)
  Definition fown (r : file_names) (s : fst) : iProp Σ :=
    (fdeed r s ∗ ftkt r s)%I.

  Global Instance fdeed_timeless r s : Timeless (fdeed r s).
  Proof using . rewrite /fdeed. apply _. Qed.
  Global Instance fdeed_whole_timeless r s : Timeless (fdeed_whole r s).
  Proof using . rewrite /fdeed_whole. apply _. Qed.
  Global Instance ftkt_timeless r s : Timeless (ftkt r s).
  Proof using . rewrite /ftkt. apply _. Qed.
  Global Instance fown_timeless r s : Timeless (fown r s).
  Proof using . rewrite /fown. apply _. Qed.

  Lemma fdeed_agree (r : file_names) (s s' : fst) :
    fdeed r s -∗ fdeed r s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /fdeed. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  Lemma ftkt_agree (r : file_names) (s s' : fst) :
    ftkt r s -∗ ftkt r s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /ftkt. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  (* a half beside the whole is three halves: the exclusion the reader's
     law and the parking step both run on *)
  Lemma fdeed_whole_excl (r : file_names) (s s' : fst) :
    fdeed r s -∗ fdeed_whole r s' -∗ False.
  Proof using .
    rewrite /fdeed /fdeed_whole. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    iPureIntro. rewrite Qp.add_comm in Hq. exact (Qp.not_add_le_l _ _ Hq).
  Qed.

  Lemma fdeed_join (r : file_names) (s s' : fst) :
    fdeed r s -∗ fdeed r s' -∗ fdeed_whole r s.
  Proof using .
    iIntros "H1 H2". iDestruct (fdeed_agree with "H1 H2") as %<-.
    rewrite /fdeed /fdeed_whole.
    assert (Heq : (1 : Qp) = (1/2 + 1/2)%Qp) by (symmetry; exact Qp.half_half).
    rewrite Heq. iCombine "H1 H2" as "H". iExact "H".
  Qed.

  Lemma fdeed_split (r : file_names) (s : fst) :
    fdeed_whole r s -∗ fdeed r s ∗ fdeed r s.
  Proof using .
    rewrite /fdeed /fdeed_whole. iIntros "H".
    assert (Heq : (1 : Qp) = (1/2 + 1/2)%Qp) by (symmetry; exact Qp.half_half).
    iEval (rewrite Heq) in "H". iDestruct (ghost_var_split with "H") as "[H1 H2]".
    iFrame "H1 H2".
  Qed.

  Lemma fdeed_whole_update (r : file_names) (s s' : fst) :
    fdeed_whole r s ==∗ fdeed_whole r s'.
  Proof using . rewrite /fdeed_whole. iApply ghost_var_update. Qed.

  Lemma ftkt_update (r : file_names) (s s' s'' : fst) :
    ftkt r s -∗ ftkt r s' ==∗ ftkt r s'' ∗ ftkt r s''.
  Proof using .
    rewrite /ftkt. iIntros "H1 H2".
    iMod (ghost_var_update_halves s'' with "H1 H2") as "[H1 H2]".
    iModIntro. iFrame "H1 H2".
  Qed.

  (* fresh names, both halves of both ghosts, at any value: what every
     transport and the era-0 mint allocate *)
  Lemma fnames_alloc (r1 : echo_names) (s : fst) :
    ⊢ |==> ∃ r : file_names,
        ⌜fn_cons r = r1⌝ ∗ fdeed r s ∗ fdeed r s ∗ ftkt r s ∗ ftkt r s.
  Proof using .
    iMod (ghost_var_alloc s) as (gd) "Hd".
    iMod (ghost_var_alloc s) as (gt) "Ht".
    iModIntro. iExists (MkFileNames r1 gd gt). rewrite /fdeed /ftkt /=.
    iDestruct "Hd" as "[Hd1 Hd2]". iDestruct "Ht" as "[Ht1 Ht2]".
    iFrame "Hd1 Hd2 Ht1 Ht2". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  THE FILE'S STATE ON THE VIEW                                  *)
  (* ---------------------------------------------------------------- *)

  (* the content the view holds at [f]: the file's bytes at the inum the
     root's entry [f] names, [None] when there is no such entry -- or when
     the row is not a plain file, which [f_ok] excludes *)
  Definition fcontent_of (av : aview) : fst :=
    match astep av FsImg.ROOTINO fname_f with
    | None => None
    | Some i =>
        match av !! i with
        | Some (MkAnode (AFile bs) _) => Some bs
        | _ => None
        end
    end.

  (* [f] is absent, or it is a plain file with exactly these bytes and one
     link.  The link count is pinned at 1 because the application never
     links [f] (a link by an unverified process is an unpaid move: taint),
     and the pinned observation the read runs on wants the row on the
     nose. *)
  Definition f_ok (av : aview) (s : fst) : Prop :=
    match s with
    | None => f_absent av
    | Some bs =>
        exists i : Z,
          astep av FsImg.ROOTINO fname_f = Some i
          /\ av !! i = Some (MkAnode (AFile bs) 1%nat)
    end.

  Lemma f_ok_fcontent (av : aview) (s : fst) :
    f_ok av s -> fcontent_of av = s.
  Proof using .
    rewrite /f_ok /fcontent_of. destruct s as [bs |].
    - intros (i & Hs & Hrow). by rewrite Hs Hrow.
    - rewrite /f_absent. intros Hs. by rewrite Hs.
  Qed.

  (* the bytes are a chunk subset of one of these lines *)
  Definition f_bytes_typed (ls : list wordline) (bs : list (bv 8)) : Prop :=
    exists (ws : wordline) (sel : list nat),
      ws ∈ ls /\ sel_ok (echo_chunks ws) sel /\ bs = subseq (echo_chunks ws) sel.

  Lemma f_bytes_typed_mono (ls ls' : list wordline) (bs : list (bv 8)) :
    ls `prefix_of` ls' -> f_bytes_typed ls bs -> f_bytes_typed ls' bs.
  Proof using .
    intros Hp (ws & sel & Hin & Hsel & Hbs). exists ws, sel.
    split; [| by split]. eapply elem_of_prefix; [exact Hin | exact Hp].
  Qed.

  (* ...as the claim carries it: nothing at an absent file, a lower bound
     of the line list and the pure fact at a present one.  The lower bound
     sits only in the [Some] arm: a lower bound of the fixed-part list is
     not mintable from nothing ([◯ML []] is not a unit), and era 0 has no
     [f]. *)
  Definition f_typed (c : file_fixed) (s : fst) : iProp Σ :=
    match s with
    | None => emp
    | Some bs => (∃ ls : list wordline, fl_lb c ls ∗ ⌜f_bytes_typed ls bs⌝)%I
    end.

  Global Instance f_typed_persistent c s : Persistent (f_typed c s).
  Proof using . destruct s; rewrite /f_typed; apply _. Qed.
  Global Instance f_typed_timeless c s : Timeless (f_typed c s).
  Proof using . destruct s; rewrite /f_typed; apply _. Qed.

  (* the two ways a process re-proves the typed fact at a new content *)
  Lemma f_typed_none (c : file_fixed) : ⊢ f_typed c None.
  Proof using . by rewrite /f_typed. Qed.

  Lemma f_typed_some (c : file_fixed) (ls : list wordline) (ws : wordline)
      (sel : list nat) :
    ws ∈ ls -> sel_ok (echo_chunks ws) sel ->
    fl_lb c ls -∗ f_typed c (Some (subseq (echo_chunks ws) sel)).
  Proof using .
    intros Hin Hsel. iIntros "#Hlb". rewrite /f_typed. iExists ls.
    iFrame "Hlb". iPureIntro. by exists ws, sel.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4.  THE CLAIM                                                     *)
  (* ---------------------------------------------------------------- *)

  (* EXACT: the claim's halves at the content.  IN FLIGHT: the whole deed
     at the OLD value, the ticket's half at the old value, the content at
     the NEW one -- the window between a fire's two phases. *)
  Definition f_state (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    ((∃ s : fst, fdeed r s ∗ ftkt r s ∗ f_typed c s ∗ ⌜f_ok av s⌝)
     ∨ (∃ s s' : fst, fdeed_whole r s ∗ ftkt r s ∗ f_typed c s' ∗ ⌜f_ok av s'⌝))%I.

  Global Instance f_state_timeless c r av : Timeless (f_state c r av).
  Proof using . rewrite /f_state. apply _. Qed.

  (* THE PREDICATE: tainted, or the four binaries are the image's AND the
     console is in one of its states AND [f] is in the deed's state. *)
  Definition file_pred (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    (file_taint c
     ∨ (⌜file_fs_pure av⌝ ∗ cons_state (fn_cons r) av ∗ f_state c r av))%I.

  Global Instance file_pred_timeless c r av : Timeless (file_pred c r av).
  Proof using . rewrite /file_pred. apply _. Qed.

  (* the exact arm, as the transports and the era mint build it *)
  Lemma file_pred_exact (c : file_fixed) (r : file_names) (av : aview) (s : fst) :
    file_fs_pure av -> f_ok av s ->
    cons_state (fn_cons r) av -∗ fdeed r s -∗ ftkt r s -∗ f_typed c s -∗
    file_pred c r av.
  Proof using .
    intros Hp Hok. iIntros "Hc Hd Ht #Hty". rewrite /file_pred. iRight.
    iSplitR; [ by iPureIntro |]. iFrame "Hc". rewrite /f_state. iLeft.
    iExists s. iFrame "Hd Ht Hty". by iPureIntro.
  Qed.

  (* THE ECHO APPLICATION'S CLAIM IS THIS ONE WITH THE FILE FORGOTTEN --
     which is what lets every console law [AppEcho] proves at [echo_pred]
     be read here: open, apply, close with the file conjunct framed.
     Stated as an ACCESSOR so that nothing is lost. *)
  Lemma file_pred_cons (c : file_fixed) (r : file_names) (av : aview) :
    file_pred c r av -∗
    echo_pred c.1 (fn_cons r) av ∗
    (echo_pred c.1 (fn_cons r) av -∗ file_pred c r av).
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (%Hp & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iIntros "_". by iLeft. }
    iSplitL "Hc".
    { iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp). }
    iIntros "[#Ht | (_ & Hc)]".
    { by iLeft. }
    iRight. iFrame "Hc Hf". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4a.  THE DEED LAW: what a holder reads off the claim              *)
  (* ---------------------------------------------------------------- *)

  (* LINEAR, [AppEcho.echo_cons_abs_law]'s shape and
     [PinnedObs.pobs_walk_dead]'s premise: the deed goes in and comes back,
     and the fact is the claim's file state at the deed's value, with its
     typed witness -- or the taint.  A holder of a half meets no in-flight
     arm. *)
  Lemma file_deed_law (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (s : fst),
           fdeed r s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdeed r s ∗
           ((⌜f_ok v s⌝ ∗ f_typed c s) ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v s) "Hd Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iFrame "Hd". by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hw & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hw") as %[]. }
    iDestruct "Hf" as (s') "(Hd' & Ht & #Hty & %Hok)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iSplitL "Hc Hd' Ht".
    { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc". iLeft. iExists s.
      iFrame "Hd' Ht Hty". by iPureIntro. }
    iFrame "Hd". iLeft. iFrame "Hty". by iPureIntro.
  Qed.

  (* ...and its pure-only reading *)
  Lemma file_deed_law_pure (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (s : fst),
           fdeed r s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdeed r s ∗ (⌜f_ok v s⌝ ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v s) "Hd Hp".
    iDestruct (file_deed_law c r with "Hd Hp") as "(Hp & Hd & [[%H _] | #Ht])";
      iFrame "Hp Hd"; [ iLeft; by iPureIntro | by iRight ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4b.  THE STEPS                                                    *)
  (*                                                                    *)
  (*  Every view move an application program pays is one of these, at   *)
  (*  the shape [AppInv.app_step] takes.  The pure premises are the     *)
  (*  deltas' business: the fire hands the mover [av] and [av'] and the *)
  (*  lanes prove them from [FsAbsDelta]'s legs.                        *)
  (* ---------------------------------------------------------------- *)

  (* the console's state is carried across a move that leaves the console
     where it was: [cons_state]'s four arms are pure guards over ghosts,
     so a move preserving both pure predicates preserves the arm *)
  Lemma cons_state_mono (r1 : echo_names) (av av' : aview) :
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    cons_state r1 av -∗ cons_state r1 av'.
  Proof using .
    intros Hab Hpr. rewrite /cons_state.
    iIntros "[[%H Htok] | [Hc | [Hc | [%H [Htok Hseal]]]]]".
    - iLeft. iFrame "Htok". iPureIntro. by apply Hab.
    - iDestruct "Hc" as (i) "(%Hp & Hk & Ht)". iRight. iLeft. iExists i.
      iFrame "Hk Ht". iPureIntro. by apply Hpr.
    - iDestruct "Hc" as (i) "(%Hp & Hk & Hs)". iRight. iRight. iLeft.
      iExists i. iFrame "Hk Hs". iPureIntro. by apply Hpr.
    - iRight. iRight. iRight. iFrame "Htok Hseal". iPureIntro. by apply Hab.
  Qed.

  (* the file's state is carried across a move that leaves [f] where it
     was: init's console mknod, every open that creates nothing *)
  Lemma f_state_mono (c : file_fixed) (r : file_names) (av av' : aview) :
    (forall s, f_ok av s -> f_ok av' s) ->
    f_state c r av -∗ f_state c r av'.
  Proof using .
    intros Hok. rewrite /f_state. iIntros "[Hf | Hf]".
    - iDestruct "Hf" as (s) "(Hd & Ht & #Hty & %H)". iLeft. iExists s.
      iFrame "Hd Ht Hty". iPureIntro. by apply Hok.
    - iDestruct "Hf" as (s s') "(Hw & Ht & #Hty & %H)". iRight. iExists s, s'.
      iFrame "Hw Ht Hty". iPureIntro. by apply Hok.
  Qed.

  (* THE FREE STEP: a move that touches neither the console nor [f] --
     what a step wand of [AppInv.app_step]'s shape is built from at every
     such fire, and what a CONSOLE step ([UInitCons]'s four) composes with
     through [file_pred_cons]. *)
  Lemma file_step_free (c : file_fixed) (r : file_names) (av av' : aview) :
    (file_fs_pure av -> file_fs_pure av') ->
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    (forall s, f_ok av s -> f_ok av' s) ->
    file_pred c r av -∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. rewrite /file_pred.
    iIntros "[#Ht | (%Hp & Hc & Hf)]"; [ by iLeft |].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    by iApply (f_state_mono with "Hf").
  Qed.

  (* PHASE 1, THE PARK: the holder's deed half goes in, the arm goes from
     exact to in flight at the new content.  Update-free, so it is
     [AppInv.app_step]'s wand verbatim once lifted by [iModIntro]. *)
  Lemma file_step_park (c : file_fixed) (r : file_names) (av av' : aview)
      (s s' : fst) :
    (file_fs_pure av -> file_fs_pure av') ->
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    (f_ok av s -> f_ok av' s') ->
    fdeed r s -∗ f_typed c s' -∗
    file_pred c r av -∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. iIntros "Hd #Hty' Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hp & Hc & Hf)]"; [ by iLeft |].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    rewrite /f_state.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hw & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hw") as %[]. }
    iDestruct "Hf" as (s0) "(Hd' & Ht & _ & %Hok0)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iDestruct (fdeed_join with "Hd Hd'") as "Hw".
    iRight. iExists s, s'. iFrame "Hw Ht Hty'". iPureIntro. by apply Hok.
  Qed.

  (* THE TAINTED STEP: a holder of the supply moves the view without
     answering for it ([AppInv.app_step_acc]'s consumer shape). *)
  Lemma file_step_taint (c : file_fixed) (r : file_names) (av av' : aview) :
    file_taint c -∗ file_pred c r av -∗ file_pred c r av'.
  Proof using . iIntros "#Ht _". rewrite /file_pred. by iLeft. Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  THE SUPPLY, OFF THE TAINT, AND ITS CONVERSE                   *)
  (* ---------------------------------------------------------------- *)

  Lemma file_sup_of_taint (c : file_fixed) (r : file_names) :
    file_taint c -∗ app_sup_raw (file_pred c) r.
  Proof using .
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /file_pred. by iLeft.
  Qed.

  Lemma file_taint_of_sup (c : file_fixed) (r : file_names) :
    app_sup_raw (file_pred c) r -∗ file_taint c.
  Proof using .
    rewrite /app_sup_raw. iIntros "#Hs".
    iSpecialize ("Hs" $! (∅ : aview)).
    rewrite /file_pred.
    iDestruct "Hs" as "[Ht | [%Hp _]]"; [ iExact "Ht" | ].
    exfalso. apply file_fs_pure_echo in Hp.
    destruct Hp as (_ & (_ & Hc & _) & _).
    by apply lookup_empty_Some in Hc.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  6.  THE TRANSPORTS                                                *)
  (* ---------------------------------------------------------------- *)

  (* the copy's file state is EXACT at the view's own content, whatever
     arm the original is in; the typed witness duplicates *)
  Lemma f_state_copy (c : file_fixed) (r r' : file_names) (av : aview) :
    fdeed r' (fcontent_of av) -∗ ftkt r' (fcontent_of av) -∗
    f_state c r av -∗ f_state c r av ∗ f_state c r' av.
  Proof using .
    iIntros "Hd' Ht'". rewrite /f_state. iIntros "[Hf | Hf]".
    - iDestruct "Hf" as (s) "(Hd & Ht & #Hty & %Hok)".
      pose proof (f_ok_fcontent av s Hok) as Hc.
      iSplitL "Hd Ht".
      + iLeft. iExists s. iFrame "Hd Ht Hty". by iPureIntro.
      + iLeft. iExists (fcontent_of av). iFrame "Hd' Ht'". rewrite Hc.
        iFrame "Hty". by iPureIntro.
    - iDestruct "Hf" as (s s') "(Hw & Ht & #Hty & %Hok)".
      pose proof (f_ok_fcontent av s' Hok) as Hc.
      iSplitL "Hw Ht".
      + iRight. iExists s, s'. iFrame "Hw Ht Hty". by iPureIntro.
      + iLeft. iExists (fcontent_of av). iFrame "Hd' Ht'". rewrite Hc.
        iFrame "Hty". by iPureIntro.
  Qed.

  (* the typed witness at the view's own content, off either arm *)
  Lemma f_state_typed_at (c : file_fixed) (r : file_names) (av : aview) :
    f_state c r av -∗ f_state c r av ∗ f_typed c (fcontent_of av).
  Proof using .
    rewrite /f_state. iIntros "[Hf | Hf]".
    - iDestruct "Hf" as (s) "(Hd & Ht & #Hty & %Hok)".
      rewrite (f_ok_fcontent av s Hok). iSplitL; [| iExact "Hty"].
      iLeft. iExists s. iFrame "Hd Ht Hty". by iPureIntro.
    - iDestruct "Hf" as (s s') "(Hw & Ht & #Hty & %Hok)".
      rewrite (f_ok_fcontent av s' Hok). iSplitL; [| iExact "Hty"].
      iRight. iExists s, s'. iFrame "Hw Ht Hty". by iPureIntro.
  Qed.

  (* the original, read as its echo half and its file half, under the
     later the transports receive it at *)
  Lemma file_pred_split (c : file_fixed) (r : file_names) (av : aview) :
    file_pred c r av -∗
    echo_pred c.1 (fn_cons r) av
    ∗ (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av)).
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (%Hp & Hc & Hf)]".
    { iSplitR; by iLeft. }
    iSplitL "Hc".
    { iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp). }
    iRight. iFrame "Hf". by iPureIntro.
  Qed.

  (* ...and put back together, at any console pair the echo half came
     back at *)
  Lemma file_pred_join (c : file_fixed) (r : file_names) (av : aview) :
    echo_pred c.1 (fn_cons r) av -∗
    (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av)) -∗
    file_pred c r av.
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (_ & Hc)] [#Ht' | (%Hp & Hf)]"; try by iLeft.
    iRight. iFrame "Hc Hf". by iPureIntro.
  Qed.

  (* THE COMMIT'S TRANSPORT ([App.Happ_xfer]): the echo half by echo's
     transport, the file half by a fresh deed and ticket allocated at the
     view's content OUTSIDE the later.  The copy's console pair is the one
     echo's transport chose. *)
  Lemma file_xfer (c : file_fixed) : ⊢ app_xfer_raw (file_pred c).
  Proof using .
    rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iDestruct (echo_xfer c.1) as "#Hex".
    iAssert (▷ (echo_pred c.1 (fn_cons r) av
                ∗ (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av))))%I
      with "[H]" as "[He Hrest]".
    { iNext. by iApply file_pred_split. }
    iMod ("Hex" $! (fn_cons r) av with "He") as "[He He']".
    iDestruct "He'" as (rc) "He'".
    iMod (fnames_alloc rc (fcontent_of av)) as (r') "(%Hrc & Hd1 & _ & Ht1 & _)".
    iModIntro.
    iAssert (▷ (file_pred c r av ∗ file_pred c r' av))%I
      with "[He He' Hrest Hd1 Ht1]" as "[H1 H2]"; last first.
    { iFrame "H1". iExists r'. iExact "H2". }
    iNext.
    iDestruct "Hrest" as "[#Ht | (%Hp & Hf)]".
    { iSplitL "He".
      { iApply (file_pred_join with "He"). by iLeft. }
      iApply (file_pred_join with "[He']").
      { rewrite Hrc. iExact "He'". }
      by iLeft. }
    iDestruct (f_state_copy c r r' av with "Hd1 Ht1 Hf") as "[Hf Hf']".
    iSplitL "He Hf".
    { iApply (file_pred_join with "He"). iRight. iFrame "Hf". by iPureIntro. }
    iApply (file_pred_join with "[He']").
    { rewrite Hrc. iExact "He'". }
    iRight. iFrame "Hf'". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  6a.  THE BOOT RESOURCE, AND THE BOOT TRANSPORT                    *)
  (* ---------------------------------------------------------------- *)

  (* WHAT /init IS HANDED AT THE ERA MINT: echo's (the console key or
     flag) and THE DEED -- both halves the process chain owns, at the
     clone's content -- beside the typed witness of that content, or the
     taint.  The witness sits under ONE later: it is read off the
     original arm, which the transport only sees under [▷]; /init strips
     it at its first step, everything under it being timeless. *)
  Definition file_boot (c : file_fixed) (k : nat) (r : file_names) : iProp Σ :=
    (echo_boot c.1 k (fn_cons r)
     ∗ ∃ s : fst, fown r s ∗ ▷ (f_typed c s ∨ file_taint c))%I.

  Lemma file_xfer_boot (c : file_fixed) (k : nat) :
    ⊢ □ (∀ (r : file_names) (av : aview),
           ▷ file_pred c r av ==∗ ▷ file_pred c r av ∗
           ∃ r' : file_names, ▷ file_pred c r' av ∗ file_boot c k r').
  Proof using .
    iIntros "!>" (r av) "H".
    iDestruct (echo_xfer_boot c.1 k) as "#Hex".
    iAssert (▷ (echo_pred c.1 (fn_cons r) av
                ∗ (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av))))%I
      with "[H]" as "[He Hrest]".
    { iNext. by iApply file_pred_split. }
    iMod ("Hex" $! (fn_cons r) av with "He") as "[He He']".
    iDestruct "He'" as (rc) "[He' Hb]".
    iMod (fnames_alloc rc (fcontent_of av)) as (r') "(%Hrc & Hd1 & Hd2 & Ht1 & Ht2)".
    iModIntro.
    iAssert (▷ (file_pred c r av ∗ file_pred c r' av
                ∗ (f_typed c (fcontent_of av) ∨ file_taint c)))%I
      with "[He He' Hrest Hd1 Ht1]" as "(H1 & H2 & H3)"; last first.
    { iFrame "H1". iExists r'. iFrame "H2". rewrite /file_boot Hrc. iFrame "Hb".
      iExists (fcontent_of av). rewrite /fown. iFrame "Hd2 Ht2 H3". }
    iNext.
    iDestruct "Hrest" as "[#Ht | (%Hp & Hf)]".
    { iSplitL "He"; [ iApply (file_pred_join with "He"); by iLeft |].
      iSplitL "He'"; [| by iRight ].
      iApply (file_pred_join with "[He']").
      { rewrite Hrc. iExact "He'". }
      by iLeft. }
    iDestruct (f_state_typed_at with "Hf") as "[Hf #Hty]".
    iDestruct (f_state_copy c r r' av with "Hd1 Ht1 Hf") as "[Hf Hf']".
    iSplitL "He Hf".
    { iApply (file_pred_join with "He"). iRight. iFrame "Hf". by iPureIntro. }
    iSplitL "He' Hf'"; [| by iLeft ].
    iApply (file_pred_join with "[He']").
    { rewrite Hrc. iExact "He'". }
    iRight. iFrame "Hf'". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  7.  THE ERA-0 CLAIM                                               *)
  (* ---------------------------------------------------------------- *)

  (* at the map a boot founds its file system at, when the disk is mkfs's
     image: echo's era-0 claim (its console key beside it, unused here)
     with [f] absent and the deed at [None] *)
  Lemma file_init (c : file_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : file_names, file_pred c r (abs_view (fss_inodes S)).
  Proof using .
    intros Hdk Hrec HS.
    iMod (echo_init c.1 dk D S Hdk Hrec HS) as (rc) "He".
    iMod (fnames_alloc rc None) as (r) "(%Hrc & Hd1 & _ & Ht1 & _)".
    iModIntro. iExists r.
    iApply (file_pred_join with "[He]").
    { rewrite Hrc. iExact "He". }
    iRight. iSplitR.
    { iPureIntro. exact (file_fs_era0 dk D S Hdk Hrec HS). }
    rewrite /f_state. iLeft. iExists None.
    iSplitL "Hd1"; [ iExact "Hd1" |].
    iSplitL "Ht1"; [ iExact "Ht1" |].
    iSplitR; [ by rewrite /f_typed |].
    iPureIntro. exact (era0_recovery_f_absent dk D S Hdk Hrec HS).
  Qed.

  (* ...at the theorem's own literal shape ([App.xv6_app_adequacy]'s
     [Happ_init]), [AppEcho.echo_init_img]'s composition verbatim *)
  Lemma file_init_img (c : file_fixed) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_blocks dk = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    ⊢ |==> ∃ r : file_names,
        file_pred c r (abs_view (fss_inodes
          (FsDurImg.img_state (fs_blocks dk) sb nib))).
  Proof using .
    intros Himg Hdk -> ->.
    pose proof (img_snap_ok dk ndisk fsimg_sb nib fsimg_cov Himg) as HS.
    rewrite Hdk in HS. rewrite Hdk.
    exact (file_init c dk era0_D _ Hdk (era0_recovery dk Hdk) HS).
  Qed.
End FileClaim.

(* ====================================================================== *)
(*  8.  THE STEPS AT THE ERA'S RECORD                                      *)
(*                                                                        *)
(*  [AppInv.app_step] and [app_inv] name the era's record ([file_app]) and *)
(*  the kernel's classes; the two shapes a fire consumes are stated here, *)
(*  at the context [TreeMove] uses for the same two.                       *)
(* ====================================================================== *)
Section FileClaimEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* ...at [AppInv.app_step]'s own shape, with the record equation the era
     carries: the fire hands the mover the node it chose and the mover
     answers with the step.  [tree_app_step_of]'s twin. *)
  Lemma file_app_step_park (c : file_fixed) (r : file_names)
      (i : Z) (I : gmap Z fs_node) (av' : aview) (s s' : fst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (file_fs_pure (abs_view I) -> file_fs_pure av') ->
    (cons_absent (abs_view I) -> cons_absent av') ->
    (forall j, cons_present_at j (abs_view I) -> cons_present_at j av') ->
    (f_ok (abs_view I) s -> f_ok av' s') ->
    fdeed r s -∗ f_typed c s' -∗ app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. iIntros "Hd #Hty'". rewrite /app_step.
    iIntros (n') "%Hav Hp". rewrite Heq. cbn [app_pred app_run app_names].
    rewrite Hav. iModIntro. iNext.
    iApply (file_step_park c r _ _ s s' Hpins Hab Hpr Hok with "Hd Hty' Hp").
  Qed.

  (* PHASE 2, THE RESYNC: at the era's record, inside the fire's own fupd
     (the mask holds [appN]), the ticket buys both ghosts at the content
     the post view actually has -- or the taint hands the ticket back. *)
  Lemma file_resync (γfs : fs_names) (c : file_fixed)
      (r : file_names) (s s' : fst) (I' : gmap Z fs_node) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    fcontent_of (abs_view I') = s' -> s <> s' ->
    app_inv γfs -∗ ftkt r s -∗
    ghost_map_auth (fs_top γfs) (1/2) I' ={E}=∗
      ghost_map_auth (fs_top γfs) (1/2) I' ∗
      (fown r s' ∨ (ftkt r s ∗ file_taint c)).
  Proof using .
    intros HE Heq Hcont Hne. iIntros "#Hinv Htk Hka".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { (* TAINTED: the ticket comes back beside the taint *)
      iMod ("Hclose" with "[Hh Hx]") as "_".
      { iNext. rewrite /app_body. iExists I'. iFrame "Hh Hx".
        rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
        iSplitL; [ by iLeft | by iPureIntro ]. }
      iModIntro. iFrame "Hka". iRight. iFrame "Htk Ht". }
    rewrite /f_state.
    iDestruct "Hf" as "[Hf | Hf]".
    { (* EXACT: refuted -- the ticket says the claim's value is the OLD
         content, the view says the content moved *)
      iDestruct "Hf" as (s0) "(Hd & Ht' & _ & %Hok)".
      iDestruct (ftkt_agree with "Htk Ht'") as %<-.
      exfalso. apply Hne. rewrite -Hcont. symmetry. exact (f_ok_fcontent _ _ Hok). }
    iDestruct "Hf" as (s0 s1) "(Hw & Ht' & #Hty & %Hok)".
    iDestruct (ftkt_agree with "Htk Ht'") as %<-.
    assert (Hs1 : s1 = s') by (rewrite -Hcont; symmetry; exact (f_ok_fcontent _ _ Hok)).
    subst s1.
    iMod (fdeed_whole_update r s s' with "Hw") as "Hw".
    iDestruct (fdeed_split with "Hw") as "[Hd1 Hd2]".
    iMod (ftkt_update r s s s' with "Htk Ht'") as "[Htk Ht']".
    iMod ("Hclose" with "[Hh Hx Hc Hd2 Ht']") as "_".
    { iNext. rewrite /app_body. iExists I'. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names].
      iApply (file_pred_exact c r _ s' Hpins Hok with "Hc Hd2 Ht' Hty"). }
    iModIntro. iFrame "Hka". iLeft. rewrite /fown. iFrame "Hd1 Htk".
  Qed.

End FileClaimEra.
