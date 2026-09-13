(* EchoOut.v -- E5's APPLICATION CLAIM, THE IRIS HALF (lane ECHO-OUT).

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE CONSOLE
   I/O CLAIM: DESIGN OF RECORD", read with the coordinator's LEDGER-ANCHORED
   ruling and its ERA-INDEX follow-up (2026-09-13), and the owner's
   correction to [echo_phi].

   WHY THE STATE IS IN THE LEDGER AND NOT IN THE CLAIMS.  [App.Happ_boot] --
   [SystemAdequacy.app_xfer_boot_raw] -- is fired ONCE PER POWER-ON, its only
   input is the durable claim (which the same shift DUPLICATES), and it is a
   plain [==∗], so no invariant may be opened inside it.  Therefore
   [app_out c ge [] []] and [app_in c ge [] [] []] have to be re-mintable at
   EVERY era out of nothing but freshly allocated ghosts, persistent
   fixed-part facts and pure facts: NO EXCLUSIVE GHOST AT THE FIXED PART MAY
   APPEAR IN EITHER CLAIM.  The application's cross-era state therefore lives
   in the LEDGER [AppEcho.echo_R], which is the application's own resource
   inside the observation invariant, persists across power cycles and already
   sees every power event.  Every link ([WpUart.out_link], [echo_link],
   [in_append], [read_link]) is a fupd at [⊤ ∖ ↑uartN Uart0], so the
   application MAY open [obsN] inside it and reach the ledger; [App.Htx]
   already runs at [⊤ ∖ ↑uartN ∖ ↑obsN] with [app_R] in hand, so it reads
   the ledger directly and never double-opens.

   THE ERA INDEX.  Every claim and every link carries the console port's
   per-era ghost name [ge] ([UartNames.un_app], minted fresh per era; lane
   CONS-IO).  That is what makes "the claim I am handed belongs to MY era" a
   fact of the STATEMENT rather than something a resource would have to
   certify: a writer's obligation is [out_link Uart0 ge b Φ] at its own [ge],
   so it can only ever be applied to the claim at that [ge].  The ledger's
   pin map is keyed BY [ge], so a claim's stage ghost is a FUNCTION of [ge]
   and no injectivity obligation arises.

   THE SHAPE.  The two port claims are, each, one of
     - the TAINT (what the licences pay through), or
     - FRESH: nothing has happened in this era yet (the arm the transport
       founds, from nothing), or
     - PAIRED: the era's persistent pin, one half of that era's stage ghost,
       and either the era's PURE fact or [era_closed] (a dead era's claim,
       which a link must still be able to hand back).
   The ledger holds the pin map's authority, the other halves, and the pure
   consistency between the two stages.  Because the two stages are tied
   inside ONE ledger, the joint facts the shift needs -- E versus
   [echoed pops], the CHAIN-FIRST "append owed" window, "every echo is
   logged", "no re-echo" -- are facts about one state.

   TWO STAGES AND NOT ONE.  A write moves [o_w] with only the OUTPUT claim in
   hand, and [WpUart.in_append] moves [pops] with only the INPUT claim in
   hand, so a single shared ghost value could not be kept in step.  The
   output stage is [(cs, E, w)], the input stage is [(E, owed)], the ledger
   carries the tie, and the echo -- which is the only step that moves [E] --
   holds BOTH claims ([WpUart.echo_link] passes the input claim through). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
(* as in EchoDisc / EchoOutPure: the Sail imports leave string_scope on top
   and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

(* ====================================================================== *)
(*  1.  THE TWO STAGES                                                     *)
(* ====================================================================== *)

(* E's HISTORIES ARE CYCLE SEGMENTS ([open_seg] of the history the byte was
   received at), not whole histories: [EchoOutPure]'s [E_index] counts with
   [ins], the discipline and [good_out] are per POWER CYCLE, and [acc]
   restarts at every era -- so instantiating [E_index] at whole histories is
   unsatisfiable from era 1 on.  Nothing in [EchoOutPure] moves: it is
   parametric in what E's first components are, and this file supplies
   segments ([EchoOutPure.open_seg_ends_in] is the one bridge). *)
Record ostage := MkO {
  o_cs : list nat;
  o_E  : list (list mobs * bv 8);
  o_w  : list (bv 8);
}.

(* [i_owed] is the CHAIN-FIRST window (RULINGS AFTER CONS-IO PHASE 1, (1)):
   between the echo's [out_link]s and the [in_append] that files the entry,
   [i_E] is ONE ENTRY AHEAD of [echoed pops]. *)
Record istage := MkI {
  i_E    : list (list mobs * bv 8);
  i_owed : bool;
}.

Definition ostage0 : ostage := MkO [] [] [].
Definition istage0 : istage := MkI [] false.

(* the OUTPUT claim's pure fact *)
Definition eout_pure (so : ostage) (acc : list (bv 8)) : Prop :=
  acc = D (o_cs so) (o_E so) ++ o_w so
  /\ o_w so `prefix_of` pending (o_cs so) (o_E so)
  /\ E_index (o_E so)
  /\ E_byte (o_E so)
  /\ Forall (fun i => (i < length line_alts)%nat) (o_cs so)
  /\ Forall (fun x => disc_seg x.1) (o_E so).

(* E's entries, read off the log: the ECHOED ones with their histories
   projected to the cycle.  [EchoOutPure.echoed] keeps the raw histories --
   which is what [read_window_prefix] is stated over -- and this is its
   cycle-relative image, which is what the stage carries. *)
Definition seg_of (l : list (list mobs * bv 8)) : list (list mobs * bv 8) :=
  (fun x => (open_seg x.1, x.2)) <$> l.

Lemma seg_of_snd (l : list (list mobs * bv 8)) : snd <$> seg_of l = snd <$> l.
Proof.
  induction l as [| x l IH]; [done |].
  change (seg_of (x :: l)) with ((open_seg x.1, x.2) :: seg_of l).
  by rewrite !fmap_cons IH.
Qed.

Lemma seg_of_app (l1 l2 : list (list mobs * bv 8)) :
  seg_of (l1 ++ l2) = seg_of l1 ++ seg_of l2.
Proof. by rewrite /seg_of fmap_app. Qed.

Lemma seg_of_length (l : list (list mobs * bv 8)) : length (seg_of l) = length l.
Proof. by rewrite /seg_of length_fmap. Qed.

(* the INPUT claim's pure fact *)
Definition ein_pure (si : istage) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ dl `prefix_of` echoed pops
  /\ seg_of (echoed pops)
     = (if i_owed si then removelast (i_E si) else i_E si).

(* ...and the LEDGER's tie between them: one [E], and the owed window is the
   only place the two may disagree. *)
Definition stage_tie (so : ostage) (si : istage) : Prop :=
  i_E si = o_E so.

Lemma epu_lookup_nil_absurd {A} (j : nat) (x : A) :
  ([] : list A) !! j = Some x -> False.
Proof. intros Hx. apply lookup_lt_Some in Hx. cbn in Hx. lia. Qed.

Lemma eout_pure_0 : eout_pure ostage0 [].
Proof.
  rewrite /eout_pure /ostage0. cbn [o_cs o_E o_w]. split_and!.
  - rewrite D_nil. done.
  - rewrite pending_nil. apply prefix_nil.
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - constructor.
  - constructor.
Qed.

Lemma ein_pure_0 : ein_pure istage0 [] [].
Proof.
  rewrite /ein_pure /istage0. cbn [i_E i_owed]. split_and!.
  - split.
    + intros e He. by apply elem_of_nil in He.
    + intros i e1 e2 H1 H2. destruct (epu_lookup_nil_absurd i e1 H1).
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - rewrite /seg_of /echoed. by rewrite filter_nil.
Qed.

Lemma stage_tie_0 : stage_tie ostage0 istage0.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE GHOST NAMES AT THE FIXED PART                                  *)
(* ====================================================================== *)

(* [AppEcho.echo_fixed] becomes this record.  [eg_taint] is the landed
   counter and nothing about it moves; the other two are ECHO-OUT's.  All
   three are allocated by [AppEcho.echo_birth]. *)
Record echo_gn := MkEchoGn {
  eg_taint : gname;   (* mono_nat: 0 while disciplined, 1 after -- LANDED *)
  eg_era   : gname;   (* mono_nat: the era counter, [obs_boots h] *)
  eg_pin   : gname;   (* ghost_map gname era_pins: ge ↦ the era's ghosts *)
}.

(* what the pin map records for a console-port era name [ge]: the era's
   NUMBER (so that a dead era's claim can be recognised against the era
   counter) and the three ghosts the era's resources live at. *)
Definition era_pins : Type := (nat * gname * gname * gname)%type.
Definition ep_k   (v : era_pins) : nat   := v.1.1.1.
Definition ep_gso (v : era_pins) : gname := v.1.1.2.
Definition ep_gsi (v : era_pins) : gname := v.1.2.
Definition ep_go  (v : era_pins) : gname := v.2.

Class echoOutG (Σ : gFunctors) := EchoOutG {
  eo_mono_nat : mono_natG Σ;
  eo_ostage   : ghost_varG Σ ostage;
  eo_istage   : ghost_varG Σ istage;
  eo_turn     : ghost_varG Σ nat;
  eo_etok     : ghost_varG Σ unit;
  eo_pin      : ghost_mapG Σ gname era_pins;
}.
#[global] Existing Instances eo_mono_nat eo_ostage eo_istage eo_turn
  eo_etok eo_pin.

Section echo_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  (* THE TAINT, ABSTRACTLY.  [AppEcho.echo_taint] is [mono_nat_lb_own
     (eg_taint γ) 1]; this file takes it as a parameter so that it sits
     BELOW [AppEcho] and the two claims can be read without the era-0 pin
     cone. *)
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.

  (* ---- the era's ghosts ---- *)

  (* PERSISTENT, AND KEYED BY [ge]: the era's stage and turn ghosts are a
     FUNCTION of the console port's per-era name, so a claim at [ge] and the
     ledger agree on which ghosts they are talking about with no injectivity
     obligation anywhere. *)
  Definition era_pin (ge : gname) (v : era_pins) : iProp Σ :=
    ghost_map_elem (eg_pin γ) ge DfracDiscarded v.

  Global Instance era_pin_persistent ge v : Persistent (era_pin ge v).
  Proof. rewrite /era_pin. apply _. Qed.
  Global Instance era_pin_timeless ge v : Timeless (era_pin ge v).
  Proof. rewrite /era_pin. apply _. Qed.

  Lemma era_pin_agree ge v v' : era_pin ge v -∗ era_pin ge v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /era_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. exact Heq.
  Qed.

  (* the two stages, split: one half in the port claim, one in the ledger *)
  Definition out_frag (gso : gname) (so : ostage) : iProp Σ :=
    ghost_var gso (1/2) so.
  Definition out_auth (gso : gname) (so : ostage) : iProp Σ :=
    ghost_var gso (1/2) so.
  Definition in_frag (gsi : gname) (si : istage) : iProp Σ :=
    ghost_var gsi (1/2) si.
  Definition in_auth (gsi : gname) (si : istage) : iProp Σ :=
    ghost_var gsi (1/2) si.

  Global Instance out_frag_timeless gso so : Timeless (out_frag gso so).
  Proof. rewrite /out_frag. apply _. Qed.
  Global Instance out_auth_timeless gso so : Timeless (out_auth gso so).
  Proof. rewrite /out_auth. apply _. Qed.
  Global Instance in_frag_timeless gsi si : Timeless (in_frag gsi si).
  Proof. rewrite /in_frag. apply _. Qed.
  Global Instance in_auth_timeless gsi si : Timeless (in_auth gsi si).
  Proof. rewrite /in_auth. apply _. Qed.

  (* the writer's cursor: one half travels in the programs' payloads (fork
     [Rc], exit/wait [Q]), the other sits in the ledger *)
  Definition turn (go : gname) (p : nat) : iProp Σ := ghost_var go (1/2) p.
  Definition turn_auth (go : gname) (p : nat) : iProp Σ := ghost_var go (1/2) p.

  Global Instance turn_timeless go p : Timeless (turn go p).
  Proof. rewrite /turn. apply _. Qed.
  Global Instance turn_auth_timeless go p : Timeless (turn_auth go p).
  Proof. rewrite /turn_auth. apply _. Qed.

  (* THE ERA TOKEN.  What makes the era's ADOPTION possible: the ledger has
     to know that [ge] is not already pinned, and nothing in the ledger can
     say so, because the kernel is what mints [ge].  The token is the
     kernel's own statement that it did mint it fresh -- see the header's
     "what waits for the kernel" -- and the ledger keeps HALF of it for
     every era it has ever adopted, so a second adoption at the same [ge]
     is refuted outright. *)
  Definition era_tok (ge : gname) : iProp Σ := ghost_var ge 1 ().
  Definition era_half (ge : gname) : iProp Σ := ghost_var ge (1/2) ().

  Global Instance era_half_timeless ge : Timeless (era_half ge).
  Proof. rewrite /era_half. apply _. Qed.

  Lemma era_tok_split ge : era_tok ge -∗ era_half ge ∗ era_half ge.
  Proof.
    rewrite /era_tok /era_half. iIntros "H".
    iEval (rewrite -Qp.half_half) in "H".
    iDestruct (ghost_var_split with "H") as "[$ $]".
  Qed.

  Lemma era_tok_half_False ge : era_tok ge -∗ era_half ge -∗ False.
  Proof.
    rewrite /era_tok /era_half. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hv _].
    exfalso. by apply (Qp.not_add_le_l 1 (1/2)%Qp).
  Qed.

  (* ...and the era counter, whose lower bound says "era k is over" *)
  Definition era_closed (k : nat) : iProp Σ := mono_nat_lb_own (eg_era γ) (S k).
  Definition era_auth (k : nat) : iProp Σ := mono_nat_auth_own (eg_era γ) 1 k.

  Global Instance era_closed_persistent k : Persistent (era_closed k).
  Proof. rewrite /era_closed. apply _. Qed.
  Global Instance era_closed_timeless k : Timeless (era_closed k).
  Proof. rewrite /era_closed. apply _. Qed.
  Global Instance era_auth_timeless k : Timeless (era_auth k).
  Proof. rewrite /era_auth. apply _. Qed.

  Lemma era_closed_now k : era_auth k -∗ era_closed k -∗ False.
  Proof.
    rewrite /era_auth /era_closed. iIntros "Ha Hlb".
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle]. lia.
  Qed.

  Lemma era_closed_of_lt k k' : (k < k')%nat -> era_auth k' -∗ era_closed k.
  Proof.
    intros Hlt. rewrite /era_auth /era_closed. iIntros "Ha".
    iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb".
    iApply (mono_nat_lb_own_le (S k) with "Hlb"). lia.
  Qed.

  Lemma era_auth_grow k k' : (k <= k')%nat -> era_auth k ==∗ era_auth k'.
  Proof.
    intros Hle. rewrite /era_auth. iIntros "Ha".
    by iMod (mono_nat_own_update k' with "Ha") as "[$ _]".
  Qed.

  (* ====================================================================== *)
  (*  3.  THE TWO PORT CLAIMS, AT THE ERA INDEX                             *)
  (* ====================================================================== *)

  Definition eout (ge : gname) (ho : list mobs) (acc : list (bv 8)) : iProp Σ :=
    ( T
    ∨ ⌜acc = []⌝
    ∨ ∃ (v : era_pins) (so : ostage),
        era_pin ge v ∗ out_frag (ep_gso v) so ∗
        (era_closed (ep_k v) ∨ ⌜eout_pure so acc⌝))%I.

  Definition ein (ge : gname) (ho : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) : iProp Σ :=
    ( T
    ∨ ⌜pops = [] /\ dl = []⌝
    ∨ ∃ (v : era_pins) (si : istage),
        era_pin ge v ∗ in_frag (ep_gsi v) si ∗
        (era_closed (ep_k v) ∨ ⌜ein_pure si pops dl⌝))%I.

  Global Instance eout_timeless ge ho acc : Timeless (eout ge ho acc).
  Proof. rewrite /eout. apply bi.or_timeless; [apply _|]. apply _. Qed.
  Global Instance ein_timeless ge ho pops dl : Timeless (ein ge ho pops dl).
  Proof. rewrite /ein. apply bi.or_timeless; [apply _|]. apply _. Qed.

  (* ---- THE FOUNDING ([App.Happ_boot], through
         [SystemAdequacy.app_xfer_boot_raw_out]) ----
     The FRESH arm, from nothing and at EVERY [ge]: the transport keeps the
     shape it has and [AppEcho.echo_Happ_boot] does not move. *)
  Lemma eout_founded ge : ⊢ eout ge [] [].
  Proof. rewrite /eout. iRight. iLeft. iPureIntro. reflexivity. Qed.

  Lemma ein_founded ge : ⊢ ein ge [] [] [].
  Proof. rewrite /ein. iRight. iLeft. iPureIntro. by split. Qed.

  (* ---- THE LICENCES ([App.Happ_out_sup] / [Happ_in_sup]) ----
     The taint absorbs any update, on both sides; the landed route to the
     taint from the supply is [AppEcho.echo_taint_of_sup]. *)
  Lemma eout_of_taint ge ho acc : T -∗ eout ge ho acc.
  Proof. iIntros "HT". rewrite /eout. iLeft. iExact "HT". Qed.

  Lemma ein_of_taint ge ho pops dl : T -∗ ein ge ho pops dl.
  Proof. iIntros "HT". rewrite /ein. iLeft. iExact "HT". Qed.

  Lemma eout_sup ge ho acc b : T -∗ eout ge ho acc ==∗ eout ge ho (acc ++ [b]).
  Proof.
    iIntros "#HT _". iModIntro.
    iApply (eout_of_taint ge ho (acc ++ [b])). iExact "HT".
  Qed.

  Lemma ein_sup_log ge ho pops dl e :
    T -∗ ein ge ho pops dl ==∗ ein ge ho (pops ++ [e]) dl.
  Proof.
    iIntros "#HT _". iModIntro.
    iApply (ein_of_taint ge ho (pops ++ [e]) dl). iExact "HT".
  Qed.

  Lemma ein_sup_deliv ge ho pops dl ws :
    T -∗ ein ge ho pops dl ==∗ ein ge ho pops (dl ++ ws).
  Proof.
    iIntros "#HT _". iModIntro.
    iApply (ein_of_taint ge ho pops (dl ++ ws)). iExact "HT".
  Qed.

  (* ====================================================================== *)
  (*  4.  THE LEDGER'S ERA MACHINE                                          *)
  (* ====================================================================== *)

  (* WHAT A DEAD ERA LEAVES BEHIND.  Its claims are in an invariant nobody
     opens again, but a LINK is a [∀]-statement and may still be applied to
     one, so the ledger keeps that era's authorities: a stale link then
     re-establishes the claim's [era_closed] arm and, on the write path,
     still advances that era's cursor.  Nothing else reads them. *)
  Definition era_dead (v : era_pins) : iProp Σ :=
    (∃ (so : ostage) (si : istage) (p : nat),
       out_auth (ep_gso v) so ∗ in_auth (ep_gsi v) si ∗ turn_auth (ep_go v) p)%I.

  (* THE CURRENT ERA, or [None] before this era's first link.  The pair is
     ALLOCATED LAZILY at the first link (the era token pays for it), which
     is what keeps the transport free of ghosts.  [i_esc] is the input
     claim's half held in escrow until ITS first link -- the output claim
     always pairs first, because under the discipline the prologue is on the
     wire before any input is accepted. *)
  Definition era_live (ge : gname) (v : era_pins)
      (so : ostage) (si : istage) (esc : bool) (p : nat)
      (h : list mobs) : iProp Σ :=
    (era_pin ge v ∗ out_auth (ep_gso v) so ∗ in_auth (ep_gsi v) si
     ∗ (if esc then in_frag (ep_gsi v) si else True)
     ∗ turn_auth (ep_go v) p
     ∗ ⌜p = length (o_w so)⌝
     ∗ ⌜stage_tie so si⌝
     ∗ ⌜Forall (fun x => x.1 `prefix_of` open_seg h) (o_E so)⌝
     ∗ ⌜(length (o_E so) <= length (ins (open_seg h)))%nat⌝)%I.

  Definition cur_name (cur : option (gname * era_pins)) : option gname :=
    fst <$> cur.

  (* THE ERA COUNTER IS THE LEDGER'S OWN, not [obs_boots h]: [obs_boots]
     counts [ObsPowerOn] only, so it does not move at a PowerOff, while the
     era whose claims are in the dying invariant is over at THAT event.  It
     is existentially quantified because [era_auth] is exclusive, so the
     ledger's own copy determines it. *)
  Definition era_inv (h : list mobs) : iProp Σ :=
    (∃ (Mp : gmap gname era_pins) (cur : option (gname * era_pins)) (kcur : nat),
       ghost_map_auth (eg_pin γ) 1 Mp
       ∗ era_auth kcur
       ∗ ([∗ map] ge ↦ _ ∈ Mp, era_half ge)
       ∗ ([∗ map] ge ↦ v ∈ (match cur_name cur with
                            | None => Mp
                            | Some g => delete g Mp
                            end), era_dead v)
       ∗ ⌜forall ge v, Mp !! ge = Some v ->
            (Some ge = cur_name cur /\ ep_k v = kcur) \/ (ep_k v < kcur)%nat⌝
       ∗ match cur with
         | None => ⌜cur_name cur = None⌝
         | Some (ge, v) =>
             ⌜Mp !! ge = Some v⌝ ∗
             ∃ so si esc p, era_live ge v so si esc p h
         end)%I.

  (* ...and THE WHOLE LEDGER, which is what [AppEcho.echo_R] becomes: the
     landed taint counter, the era machine, and PHI's running record --
     every cycle's output was good, or the discipline is already broken
     (the taint's own arm). *)
  Definition echo_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1 (if decide (disc h) then 0%nat else 1%nat)
     ∗ era_inv h
     ∗ (⌜Forall good_out (cycles_of h)⌝ ∨ T))%I.

  Global Instance era_dead_timeless v : Timeless (era_dead v).
  Proof. rewrite /era_dead. apply _. Qed.

  Global Instance era_live_timeless ge v so si esc p h :
    Timeless (era_live ge v so si esc p h).
  Proof. rewrite /era_live. destruct esc; apply _. Qed.

  Global Instance era_inv_timeless h : Timeless (era_inv h).
  Proof.
    rewrite /era_inv. apply bi.exist_timeless. intros Mp.
    apply bi.exist_timeless. intros cur.
    apply bi.exist_timeless. intros kcur.
    destruct cur as [[ge v] |]; apply _.
  Qed.

  Global Instance echo_led_timeless h : Timeless (echo_led h).
  Proof. rewrite /echo_led. apply _. Qed.

  (* WHAT THE BIRTH STEP YIELDS, i.e. what [AppEcho.echo_cl] becomes: the
     landed taint counter at 0, the era machine UNPAIRED at era
     [obs_boots [] = 0], and PHI's record at the empty history.
     [AppEcho.echo_birth] is then three [own_alloc]s and this. *)
  Lemma echo_led_init :
    mono_nat_auth_own (eg_taint γ) 1 0%nat -∗
    mono_nat_auth_own (eg_era γ) 1 0%nat -∗
    ghost_map_auth (eg_pin γ) 1 (∅ : gmap gname era_pins) -∗
    echo_led [].
  Proof.
    iIntros "Ht He Hm". rewrite /echo_led /era_inv /era_auth.
    rewrite decide_True; [| exact disc_nil].
    iFrame "Ht".
    iSplitL "He Hm".
    - iExists ∅, None, 0%nat. cbn [cur_name fmap option_fmap].
      iFrame "Hm He". rewrite !big_sepM_empty.
      iSplit; [done|]. iSplit; [done|]. iSplit; [| done].
      iPureIntro. intros ge v Hv. by rewrite lookup_empty in Hv.
    - iLeft. iPureIntro. rewrite /cycles_of /cycles_rev /=. constructor.
  Qed.

  (* ====================================================================== *)
  (*  5.  THE LEDGER'S STEPS                                                *)
  (* ====================================================================== *)

  (* THE POWER EVENT.  The counter's landed argument ([disc_power]), the era
     machine's own step -- the live era becomes DEAD and the machine goes
     unpaired, which is what makes the next era's adoption possible -- and
     PHI's record, which a power event does not touch ([cycles_of_on] adds
     an EMPTY cycle, and [good_out []] holds). *)
  Lemma era_inv_pow (h : list mobs) (e : mobs) :
    era_inv h ==∗ era_inv (h ++ [e]).
  Proof.
    iIntros "H". rewrite /era_inv.
    iDestruct "H" as (Mp cur kcur) "(Hm & Hk & Hhalf & Hdead & %Hdom & Hcur)".
    iMod (era_auth_grow kcur (S kcur) ltac:(lia) with "Hk") as "Hk".
    destruct cur as [[ge v] |].
    - iDestruct "Hcur" as "(%Hge & Hlive)".
      iDestruct "Hlive" as (so si esc p) "Hlive".
      rewrite /era_live.
      iDestruct "Hlive" as
        "(#Hpin & Ho & Hi & Hesc & Ht & %Hp & %Htie & %Hpre & %Hlen)".
      iModIntro. iExists Mp, None, (S kcur).
      cbn [cur_name fmap option_fmap]. iFrame "Hm Hk Hhalf".
      iSplitL "Hdead Ho Hi Ht".
      + iApply (big_sepM_delete _ Mp ge v Hge).
        iSplitR "Hdead"; [| iExact "Hdead"].
        rewrite /era_dead. iExists so, si, p. iFrame "Ho Hi Ht".
      + iSplit; [| done]. iPureIntro. intros ge' v' Hv'. right.
        destruct (Hdom ge' v' Hv') as [[Heq Hkv] | Hlt]; lia.
    - iDestruct "Hcur" as "%Hnone". iModIntro. iExists Mp, None, (S kcur).
      cbn [cur_name fmap option_fmap]. iFrame "Hm Hk Hhalf Hdead".
      iSplit; [| done]. iPureIntro. intros ge' v' Hv'. right.
      destruct (Hdom ge' v' Hv') as [[Heq Hkv] | Hlt]; [| lia].
      cbn [cur_name fmap option_fmap] in Heq. discriminate Heq.
  Qed.

  Lemma echo_led_pow (h : list mobs) (on : bool) :
    echo_led h ==∗ echo_led (h ++ [if on then ObsPowerOff else ObsPowerOn]).
  Proof.
    iIntros "(Ht & He & Hphi)". rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_power h on)).
    iFrame "Ht".
    iMod (era_inv_pow h (if on then ObsPowerOff else ObsPowerOn) with "He")
      as "$".
    iModIntro. destruct on.
    - (* PowerOff: the cycle list does not move *)
      rewrite cycles_of_off. iExact "Hphi".
    - (* PowerOn: a new, EMPTY cycle, whose output is trivially good *)
      rewrite cycles_of_on.
      iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro. apply Forall_app. split; [exact Hg |].
      apply Forall_singleton. exists []. split; [constructor |].
      rewrite /sess /= sess_n_0. cbn [obs_wire]. apply prefix_nil.
  Qed.

  (* AN INPUT BYTE.  The counter's landed argument ([disc_in] / [disc_other])
     and the tag it mints; the era machine and PHI's record do not move
     ([good_out] is MONOTONE in the input count, because [sess_n cs n] only
     grows -- so an input can never falsify a cycle that was good). *)
  (* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
     that was good: the wire is unchanged and [sess_n] only grows with the
     input count.  That is every rx event (on either port) and every output
     on the OTHER port -- i.e. everything [App.Htx]/[Hrx] must account for
     except the console's own drain, which needs the claim. *)
  Lemma good_out_step (seg : list mobs) (e : mobs) :
    obs_wire Uart0 [e] = [] ->
    good_out seg -> good_out (seg ++ [e]).
  Proof.
    intros He (cs & Hcs & Hpre). exists cs. split; [exact Hcs |].
    rewrite obs_wire_app He app_nil_r.
    rewrite /sess ins_app length_app.
    etrans; [exact Hpre |]. apply sess_n_mono. lia.
  Qed.

  Lemma obs_wire_in (i : uart_id) (b : bv 8) : obs_wire Uart0 [ObsUartIn i b] = [].
  Proof. by destruct i. Qed.

  Lemma obs_wire_out_other (i : uart_id) (b : bv 8) :
    i <> Uart0 -> obs_wire Uart0 [ObsUartOut i b] = [].
  Proof. intros Hi. destruct i; [by destruct Hi | done]. Qed.

  Lemma io_singleton (e : mobs) :
    is_io e = true -> Forall (fun x => is_io x = true) [e].
  Proof. intros He. constructor; [exact He | constructor]. Qed.

  (* PHI's RECORD ACROSS AN EVENT THAT DOES NOT WRITE THE CONSOLE: the closed
     cycles are untouched and the open one extends by that event. *)
  Lemma phi_step_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
    Forall good_out (cycles_of h) -> Forall good_out (cycles_of (h ++ [e])).
  Proof.
    intros Hsh Hio Hw HF.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs Hlast].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton in Hlast. rewrite Forall_singleton.
    apply good_out_step; [exact Hw | exact Hlast].
  Qed.

  (* ...AND THE CLOSED CYCLES ALONE, which is what the console's own drain
     gets: the open cycle's [good_out] comes from the CLAIM
     ([echo_led_drain]) and is handed in. *)
  Lemma phi_step_cons (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true ->
    good_out (open_seg h ++ [e]) ->
    Forall good_out (cycles_of h) -> Forall good_out (cycles_of (h ++ [e])).
  Proof.
    intros Hsh Hio Hgo HF.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs _].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton. exact Hgo.
  Qed.

  (* THE ERA MACHINE ACROSS AN I/O EVENT: only [era_live]'s two same-cycle
     facts mention the history, and both are monotone in the open segment. *)
  Lemma era_inv_io (h : list mobs) (e : mobs) :
    is_io e = true -> era_inv h -∗ era_inv (h ++ [e]).
  Proof.
    intros Hio. rewrite /era_inv. iIntros "H".
    iDestruct "H" as (Mp cur kcur) "(Hm & Hk & Hhalf & Hdead & %Hdom & Hcur)".
    iExists Mp, cur, kcur. iFrame "Hm Hk Hhalf Hdead".
    iSplit; [by iPureIntro |].
    destruct cur as [[ge v] |]; [| iExact "Hcur"].
    iDestruct "Hcur" as "(%Hge & Hlive)". iSplit; [by iPureIntro |].
    iDestruct "Hlive" as (so si esc p) "Hlive". iExists so, si, esc, p.
    rewrite /era_live.
    iDestruct "Hlive" as
      "(#Hpin & Ho & Hi & Hesc & Ht & %Hp & %Htie & %Hpre & %Hlen)".
    iFrame "Hpin Ho Hi Hesc Ht".
    rewrite (open_seg_io h [e] (io_singleton e Hio)).
    iPureIntro. split_and!; [exact Hp | exact Htie | |].
    - rewrite Forall_forall in Hpre. rewrite Forall_forall.
      intros x Hx. destruct (Hpre x Hx) as [z Hz].
      exists (z ++ [e]). rewrite Hz. by rewrite app_assoc.
    - rewrite ins_app length_app. lia.
  Qed.

  (* ====================================================================== *)
  (*  6.  THE STEPS THE LINKS SPEND -- STATED (proofs: the worklist)         *)
  (* ====================================================================== *)

  (* THE CONSOLE'S OUTPUT needs the claim, which is [echo_led_drain]'s job:
     the ledger step takes the [good_out] it produced at the NEW segment. *)
  Lemma echo_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (T ∨ ⌜good_out (open_seg h ++ [ObsUartOut i b])⌝) -∗
    echo_led h ==∗ echo_led (h ++ [ObsUartOut i b]).
  Proof.
    intros Hsh. iIntros "Hgo (Hcnt & He & Hphi)".
    iDestruct (era_inv_io h (ObsUartOut i b) eq_refl with "He") as "He".
    rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_out h i b Hsh)).
    iModIntro. iFrame "Hcnt He".
    iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
    iDestruct "Hgo" as "[HT | %Hgo]"; [by iRight |].
    iLeft. iPureIntro. by apply phi_step_cons.
  Qed.

  Lemma echo_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    echo_led h ==∗
      echo_led (h ++ [ObsUartIn i b])
      ∗ (⌜disc (h ++ [ObsUartIn i b])⌝ ∨ mono_nat_lb_own (eg_taint γ) 1).
  Proof.
    intros Hsh. iIntros "(Hcnt & He & Hphi)".
    iDestruct (era_inv_io h (ObsUartIn i b) eq_refl with "He") as "He".
    iAssert (⌜Forall good_out (cycles_of (h ++ [ObsUartIn i b]))⌝ ∨ T)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro.
      apply (phi_step_io h (ObsUartIn i b) Hsh eq_refl (obs_wire_in i b) Hg). }
    rewrite /echo_led.
    destruct (decide (disc (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (disc_in h b Hsh Hd')
          | exact (proj1 (disc_other h (ObsUartIn Uart1 b) eq_refl I Hsh) Hd') ]. }
      iModIntro. iFrame "Hcnt He Hphi". iLeft. iPureIntro. exact Hd'.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc h)); lia |].
      iModIntro. iFrame "Hcnt He Hphi". iRight. iExact "Hlb".
  Qed.

  (* PHI's read at the end of the run, in the OWNER's form (2026-09-13): the
     guard is the WHOLE history's discipline.  Once the taint is set [disc]
     is false forever ([EchoDisc.disc_prefix]), so the ledger's disjunction
     is exactly this implication. *)
  Lemma echo_led_phi (h : list mobs) :
    (T -∗ mono_nat_lb_own (eg_taint γ) 1) -∗
    echo_led h -∗ ⌜disc h -> Forall good_out (cycles_of h)⌝.
  Proof.
    iIntros "HTT (Hcnt & _ & [%Hg | HT'])".
    { iPureIntro. by intros _. }
    iDestruct ("HTT" with "HT'") as "Hlb".
    iDestruct (mono_nat_lb_own_valid with "Hcnt Hlb") as %[_ Hle].
    iPureIntro. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.

  (* (E) THE ECHO SHIFT's core step, at the STORE arm: the byte goes out and
     [i_owed] is raised; [ein_step_append] lowers it.  The premises are what
     [WpUart.echo_link] hands over -- the order fact and the wire below
     [acc] at the byte's own history -- and D2
     ([EchoOutPure.D2_next_input]) is applied at
     [W := obs_wire Uart0 (open_seg h)], whose LOWER bound is the
     discipline's ([EchoOutPure.disc_seg_open_seg]) and whose UPPER bound is
     that premise. *)
  Lemma eout_step_echo (ge : gname) (h : list mobs) (c : bv 8)
      (ho hi : list mobs) (acc : list (bv 8))
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` acc ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    echo_led h -∗ eout ge ho acc -∗ ein ge hi pops dl ==∗
      echo_led h ∗ eout ge h (acc ++ [echo_of c]) ∗ ein ge hi pops dl.
  Proof.
  Admitted.

  (* ...and the LOG's side, fired after the chain ([WpUart.in_append]): the
     entry is filed and [i_owed] goes back down.  [cs] is what the arm
     actually emitted -- [[]] for a drop (the stoppable run's LEFT conjunct,
     which the claim tolerates: a dropped byte does not enter [echoed]) or
     [[echo_of c]] for the store. *)
  Lemma ein_step_append (ge : gname) (h : list mobs) (c : bv 8)
      (cs : list (bv 8)) (hi : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_ends_in Uart0 h c ->
    cons_echo c cs ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    echo_led h -∗ ein ge hi pops dl ==∗
      echo_led h ∗ ein ge h (pops ++ [(h, c, cs)]) dl.
  Proof.
  Admitted.

  (* (W) THE WRITE.  The writer carries the era's pin, its cursor, and
     PERSISTENT lower bounds on the stage's two growing components; D1 ("no
     echo while a continuation is part-written") is what turns the bounds
     into equalities at the write, and it is a ledger invariant. *)
  Lemma eout_step_write (ge : gname) (v : era_pins) (p : nat) (b : bv 8)
      (cs : list nat) (E : list (list mobs * bv 8))
      (ho : list mobs) (acc : list (bv 8)) (h : list mobs) :
    pending cs E !! p = Some b ->
    era_pin ge v -∗ turn (ep_go v) p -∗
    echo_led h -∗ eout ge ho acc ==∗
      echo_led h ∗ eout ge ho (acc ++ [b]) ∗ turn (ep_go v) (S p).
  Proof.
  Admitted.

  (* (R) THE READ.  [ws] is the window the read CONSUMED; [read_ok] is what
     [WpUart.read_link] hands over.  The conclusion is what SH-LINE needs. *)
  Lemma ein_step_read (ge : gname) (hi : list mobs) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (h : list mobs) :
    read_ok pops dl ws ->
    echo_led h -∗ ein ge hi pops dl ==∗
      echo_led h ∗ ein ge hi pops (dl ++ ws)
      ∗ (T ∨ ⌜(dl ++ ws) `prefix_of` echoed pops⌝).
  Proof.
  Admitted.

  (* ...and the LINE, which is what SH-LINE reads off it.  Everything here is
     [EchoOutPure]'s: the consumed window is a slice of the echoed entries
     and a 17-byte slice at a multiple of 17 IS [echo_line]. *)
  Lemma ein_read_line (si : istage) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (q : nat) :
    ein_pure si pops dl ->
    i_owed si = false ->
    E_byte (i_E si) ->
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = (length echo_line * q)%nat ->
    length ws = length echo_line ->
    snd <$> ws = echo_line.
  Proof.
    intros (_ & _ & _ & Hseg) Hno HE Hp Hdl Hws.
    rewrite Hno in Hseg.
    (* [seg_of] changes no byte, so the window's bytes are the stage's *)
    rewrite -(seg_of_snd ws).
    apply (read_window_line (i_E si) (seg_of dl) (seg_of ws) q).
    - exact HE.
    - rewrite -seg_of_app -Hseg. destruct Hp as [z Hz]. rewrite Hz.
      exists (seg_of z). by rewrite seg_of_app.
    - by rewrite seg_of_length.
    - by rewrite seg_of_length.
  Qed.

  (* (L) THE LEDGER STEP AT THE DRAIN ([App.Htx]).  The claim is in hand, the
     ledger too, and [EchoOutPure.good_out_of_stage] turns the stage into
     [good_out] of the open cycle -- the SAME-CYCLE side condition comes from
     [era_live]'s two pure conjuncts, NOT from [ho ⊑ h], so [Htx] needs no
     new premise. *)
  Lemma echo_led_drain (ge : gname) (h : list mobs) (ho : list mobs)
      (acc : list (bv 8)) (seg : list mobs) :
    trace_shape h true ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` acc ->
    echo_led h -∗ eout ge ho acc -∗
      echo_led h ∗ eout ge ho acc ∗ (T ∨ ⌜good_out seg⌝).
  Proof.
  Admitted.

End echo_out.
