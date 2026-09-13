(* ===================================================================== *)
(* ChildTok.v -- THE GENERATION, AS A SAVED PREDICATE CARRYING ITS SLOT,  *)
(* ITS PID AND ITS EXIT PAYLOAD.                                          *)
(*                                                                        *)
(* Design of record: claude-notes/projects/app-echo.md, the WAIT-EXIT     *)
(* section (the ESCROW shape).  A process's GENERATION is the             *)
(* ghost name allocproc mints for it -- the identity of THIS incarnation  *)
(* of a proc slot, which is what a wait()-side resource transfer has to   *)
(* be indexed by, a pid being reused and a generation not                 *)
(* ([UexecSlot.uvis_gen] is the key's reading of it).  The name carries   *)
(* three things at once, and they are one saved element rather than three *)
(* ghosts because every party that holds a piece of a generation has to   *)
(* agree with every other on all three:                                   *)
(*                                                                        *)
(*   the SLOT      the [proc_addr] of the slot this incarnation occupies  *)
(*                 -- [SchedCtx]'s and [ProcInv.proc_priv]'s own          *)
(*                 parameter, so the party that reads it has it in hand.  *)
(*   the PID       the pid <allocpid> chose, at the [mword 32] the cell   *)
(*                 holds.  A generation has one pid forever is then       *)
(*                 agreement and not an invariant.                        *)
(*   the PAYLOAD   [Q : Z -> iProp], the resources this process's exit    *)
(*                 owes its parent, as a function of the exit STATUS.     *)
(*                 fork chooses it ([SpecKfork]'s [gen_set]); exit pays   *)
(*                 [Q xs] into the escrow; wait hands the parent [Q xs].  *)
(*                                                                        *)
(* WHY A SAVED PREDICATE.  The payload is an [iProp], so it cannot be a   *)
(* value in an ordinary camera without a step-index; [saved_anything_own] *)
(* at [genF] is the standard way to put one in a ghost -- and the ▷ that  *)
(* buys it is exactly the ▷ in the payment rule below, which the escrow   *)
(* pays for free (kexit's deposit and kwait's return are separated by at  *)
(* least one step) and a TIMELESS payload does not pay at all             *)
(* ([gen_pay_timeless]).                                                  *)
(*                                                                        *)
(* THE FOUR PIECES OF ONE GENERATION, and who holds them:                 *)
(*                                                                        *)
(*   [child_tok γ pid Q]  the PARENT's quarter, minted at fork.  Its      *)
(*                        holder is the one party wait() may hand the     *)
(*                        payload to.                                     *)
(*   [gen_kq γ pa pid Q]  the KERNEL's quarter, kept in the child's       *)
(*                        private block ([ProcInv.proc_priv_core]) until  *)
(*                        exit moves it into the ZOMBIE escrow.           *)
(*   [my_pay γ Q]         the CHILD's knowledge of its own payload:       *)
(*                        persistent, because it is what the child's slot *)
(*                        is built against and a slot is re-established   *)
(*                        at every trap.  It is the discarded HALF, so it *)
(*                        is also where the two persistent readings       *)
(*                        [gen_slot] / [gen_pid] come from.               *)
(*   [exit_tok γ pid xs]  the ESCROW: the kernel's quarter TOGETHER WITH  *)
(*                        the paid payload.  kexit produces it, kwait     *)
(*                        returns it, and [gen_pay] is what a parent      *)
(*                        holding the matching [child_tok] does with it.  *)
(*                                                                        *)
(* PERSISTENCE IS ONLY THROUGH THE DISCARDED FRACTION.  A quarter is a    *)
(* [DfracOwn], hence linear: neither the parent's token nor the kernel's  *)
(* may be duplicated, which is what makes -- the payload is paid once -- a *)
(* THEOREM.  The two readings are stated at [DfracDiscarded] for that     *)
(* reason -- they are facts, so they must come off the half fork discards *)
(* and never off a quarter.                                               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.algebra Require Import dfrac excl.  (* [exclR] -- the alive token's camera *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own saved_prop.
Require Import SailStdpp.Base SailStdpp.Values.
Local Open Scope Z_scope.

(* THE FUNCTOR.  A pair: the two VALUES the generation pins (its slot
   address and its pid, at [leibnizO] because both are discrete machine
   words) and the PREDICATE it saves (the exit payload, indexed by the exit
   status).  [constOF] on the left is what keeps the values out of the
   step-indexing: agreement on them is a PURE equality with no later,
   which is what [gen_agree] hands its callers. *)
(* ...AND THE THREE THINGS A GENERATION RECORDS BESIDES ITS PAYLOAD (lane
   SELF-KILL, §3a).

   [ga]  THE ALIVE TOKEN'S GHOST NAME, in the PURE component beside the
         slot and the pid, so agreement on it is a plain equality with no
         later.  It cannot be the generation's own name: [gn] is
         [saved_anything_alloc]'s, and no [own_alloc] variant targets a
         chosen name, so an exclusive token AT [gn] is not allocatable.
         The token itself is [alive_tok] below -- linear, exclusive, minted
         with the incarnation and carried by the process ([UkRun.urun]),
         and what a LIVE process spends to refute "this process was
         killed".
   [K]   THE INCARNATION'S OWN CREDENTIAL PART.  A kill costs the killer
         [K] of the target; echo's programs choose [echo_taint ∨
         alive_tok ga], the generic process chooses [emp].  A saved
         PROPOSITION, so agreement costs a later -- which every consumer of
         the payload already pays.
   [Kp]  ...AND HOW A KILLER WHO HOLDS ONLY THE APPLICATION'S SUPPLY PAYS
         IT: the persistent implication [□ (app_sup -∗ K)].  It is stored
         OPAQUELY, as a second saved proposition, because [AppInv.app_sup]
         is not reachable at this altitude -- this file requires stdpp,
         iris and Sail and nothing of the application -- so the equation is
         made where [app_sup] is nameable, at the dispatcher's fork row,
         and what travels here is the proposition. *)
Definition genF : oFunctor :=
  prodOF (constOF (leibnizO (Values.mword 64 * Values.mword 32 * gname)))
         (prodOF (Z -d> ▶ ∙) (prodOF (▶ ∙) (▶ ∙))).

Global Instance genF_contractive : oFunctorContractive genF.
Proof. apply _. Qed.

(* THE ALIVE TOKEN'S VALUE, AND IT IS A TYPE OF OUR OWN.  [exclR unitO] is
   already an [inG] of the bundle ([Xv6Cameras.icache_tickG]), and two
   providers of one [inG] in one scope do not fail -- they make two
   instance paths whose propositions print identically
   (durable-notes.md).  A one-constructor inductive of this file's own
   makes the camera unmistakable. *)
Inductive alive_val := Alive.

Global Instance alive_val_eq_dec : EqDecision alive_val.
Proof. solve_decision. Defined.

Definition atokR : cmra := exclR (leibnizO alive_val).

(* THE CAPACITY CLASS, AND IT LIVES HERE rather than in [Xv6Cameras.v] with
   the bundle's other members.  The reason is import hygiene: the files
   that name this file's pieces are U-tier leaves that bind no
   whole-system bundle, so each has to name the class itself -- and naming
   [savedAnythingG Σ genF] raw would make every one of them import
   [saved_prop], whose own re-exports re-shadow [Forall_forall] and the
   numeral scopes at whatever point in the client's import list the
   [Require] happens to sit.  A CLASS OF OUR OWN costs the client one name
   and imports nothing.  [Xv6Cameras] re-exports it and [Xv6G.xv6_ctok] is
   the bundle's field, so the kernel side reaches it through the bundle
   and must not bind it again. *)
Class ctokG (Σ : gFunctors) := CtokG {
  ctok_inG :: savedAnythingG Σ genF;
  (* the alive token's camera rides the SAME class, for the reason the
     class exists at all: a U-tier leaf that names one names the other. *)
  ctok_alive :: inG Σ atokR;
}.
Definition ctokΣ : gFunctors := #[ savedAnythingΣ genF; GFunctor atokR ].
Global Instance subG_ctokΣ {Σ} : subG ctokΣ Σ -> ctokG Σ.
Proof. solve_inG. Qed.

Section ChildTok.
  Context `{!ctokG Σ}.

  Implicit Types (γ ga : gname) (dq : dfrac) (pa : Values.mword 64)
                 (pid : Values.mword 32) (Q : Z -> iProp Σ) (xs : Z)
                 (K Kp : iProp Σ).

  (* ------------------------------------------------------------------ *)
  (* THE ALIVE TOKEN.                                                     *)
  (* ------------------------------------------------------------------ *)

  (* WHAT A PROCESS SPENDS TO SAY IT IS STILL ITSELF.  Exclusive and
     per-INCARNATION (pids are reused, generations are not), minted with
     the generation and carried by the process.  Two readers cannot both
     hold it, which is the whole of its content: a process that holds its
     own token refutes any claim that its incarnation was killed, and a
     process that FAULTS ON PURPOSE hands it over as the credential its
     death costs. *)
  Definition alive_tok ga : iProp Σ := own ga (Excl (Alive : leibnizO alive_val)).

  Global Instance alive_tok_timeless ga : Timeless (alive_tok ga).
  Proof. apply _. Qed.

  Lemma alive_tok_excl ga : alive_tok ga -∗ alive_tok ga -∗ False.
  Proof.
    rewrite /alive_tok. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. exact (exclusive_l _ _ Hv).
  Qed.

  Lemma alive_tok_alloc : ⊢ |==> ∃ ga, alive_tok ga.
  Proof. rewrite /alive_tok. iApply own_alloc. done. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE GENERATION.                                                      *)
  (* ------------------------------------------------------------------ *)

  (* the saved element, spelled once: the three PURE values, the payload
     under [Next] (the functor's ▷) and the two saved propositions *)
  Definition gen_el pa pid ga Q K Kp : oFunctor_apply genF (iPropO Σ) :=
    (((pa, pid, ga) : leibnizO (Values.mword 64 * Values.mword 32 * gname)),
     (Next ∘ Q, (Next K, Next Kp))).

  (* A FRACTION OF A GENERATION.  Every piece below is this at a fraction. *)
  Definition gen_own γ dq pa pid ga Q K Kp : iProp Σ :=
    saved_anything_own (F := genF) γ dq (gen_el pa pid ga Q K Kp).

  (* ---- the readings, and they are facts only off the discarded half ---- *)

  (* EVERYTHING THE DISCARDED HALF SAYS, AT ONCE.  The four readings below
     are this at one component named and the rest hidden; it is a reading
     in its own right because the party that CUTS the generation
     ([gen_split]) knows all four and every later reader wants a different
     one. *)
  Definition gen_know γ ga Q K Kp : iProp Σ :=
    (∃ pa pid, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  (* the slot this incarnation occupies *)
  Definition gen_slot γ pa : iProp Σ :=
    (∃ pid ga Q K Kp, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  (* ...and the pid it was given.  A generation has one pid forever, which
     is what the escrow's pid-keyed reading in [SpecKwait]'s success arm
     stands on. *)
  Definition gen_pid γ pid : iProp Σ :=
    (∃ pa ga Q K Kp, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  (* THE CHILD'S KNOWLEDGE OF ITS OWN PAYLOAD.  Persistent, so it travels
     into the child's slot and survives exec ([UexecSlot.uvis_gen] does),
     and so that a slot -- re-established at every trap -- may name it
     without owning anything linear. *)
  Definition my_pay γ Q : iProp Σ :=
    (∃ pa pid ga K Kp, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  (* ...AND THE SAME READING FOR THE THREE NEW COMPONENTS.  [gen_alive] is
     PURE agreement (the name is in the [constOF] half), the other two cost
     a later, exactly as the payload does. *)
  Definition gen_alive γ ga : iProp Σ :=
    (∃ pa pid Q K Kp, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  Definition kcred γ K : iProp Σ :=
    (∃ pa pid ga Q Kp, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  Definition kpay γ Kp : iProp Σ :=
    (∃ pa pid ga Q K, gen_own γ DfracDiscarded pa pid ga Q K Kp)%I.

  Global Instance gen_know_persistent γ ga Q K Kp : Persistent (gen_know γ ga Q K Kp).
  Proof. apply _. Qed.
  Global Instance gen_slot_persistent γ pa : Persistent (gen_slot γ pa).
  Proof. apply _. Qed.
  Global Instance gen_pid_persistent γ pid : Persistent (gen_pid γ pid).
  Proof. apply _. Qed.
  Global Instance my_pay_persistent γ Q : Persistent (my_pay γ Q).
  Proof. apply _. Qed.
  Global Instance gen_alive_persistent γ ga : Persistent (gen_alive γ ga).
  Proof. apply _. Qed.
  Global Instance kcred_persistent γ K : Persistent (kcred γ K).
  Proof. apply _. Qed.
  Global Instance kpay_persistent γ Kp : Persistent (kpay γ Kp).
  Proof. apply _. Qed.

  (* the four projections of the whole reading *)
  Lemma gen_know_my_pay γ ga Q K Kp : gen_know γ ga Q K Kp -∗ my_pay γ Q.
  Proof.
    rewrite /gen_know /my_pay. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, ga, K, Kp. iExact "H".
  Qed.

  Lemma gen_know_alive γ ga Q K Kp : gen_know γ ga Q K Kp -∗ gen_alive γ ga.
  Proof.
    rewrite /gen_know /gen_alive. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, Q, K, Kp. iExact "H".
  Qed.

  Lemma gen_know_kcred γ ga Q K Kp : gen_know γ ga Q K Kp -∗ kcred γ K.
  Proof.
    rewrite /gen_know /kcred. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, ga, Q, Kp. iExact "H".
  Qed.

  Lemma gen_know_kpay γ ga Q K Kp : gen_know γ ga Q K Kp -∗ kpay γ Kp.
  Proof.
    rewrite /gen_know /kpay. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, ga, Q, K. iExact "H".
  Qed.

  (* ---- the two linear quarters ---- *)

  (* THE PARENT'S QUARTER, handed to the forking process at [kfork]'s pid
     arm.  The slot is existential: a parent is told which CHILD it has,
     not which proc slot the kernel put it in. *)
  Definition child_tok γ pid Q : iProp Σ :=
    (∃ pa ga K Kp, gen_own γ (DfracOwn (1/4)%Qp) pa pid ga Q K Kp)%I.

  (* THE KERNEL'S QUARTER, in the child's private block. *)
  Definition gen_kq γ pa pid Q : iProp Σ :=
    (∃ ga K Kp, gen_own γ (DfracOwn (1/4)%Qp) pa pid ga Q K Kp)%I.

  (* THE ESCROW.  What a ZOMBIE slot holds for its parent: the kernel's
     quarter of the dead incarnation's generation, and the payload PAID at
     the status the slot's [p_xstate] cell now reads.

     WHY TWO PREDICATES AND NOT ONE.  The party that pays is the exiting
     PROCESS, and what it deposits at the trap boundary is its own
     [my_pay γ Q'] beside [Q' xs] ([UexecRet.uexec_dep_F] at [USYS_exit]):
     a slot may only ever name the payload it can prove it has, which is
     what the persistent half is.  The party that HOLDS the kernel's
     quarter is kexit, out of the dying process's private block
     ([ProcInv.proc_priv_core]), and its [Q] is bound by that block's own
     existential.  The two are THE SAME PREDICATE -- agreement of two
     pieces of one generation -- but only up to the saved predicate's
     later, so pairing them here rather than rewriting one into the other
     is what keeps kexit's park later-free.  [gen_pay] pays the ▷ once, at
     the reaper, where it costs nothing.

     A KILL IS PAID TOO, AND OUT OF THE SAME PAYLOAD.  A process that
     [kill] marked is torn down by the kernel at its next trap, which runs
     [exit(-1)] with the process's own continuation undelivered -- so
     nothing the PROGRAM does can pay at that moment.  What pays is what
     the program handed the kernel when it trapped: its run carries
     [UkRun.ukn_pay N (-1)] as a linear conjunct precisely so that the
     kernel can spend it on the kill path, and hands it back at every
     resume that is not one ([UexecRet.uexec_pay_dep] / [uexec_pay_arm]).
     So a parent gets [Q (-1)] whether its child called [exit(-1)] or was
     killed, and there is exactly one arm here.

     KEYED AT THE STORED STATUS.  [xs] is the value in the slot's
     [p_xstate] cell, whose other half rides this same block
     ([ProcDefs.proc_dormant]); the reaper holds [p->lock], so the half it
     reads through [SchedCtx.proc_pub] and the half beside this escrow
     agree, and the status it copies out to the parent IS this [xs]. *)
  Definition exit_tok γ pid xs : iProp Σ :=
    (∃ pa Q Q', gen_kq γ pa pid Q ∗ my_pay γ Q' ∗ Q' xs)%I.

  (* ------------------------------------------------------------------ *)
  (* AGREEMENT.                                                          *)
  (* ------------------------------------------------------------------ *)

  (* Two pieces of one generation agree on all three components: on the
     slot and the pid PURELY (they are [constOF]), and on the payload up to
     the saved predicate's own later. *)
  (* THE THREE PURE COMPONENTS AGREE PURELY, and the three saved ones up to
     the saved predicate's own later. *)
  Lemma gen_agree_all γ dq dq' pa pid ga Q K Kp pa' pid' ga' Q' K' Kp' :
    gen_own γ dq pa pid ga Q K Kp -∗ gen_own γ dq' pa' pid' ga' Q' K' Kp' -∗
    ⌜pa = pa' /\ pid = pid' /\ ga = ga'⌝ ∗ ▷ (∀ xs, Q xs ≡ Q' xs) ∗
    ▷ (K ≡ K') ∗ ▷ (Kp ≡ Kp').
  Proof.
    iIntros "H1 H2".
    iDestruct (saved_anything_agree with "H1 H2") as "Heq".
    rewrite /gen_el prod_equivI /=.
    iDestruct "Heq" as "[Hv Hr]".
    rewrite prod_equivI /=. iDestruct "Hr" as "[Hf Hkk]".
    rewrite prod_equivI /=. iDestruct "Hkk" as "[Hk Hkp]".
    iDestruct "Hv" as %Hv.
    iSplitR.
    { iPureIntro. change ((pa, pid, ga) = (pa', pid', ga')) in Hv.
      split; [ exact (f_equal (fun z => fst (fst z)) Hv) | ].
      split; [ exact (f_equal (fun z => snd (fst z)) Hv)
             | exact (f_equal snd Hv) ]. }
    iSplitL "Hf".
    { rewrite discrete_fun_equivI.
      rewrite bi.later_forall. iIntros (xs).
      iSpecialize ("Hf" $! xs). by rewrite later_equivI. }
    iSplitL "Hk"; by rewrite later_equivI.
  Qed.

  (* the shape every existing caller wants: the pure half and the payload *)
  Lemma gen_agree γ dq dq' pa pid ga Q K Kp pa' pid' ga' Q' K' Kp' :
    gen_own γ dq pa pid ga Q K Kp -∗ gen_own γ dq' pa' pid' ga' Q' K' Kp' -∗
    ⌜pa = pa' /\ pid = pid' /\ ga = ga'⌝ ∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof.
    iIntros "H1 H2".
    iDestruct (gen_agree_all with "H1 H2") as "($ & $ & _ & _)".
  Qed.

  (* the pure half alone, which is all most callers want *)
  Lemma gen_agree_pure γ dq dq' pa pid ga Q K Kp pa' pid' ga' Q' K' Kp' :
    gen_own γ dq pa pid ga Q K Kp -∗ gen_own γ dq' pa' pid' ga' Q' K' Kp' -∗
    ⌜pa = pa' /\ pid = pid' /\ ga = ga'⌝.
  Proof.
    iIntros "H1 H2". iDestruct (gen_agree with "H1 H2") as "[$ _]".
  Qed.

  (* ...AND THE THREE NEW READINGS' OWN AGREEMENTS, which is what pins an
     incarnation's alive token, its credential and its payment rule.  The
     first is PURE -- the name rides the [constOF] half. *)
  Lemma gen_alive_agree γ ga ga' :
    gen_alive γ ga -∗ gen_alive γ ga' -∗ ⌜ga = ga'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid Q K Kp) "H1".
    iDestruct "H2" as (pa' pid' Q' K' Kp') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & _ & Hga). done.
  Qed.

  Lemma kcred_agree γ K K' : kcred γ K -∗ kcred γ K' -∗ ▷ (K ≡ K').
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid ga Q Kp) "H1".
    iDestruct "H2" as (pa' pid' ga' Q' Kp') "H2".
    iDestruct (gen_agree_all with "H1 H2") as "(_ & _ & $ & _)".
  Qed.

  Lemma kpay_agree γ Kp Kp' : kpay γ Kp -∗ kpay γ Kp' -∗ ▷ (Kp ≡ Kp').
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid ga Q K) "H1".
    iDestruct "H2" as (pa' pid' ga' Q' K') "H2".
    iDestruct (gen_agree_all with "H1 H2") as "(_ & _ & _ & $)".
  Qed.

  Lemma gen_slot_agree γ pa pa' :
    gen_slot γ pa -∗ gen_slot γ pa' -∗ ⌜pa = pa'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pid ga Q K Kp) "H1".
    iDestruct "H2" as (pid' ga' Q' K' Kp') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(Hpa & _ & _). done.
  Qed.

  Lemma gen_pid_agree γ pid pid' :
    gen_pid γ pid -∗ gen_pid γ pid' -∗ ⌜pid = pid'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa ga Q K Kp) "H1".
    iDestruct "H2" as (pa' ga' Q' K' Kp') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & Hpid & _). done.
  Qed.

  (* THE ESCROW'S QUARTER NAMES THE PID ITS GENERATION WAS GIVEN.  Stated
     at the DERIVED forms so a reaper never has to unfold [gen_own] -- the
     conclusion is pure, so both inputs survive ([ProofKwait]'s reap holds
     the quarter across it). *)
  Lemma gen_pid_kq_agree γ pa pid pid' Q :
    gen_pid γ pid' -∗ gen_kq γ pa pid Q -∗ ⌜pid' = pid⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa1 ga1 Q1 K1 Kp1) "H1".
    iDestruct "H2" as (ga2 K2 Kp2) "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & Hpid & _). done.
  Qed.

  (* ...AND THE TWO PERSISTENT READINGS AT THE NAMED SLOT AND PID.  A
     reading has to come off the DISCARDED half, and the half's own slot
     and pid are existential; the kernel's quarter is what names them.
     The quarter comes back -- the agreement it is used for is pure. *)
  Lemma my_pay_kq_readings γ pa pid Q :
    my_pay γ Q -∗ gen_kq γ pa pid Q -∗
    gen_slot γ pa ∗ gen_pid γ pid ∗ gen_kq γ pa pid Q.
  Proof.
    iIntros "#H1 H2".
    iDestruct "H1" as (pa1 pid1 ga1 K1 Kp1) "#Hd".
    iAssert (⌜pa1 = pa /\ pid1 = pid⌝)%I as %[-> ->].
    { iDestruct "H2" as (ga2 K2 Kp2) "H2".
      iDestruct (gen_agree_pure with "Hd H2") as %(Hpa & Hpid & _).
      iPureIntro. exact (conj Hpa Hpid). }
    iSplitR; [ iExists pid, ga1, Q, K1, Kp1; iExact "Hd" | ].
    iSplitR; [ iExists pa, ga1, Q, K1, Kp1; iExact "Hd" | ]. iExact "H2".
  Qed.

  (* a quarter reads the pid the persistent fact records *)
  Lemma child_tok_pid γ pid pid' Q :
    child_tok γ pid Q -∗ gen_pid γ pid' -∗ ⌜pid = pid'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa ga K Kp) "H1".
    iDestruct "H2" as (pa' ga' Q' K' Kp') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & Hpid & _). done.
  Qed.

  (* ...and the child's persistent knowledge is the parent's payload *)
  Lemma my_pay_agree γ Q Q' :
    my_pay γ Q -∗ my_pay γ Q' -∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid ga K Kp) "H1".
    iDestruct "H2" as (pa' pid' ga' K' Kp') "H2".
    iDestruct (gen_agree with "H1 H2") as "[_ $]".
  Qed.

  (* ...and the ESCROW names the pid it is keyed at, off the discarded
     half it carries beside the kernel's quarter: the two are pieces of one
     generation, so they agree on the pid, and the persistent reading is
     therefore free to whoever holds the escrow.  A reaping parent spends
     it to tell the generation it reaped from the one it is waiting for. *)
  Lemma exit_tok_pid γ pid xs : exit_tok γ pid xs -∗ gen_pid γ pid.
  Proof.
    iIntros "H". iDestruct "H" as (pa Q Q') "(Hk & Hmy & _)".
    iDestruct "Hk" as (ga K Kp) "Hk".
    iDestruct "Hmy" as (pa' pid' ga' K' Kp') "#Hmy".
    iDestruct (gen_agree_pure with "Hk Hmy") as %(_ & Hpid & _).
    rewrite /gen_pid Hpid. iExists pa', ga', Q', K', Kp'. iExact "Hmy".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* PID UNIQUENESS OVER A SET OF GENERATIONS -- what makes a returned    *)
  (* pid NAME one of them.                                                *)
  (*                                                                      *)
  (* wait() returns a pid, and a pid is reused; what a parent needs is    *)
  (* that no OTHER child of its own carries the pid it was just handed,   *)
  (* so that the returned number identifies the generation whose escrow   *)
  (* came with it.  That is a fact about the whole set [cs] of the        *)
  (* parent's live children, and it is PERSISTENT: each member's pid is   *)
  (* the persistent reading of its own generation, and the implication    *)
  (* beside it is pure.  It can therefore be extracted under <wait_lock>  *)
  (* -- where the registrations that prove it live                        *)
  (* ([WaitInv.children_inv_pid]) -- and survive the release.             *)
  (*                                                                      *)
  (* A BIG-OP AND NOT A [□]-WAND OVER [gen_pid]: the party that spends it *)
  (* holds [child_tok], a QUARTER, and a quarter cannot produce           *)
  (* [gen_pid] -- the readings come off the DISCARDED half alone.  So the *)
  (* summary has to HAND OUT each member's pid rather than ask for it,    *)
  (* which is what [gen_uniq_tok] then pairs with the parent's token.     *)
  (* ------------------------------------------------------------------ *)
  Definition gen_uniq (cs : gset gname) (pid : mword 32) (γ' : gname) : iProp Σ :=
    ([∗ set] γ ∈ cs, ∃ pidγ : mword 32,
       gen_pid γ pidγ ∗ ⌜pidγ = pid -> γ = γ'⌝)%I.

  Global Instance gen_uniq_persistent cs pid γ' : Persistent (gen_uniq cs pid γ').
  Proof. apply _. Qed.

  (* one member's reading, out of the summary *)
  Lemma gen_uniq_at (cs : gset gname) (pid : mword 32) (γ' γ : gname) :
    γ ∈ cs ->
    gen_uniq cs pid γ' -∗ ∃ pidγ : mword 32,
      gen_pid γ pidγ ∗ ⌜pidγ = pid -> γ = γ'⌝.
  Proof.
    intro Hin. iIntros "H".
    iApply (big_sepS_elem_of _ cs γ Hin with "H").
  Qed.

  (* THE FORM A PARENT SPENDS: it holds a token for one of its children at
     the pid it forked, and the reaper's summary says that child IS the
     generation the escrow is at. *)
  Lemma gen_uniq_tok (cs : gset gname) (pid : mword 32) (γ' γ : gname)
      (Q : Z -> iProp Σ) :
    γ ∈ cs ->
    gen_uniq cs pid γ' -∗ child_tok γ pid Q -∗ ⌜γ = γ'⌝.
  Proof.
    intro Hin. iIntros "Hu Ht".
    iDestruct (gen_uniq_at cs pid γ' γ Hin with "Hu") as (pidγ) "[Hgp %Himp]".
    iDestruct (child_tok_pid with "Ht Hgp") as %Heq.
    iPureIntro. exact (Himp (eq_sym Heq)).
  Qed.

  (* ...AND ITS CONTRAPOSITIVE, which is what a parent whose wait returned
     SOMEBODY ELSE'S pid spends: the generation that was reaped is not the
     one it is waiting for, so its own child is still in the set the reap
     left. *)
  Lemma exit_tok_tok_ne γ' γ (pid pid' : mword 32) (xs : Z) (Q : Z -> iProp Σ) :
    pid <> pid' ->
    exit_tok γ' pid xs -∗ child_tok γ pid' Q -∗ ⌜γ <> γ'⌝.
  Proof.
    intro Hne. iIntros "He Ht".
    iDestruct (exit_tok_pid with "He") as "#Hgp".
    destruct (decide (γ = γ')) as [-> | Hd].
    - iDestruct (child_tok_pid with "Ht Hgp") as %Heq.
      iPureIntro. exfalso. exact (Hne (eq_sym Heq)).
    - iPureIntro. exact Hd.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE PAYMENT RULE -- what the whole file exists for.                  *)
  (*                                                                      *)
  (* INDEXED BY THE GENERATION, NOT BY THE PID: a stale token (child       *)
  (* reaped, escrow dropped, pid reused by a later incarnation) can never  *)
  (* combine, because the two names differ and nothing agrees.            *)
  (* ------------------------------------------------------------------ *)
  Lemma gen_pay γ pid Q xs :
    child_tok γ pid Q -∗ exit_tok γ pid xs -∗ ▷ Q xs.
  Proof.
    iIntros "Ht He".
    iDestruct "Ht" as (pa ga K Kp) "Ht".
    iDestruct "He" as (pa' Q0 Q') "[Hk [Hmy HQ]]".
    iDestruct "Hmy" as (pa'' pid' ga'' K'' Kp'') "Hmy".
    iDestruct (gen_agree with "Ht Hmy") as "[_ Heq]".
    iNext. iSpecialize ("Heq" $! xs). by iRewrite "Heq".
  Qed.

  (* ...AND THE LATER-FREE FORM, at a payload the parent can strip.  The
     conclusion is [◇], not [|==>]: a plain basic update does NOT absorb
     the except-0 modality (its [IsExcept0] instance demands it of the
     body), while every site that could consume the payload -- a fancy
     update, a WP step -- does.  So a TIMELESS payload costs its reaper an
     [iMod] and no step at all. *)
  Lemma gen_pay_timeless γ pid Q xs `{!Timeless (Q xs)} :
    child_tok γ pid Q -∗ exit_tok γ pid xs -∗ ◇ (Q xs).
  Proof.
    iIntros "Ht He".
    iDestruct (gen_pay with "Ht He") as "H".
    iMod "H". by iModIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE MINT, THE CHOICE, AND THE SPLIT.                                 *)
  (* ------------------------------------------------------------------ *)

  (* ALLOCPROC's step: a fresh incarnation of slot [pa] at the pid
     <allocpid> chose, owed nothing.  The trivial payload is what a slot
     that is never forked with a real one keeps. *)
  (* ...AND IT MINTS THE ALIVE TOKEN WITH IT (lane SELF-KILL §3a).  The
     token's name goes into the element, so every later reading of the
     generation says which token belongs to this incarnation, and the
     TOKEN comes out beside the generation for whoever is building the
     process.  The credential and its payment rule start at [emp]: an
     incarnation nobody forked with a real one costs nothing to kill, and
     [gen_set] is where a fork chooses otherwise. *)
  (* WHAT ALLOCPROC HANDS ITS CALLER, as ONE row: the whole generation and
     the token minted with it, at a name only this pair knows.  Bundled
     rather than handed out as two rows so that [SpecAllocproc]'s post
     keeps its arity and every pass-through site is untouched. *)
  Definition gen_fresh γ pa pid : iProp Σ :=
    (∃ ga, gen_own γ (DfracOwn 1) pa pid ga (fun _ => True)%I emp emp ∗
           alive_tok ga)%I.

  Lemma gen_alloc pa pid :
    ⊢ |==> ∃ γ, gen_fresh γ pa pid.
  Proof.
    iMod alive_tok_alloc as (ga) "Hga".
    iMod (saved_anything_alloc (F := genF)
            (gen_el pa pid ga (fun _ => True)%I emp emp) (DfracOwn 1)
            ltac:(done)) as (γ) "Hg".
    iModIntro. iExists γ, ga. iFrame "Hg Hga".
  Qed.

  (* the two halves of the fresh row, for a caller that wants them apart *)
  Lemma gen_fresh_split γ pa pid :
    gen_fresh γ pa pid -∗
    ∃ ga, gen_own γ (DfracOwn 1) pa pid ga (fun _ => True)%I emp emp ∗
          alive_tok ga.
  Proof. rewrite /gen_fresh. iIntros "H". iExact "H". Qed.

  (* KFORK's first step: the FORKING PARENT chooses what the child's exit
     will owe.  Only at FULL ownership -- once the quarters are out, the
     payload is fixed for the life of the incarnation. *)
  (* ...AND THE CREDENTIAL AND ITS PAYMENT RULE ARE CHOSEN HERE TOO, in one
     step with the payload: the three are the fork row's single decision
     about what this child is worth, and the alive token's NAME is not
     among them -- it was minted with the incarnation and does not move. *)
  Lemma gen_set γ pa pid ga Q K Kp Q' K' Kp' :
    gen_own γ (DfracOwn 1) pa pid ga Q K Kp ==∗
    gen_own γ (DfracOwn 1) pa pid ga Q' K' Kp'.
  Proof.
    iApply (saved_anything_update (F := genF) (gen_el pa pid ga Q' K' Kp')).
  Qed.

  (* ...and its second: the three pieces, out of the whole.  1/4 to the
     parent, 1/4 to the kernel's copy in the child's block, and the
     remaining half DISCARDED -- which is what makes [my_pay] (and with it
     [gen_slot] / [gen_pid]) persistent. *)
  (* ...AND THE PERSISTENT THIRD PIECE IS THE WHOLE READING NOW: the party
     that cuts the generation knows all four components, and each later
     reader wants a different one ([gen_know_my_pay] and its three
     siblings).  Handing out [my_pay] alone would lose the alive token's
     name and the credential at the one point where they are known. *)
  Lemma gen_split γ pa pid ga Q K Kp :
    gen_own γ (DfracOwn 1) pa pid ga Q K Kp ==∗
    child_tok γ pid Q ∗ gen_kq γ pa pid Q ∗ gen_know γ ga Q K Kp.
  Proof.
    iIntros "H". rewrite /gen_own.
    iEval (rewrite -Qp.half_half) in "H".
    iDestruct "H" as "[H1 H2]".
    iMod (saved_anything_persist with "H2") as "#Hp".
    iEval (rewrite -Qp.quarter_quarter) in "H1".
    iDestruct "H1" as "[Ha Hb]".
    iModIntro. iSplitL "Ha".
    { iExists pa, ga, K, Kp. iExact "Ha". }
    iSplitL "Hb"; [ iExists ga, K, Kp; iExact "Hb" |].
    iExists pa, pid. iExact "Hp".
  Qed.

  (* the escrow, built PAID: what kexit does with the block's quarter and
     the DEPOSIT the exiting process made at the trap boundary -- the
     process's own [my_pay] and the payload paid at the status kexit
     stored. *)
  Lemma exit_tok_intro γ pa pid Q Q' xs :
    gen_kq γ pa pid Q -∗ my_pay γ Q' -∗ Q' xs -∗ exit_tok γ pid xs.
  Proof. iIntros "Hk #Hmy HQ". iExists pa, Q, Q'. iFrame "Hk Hmy HQ". Qed.

End ChildTok.

Global Typeclasses Opaque gen_own.
