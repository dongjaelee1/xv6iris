(* App.v -- APPLICATIONS: the record, and the whole-system theorem at one.

   Design of record: claude-notes/design/applications.md and the
   application-side sections of claude-notes/projects/app-echo.md (the
   "app-instances.md" this header used to cite does not exist; its round
   and section numbers survive below as cross-references into those two).
   An application is a collection of user programs plus what it
   claims -- a FIXED PART (section 6 ruling 1: a [Type] of its own, born
   once by its birth step and carried by the machine's record for the
   whole run), a predicate on the abstract file-system state's VIEW at the
   fixed part and at its own per-instance ghost names ([AppCfg.appcfg]'s
   data), what it is lent at every boot about the durable state, a trace
   ledger, and a pure conclusion.  The DATA is the record [xv6_app]; the
   OBLIGATIONS are the premises of [xv6_app_adequacy], stated exactly as
   [SystemAdequacy.xv6_power_adequacy_gen] states them (at the raw gnames
   and the fixed part, the [boot_fixedGS] literal), so that an application
   that can pay some and not others is a DEFINITION and never a vacuous
   theorem.

   THE GENERIC APPLICATION [app_triv] -- user space does anything, the
   abstract state is anything, the kernel stays correct -- pays every
   obligation trivially; [SystemAdequacy.xv6_trace_adequacy] and its
   siblings are [xv6_power_adequacy_gen] at exactly its data.  The first
   non-trivial application is [AppEcho.v]; what it still owes is
   claude-notes/projects/app-echo.md.

   THE OBLIGATIONS ARE SIX FAMILIES, and that is all of them: [Hbirth],
   [Happ_xfer], [Happ_init], [Hinit_boot], the trace ledger's ([HR0],
   [HRt], [Hpow], [Htx], [Hrx]) and [Hphi].  There is no parked license:
   the BLANKET PROMISE that the claim survives every one-row move of the
   map is gone, because the AU fires' steps come out of the PROCESS's own
   deposit ([UexecSG.sbundle_at]); and there is no supply either -- the
   kernel mints no user-execution slot, so what the application owes about
   user execution is the FIRST PROCESS'S EXEC BUNDLE and nothing else.

   HOW THE PIECES MEET THE THEOREM.
   - [app_fixed]/[app_cl] are the BIRTH STEP: [Hbirth] runs FIRST in
     [RiscvAdequacy.riscv_power_adequacy], before the crash slot, and the
     value it yields is [RiscvPtsto.riscv_client] of every era's record.
   - [app_names]/[app_pred] become the era's [AppCfg.appcfg]:
     [SystemAdequacy.xv6_boot_era] builds the record
     [MkAppcfg _ (app_pred c) r] -- the fixed part APPLIED -- at the
     running instance [r] the boot obligation witnesses and threads it to
     the era mint ([FsCfgSnap.fs_cfg_alloc_snap]), which founds the
     application's invariant ([AppInv.app_inv]: its half of the abstract
     map's authority beside its claim) at the founded map's view.  The
     claim IS the application's DURABLE one (app-instances.md round C):
     the crash slot is the composite [SystemAdequacy.xv6_slot] -- the file
     system's record beside the application's claim at the same snapshot
     name ([AppDur.app_dur_raw]) -- the PowerOn arm clones it onto the
     lend by the TRANSPORT [Happ_xfer], and the boot founds the era from
     the lent claim.  Era 0's claim is [Happ_init], at the image's state.
   - [Hinit_boot] is the FIRST PROCESS'S EXEC BUNDLE
     ([InitBoot.init_boot_bundle]): kexec's caller-side bundle at "/init",
     whose SLOT PIECE answers at the key kexec builds.  forkret's boot arm
     runs that kexec between the first park and the first resume, so no
     slot the kernel could have minted survives it -- which is why this,
     and not a supply, is what the application owes about user execution.
     The generic application discharges it from the trivial mint
     ([SystemAdequacy.init_boot_of_triv]); a constraining application
     discharges it from its own pinned bundle at "/init".  Either way it
     is a discharged premise, not a gap (see [SystemAdequacy]'s
     [Hinit_boot]).
   - [app_R c] is the trace slot's resource at the fixed part; [HR0]
     RECEIVES the birth step's yield ([obs_ledger_at_alloc_cl]) -- for the
     echo application, its taint counter at 0; the power step and the two
     UART-arm wands are [xv6_trace_adequacy]'s, quantified over the fixed
     part (the record's [riscv_client] is it by iota at the boot).
   - [app_phi] is read at the end of the run by [Hphi], which holds the
     crash predicate and the ledger side by side -- which is where an
     application relates "the input kept the discipline" (its counter at
     0) to "the durable state is still what it claims" (the crash
     predicate's arm of the disjunction; lane L4). *)
(* Require block: SystemAdequacy.v's, VERBATIM (durable-notes: trimmed
   imports have OOM'd the build), plus this file's own lines. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang ObsTrace RiscvPtsto.
Require Import FsState.
Require Import FsAbsDefs.        (* [aview], [abs_view]: the claim is over the view *)
Require Import InitBoot.         (* [init_boot_bundle]: the first process's
                                    exec bundle, the application's one
                                    obligation about user execution *)
Require Import InodeInv.         (* [ROOTINO] *)
Require Import AppCfg.           (* [MkAppcfg]: the era's application record,
                                    which [Hinit_boot]'s equation names *)
Require Import AppInv.           (* [app_sup_raw]: the supply, at the raw
                                    gname *)
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import VirtioModel.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FsImg.
Require Import ProcAvail.
Require Import Xv6G.
(* ...and the rest of SystemAdequacy's block, which the first cut missed:
   a class name that is not in scope silently becomes a VARIABLE
   (durable-notes), which is how [ufdG] became one here once. *)
Require Import UserFd.
(* ...and this file's own *)
Require Import SystemAdequacy.
Require Import FsBootParams.  (* [XV6_DISK_BYTES], [fsimg_cov], [fsimg_nib] *)
Require Import CtxIdDefs.             (* [CurCtx]: the echo obligation's context *)
Require Import SpecConsoleintr.    (* [cons_echo_shift]: the echo obligation  *)
(* the image's own superblock and region width, and the disk literal, for
   the closed corollary at the real image *)
Require Import FsImgCheck.
Require FsImgDisk.
Local Open Scope Z_scope.

Record xv6_app (Σ : gFunctors) := MkApp {
  (* THE FIXED PART (app-instances.md section 6 ruling 1): its type, and
     what the birth step yields about a value of it -- born once, before
     the crash slot, and the machine record's [riscv_client] for the run *)
  app_fixed : Type;
  app_cl    : app_fixed -> iProp Σ;
  (* the application's own per-instance ghost names, and its predicate on
     the abstract state's VIEW at the fixed part and an instance
     (section 1): an iProp -- a claim that OWNS resources -- and, applied
     at the fixed part, the era's [AppCfg.app_pred] *)
  app_names : Type;
  app_pred  : app_fixed -> app_names -> aview -> iProp Σ;
  (* WHAT THE ERA'S INSTANCE IS BORN WITH BESIDE ITS CLAIM (lane APP-IFACE
     item (a), review-echo-plan finding 6): the resource the FIRST PROCESS'S
     proof is handed at [Hinit_boot] -- for the echo application, the
     console-absence key /init carries from its first [open] to its [mknod].
     LINEAR, so it cannot live inside the claim (a resource borrowed from
     the claim has to go back) and cannot be persistent (then it would say
     nothing); its producer is therefore the TRANSPORT, which is where the
     era's instance is born ([Happ_boot]).  [emp] for an application that
     wants nothing. *)
  (* ...AT THE ERA (lane CONS-IO milestone C): the boot resource is the
     era's, so it carries the era's NUMBER beside its instance. *)
  app_boot  : app_fixed -> nat -> app_names -> iProp Σ;
  (* the trace ledger, at the fixed part (section 4) *)
  app_R     : app_fixed -> list mobs -> iProp Σ;
  (* THE INPUT TAG (app-echo.md lane L5): what the application claims of a
     byte the environment pushed, at the history it arrived at.  Persistent
     (the obligation [Htagp] below), because the UART's receive column keeps
     one per queued byte and every reader copies it out.  It is the record's
     entry for the machine's ambient [RiscvPtsto.riscv_rx_tag]. *)
  app_tag   : app_fixed -> list mobs -> iProp Σ;
  (* THE KILL CREDENTIAL (app-echo.md lane KILL-PAY, K1): what the
     application charges for a kill.  The record's entry for the machine's
     ambient [RiscvPtsto.riscv_kill_cred]: a kill is legal, and every party
     it touches -- the killer, the killed slot's public payload, the trap
     that observes [p->killed], the -1 the process exits with, the -1 a
     console read returns -- is handed this.  A verified continuation
     therefore goes GENERIC where a kill could have happened, instead of
     being refuted.
     PERSISTENT and TIMELESS (the obligations [Hkillp]/[Hkillt] below), and
     BOUGHT BY THE SUPPLY ([Happ_kill]): the generic user-execution slot
     runs on [AppInv.app_sup_raw], so the credential has to be free to
     anything that already holds the application's supply -- which is what
     lets the kernel charge the kill price at a trap it cannot rule out
     without charging any verified program.  For echo it is the TAINT
     ([AppEcho.echo_taint], bought by [echo_taint_of_sup]); [True] for an
     application that puts no price on a kill. *)
  app_kill  : app_fixed -> iProp Σ;
  (* [app_out] and [app_in] lived here: the output claim and the input log,
     the two halves of the console I/O boundary.  [app_cons] below is the
     successor -- one claim over one console history (redesign R2). *)
  (* THE ERA'S CONSOLE TURN (app-echo.md, "E5 -- THE APPLICATION CLAIM",
     lane CONS-IO milestone F): what <init> is handed at the era's boot,
     beside [app_boot].  The kernel neither reads it nor mints it: [Hpow]'s
     power-on arm yields it once per era, the boot carries it
     ([RiscvAdequacy.power_boot_res] -> [Hinit_boot] ->
     [UInitKernel.init_boot_pay] -> [UkInitMain.wp_kinit_start]) and <init>
     holds it.  It is the application's own resource, so it can be the
     linear right to speak first on the console -- which is exactly what an
     echo discipline needs and what nothing per-era can say by itself. *)
  app_turn  : app_fixed -> nat -> iProp Σ;
  (* [app_win] lived here: the era's echo window token, LENT to the kernel
     because a persistent shift over a SPLIT run needed one linear thing per
     era to tell a first firing from a second.  The arm is a field of the
     console history now, so the kernel's own [WpUart.uart_arm] says which
     arm is open and no token has to stand in for it. *)
  (* THE CONSOLE CLAIM (redesign R2/R3): what the application claims of the
     whole console boundary -- the bytes the UART has accepted, the
     accepted-input log, what a process has been given, and the arm
     consoleintr has in progress.  Read against an input-history prefix of
     the run.  A RESOURCE and not a [Prop], because a pure predicate cannot
     say WHO may write and the console echo's shift is then unprovable
     against an impostor's byte ([RiscvPtsto.riscv_cons_res]'s paragraph is
     the argument).

     THE CONSOLE'S ONLY.  The board has two 16550s and by the owner's ruling
     the kernel's own port (printk, panic) is unconstrained, so the UART
     invariant indexes for us ([WpUart.chist_at] is this at [Uart0] and
     [emp] at [Uart1]) and this field says nothing about a port.

     INDEXED BY THE ERA NUMBER (lane CONS-IO milestone C).  A process of a
     dead era keeps its linear writer's token inside that era's closed
     invariants and nothing can reclaim it at power-off, so an era-agnostic
     link would let a stale writer pay the CURRENT era's claim; the pure
     index [k = S gen_id] excludes it, and the kernel's STAMP
     [obs_boots h = S gen_id] on every history it hands over is what makes
     the era's facts pure.

     ITS FOUNDING IS THE APPLICATION'S OWN, AT THE POWER-ON STEP (lane
     CONS-IO milestone E, e5-design REVISION 8; see [Hpow] below) and not
     the transport's: a transport is a [□] over a bupd that returns its own
     input, so a founding derivable from it is derivable unboundedly.
     [emp] for an application that claims nothing of the console. *)
  app_cons  : app_fixed -> nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ;
  (* the conclusion, over the operational state and the run's trace *)
  app_phi   : gstate -> list mobs -> Prop;
}.
Arguments MkApp {Σ} _ _ _ _ _ _ _ _ _ _ _.
Arguments app_fixed {Σ} _. Arguments app_cl {Σ} _ _.
Arguments app_names {Σ} _. Arguments app_pred {Σ} _ _ _ _.
Arguments app_boot {Σ} _ _ _ _.
Arguments app_R {Σ} _ _ _. Arguments app_tag {Σ} _ _ _.
Arguments app_kill {Σ} _ _.
Arguments app_turn {Σ} _ _ _.
Arguments app_cons {Σ} _ _ _ _.
Arguments app_phi {Σ} _ _ _.

(* THE GENERIC APPLICATION: no fixed part, nothing claimed, nothing read *)
Definition app_triv (Σ : gFunctors) : xv6_app Σ :=
  MkApp unit (fun _ => True%I) unit (fun _ _ _ => True%I) (fun _ _ _ => emp%I)
        (fun _ _ => emp%I) (fun _ _ => True%I) (fun _ => True%I)
        (* the era's turn: the generic application has no console
           discipline, so it is [emp] (lane CONS-IO F) *)
        (fun _ _ => emp%I)
        (* the console claim: nothing claimed (redesign R2) *)
        (fun _ _ _ _ => emp%I)
        (fun _ _ => True).

(* ---------------------------------------------------------------------- *)
(* THE THEOREM.  [xv6_power_adequacy_gen] at the application: the birth    *)
(* step is [app_cl]'s, the trace slot is the ledger of [app_R] at the fixed *)
(* part, the lend is the FS's epoch beside [app_lend], the era's predicate  *)
(* is [app_pred] at the fixed part and the instance the boot obligation     *)
(* witnesses.                                                               *)
(* ---------------------------------------------------------------------- *)
Theorem xv6_app_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}
    `{!ufdG Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (A : xv6_app Σ)
    (* ---- THE BIRTH STEP (app-instances.md section 6 ruling 1): one value
       of the fixed part, with what [app_cl] says of it ---- *)
    (Hbirth : ⊢ |==> ∃ c : app_fixed A, app_cl A c)
    (* ---- the trace ledger's obligations ([xv6_trace_adequacy]'s, the
       birth step's yield received at the ledger's birth) ---- *)
    (HRt : forall (c : app_fixed A) (h : list mobs), Timeless (app_R A c h))
    (* the tag is copied out of the UART's receive column once per reader,
       so it has to be duplicable by construction *)
    (Htagp : forall (c : app_fixed A) (h : list mobs), Persistent (app_tag A c h))
    (* ...and timeless, because the receive column that files it lives in the
       UART invariant, whose body every device leaf strips a later off *)
    (Htagt : forall (c : app_fixed A) (h : list mobs), Timeless (app_tag A c h))
    (* THE KILL CREDENTIAL'S THREE (lane KILL-PAY, K1).  Persistent and
       timeless for the reasons the tag's are -- every party a kill touches
       keeps a copy, and it rides invariant bodies the lock and device
       leaves strip a later off -- and BOUGHT BY THE SUPPLY, which is what
       makes the kernel's kill price payable by the generic slot and by no
       verified program.  echo's is [AppEcho.echo_taint_of_sup]. *)
    (Hkillp : forall c : app_fixed A, Persistent (app_kill A c))
    (Hkillt : forall c : app_fixed A, Timeless (app_kill A c))
    (Happ_kill : forall (c : app_fixed A) (r : app_names A),
       AppInv.app_sup_raw (app_pred A c) r ⊢ □ app_kill A c)
    (* THE CONSOLE CLAIM IS TIMELESS (redesign R2), for the reason the tag
       is: it lives in the console UART's invariant, whose body every device
       leaf strips a later off.  It is NOT persistent -- it holds the
       application's own authority over whose turn it is to write and how
       far the transcript has got, which is exactly what a pure predicate
       could not express.  Its FOUNDING is [Hpow]'s POWER-ON ARM below (lane
       CONS-IO milestone E); and NOTHING ELSE IS OWED, because the
       invariant's own steps preserve the claim without any monotonicity
       law -- the accepted bytes move only at the store, and the witness
       history moves only inside a writer's own shift.  An application's
       input-monotonicity is its private business, used inside the shifts it
       writes and inside [Htx] below. *)
    (Hconst : forall (c : app_fixed A) (k : nat) (h : list mobs)
                     (H : LogEntryDefs.cons_hist), Timeless (app_cons A c k h H))
    (* WHAT HOLDING THE APPLICATION'S SUPPLY ENTITLES A PROCESS TO (lane
       OUT-FUPD, the generic write's payment; KILL-ARM's mould).  Since the
       console claim is a RESOURCE, an arbitrary process's [write(2)] on the
       console is no longer free: the kernel's GENERIC SUPPLY
       ([UexecExecInst.xv6_ssupply]) carries a LICENCE
       ([WpUart.out_licence]) and this is where its price is set.  The
       trivial application pays it out of [emp]; a constraining one pays it
       out of the TAINT arm of its own claim -- a process holding the
       generic supply is one the discipline has already accounted for, so
       letting it emit an arbitrary byte weakens nothing.  It is the exact
       twin of KILL-ARM's [Happ_kill], and lands beside it.

       QUANTIFIED OVER THE ERA (milestone C): the generic process is any
       era's, so one licence covers them all.

       ONE LICENCE (redesign R2), where there were two: the supply moves the
       application's console claim by ANY boundary event.  It covers the
       generic [write(2)]'s byte, the console interrupt's shift and
       [read(2)] on fd 0 alike, because all three are events on one
       resource; [Happ_in_sup] is gone. *)
    (Happ_out_sup : forall (c : app_fixed A) (r : app_names A),
       AppInv.app_sup_raw (app_pred A c) r
         ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
                (ev : ConsLog.cons_ev),
                app_cons A c k h H ==∗
                app_cons A c k h (ConsLog.cons_step H ev)))
    (HR0 : forall c : app_fixed A, app_cl A c ⊢ |==> app_R A c [])
    (* THE POWER STEP -- AND, SINCE lane CONS-IO milestone E, THE FOUNDING
       OF THE ERA'S TWO PORT CLAIMS (e5-design REVISION 8).  Until E the
       claims were founded by the TRANSPORT ([Happ_boot] below yielded them
       at [[]]), and that was unsound as a discipline: [app_xfer_boot_raw]
       is a [□] over a bupd whose only input it hands straight back, so
       [app_out A c k [] []] was derivable UNBOUNDEDLY from nothing and no
       ledger fact could refute a claim "reset" to the founded arm.  The
       power-ON arm is the one step of the machine that runs the
       application's LEDGER and runs ONCE PER ERA, so it is where a LINEAR
       seed for the era can be minted: the application takes [app_R] at the
       pre-event history, mints the era's seed inside its own ledger, and
       yields the two claims for the era the event starts.
       THE ERA IS [S (obs_boots h)], read off the PRE-event history: the
       ledger has no [GenId] to state a stamp at, and
       [ObsTrace.obs_boots_app] gives [obs_boots (h ++ [ObsPowerOn]) =
       S (obs_boots h)], so this IS the boot count of the post-event
       history -- the number the kernel's own stamp ([Htx]/[Hrx]'s
       [⌜obs_boots h = S gen_id⌝]) will read at every history of the new
       era.  The kernel matches it to the era it boots by
       [ObsTrace.obs_wf], whose boot count at a powered-OFF machine is
       [ggen] exactly ([RiscvAdequacy]'s PowerOn arm).
       NOTHING IS OWED ON THE OFF ARM: a power-off starts no era. *)
    (Hpow : forall (c : app_fixed A) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A c h ==∗
         app_R A c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
         (if on then emp
          else app_cons A c (S (obs_boots h)) []
                 (LogEntryDefs.MkCH [] [] [] None) ∗
               (* ...AND THE ERA'S TURN (lane CONS-IO milestone F).  The
                  same arm and the same reason: this is the one step of the
                  machine that runs the application's ledger exactly once
                  per era, so it is the only place a per-era LINEAR thing
                  can be minted, and the kernel carries it to <init>. *)
               app_turn A c (S (obs_boots h))))
    (* the two UART-arm wands, at any value of the fixed part: the era
       instance's [riscv_client] is the one the boot's record carries, and
       the record's client type is [app_fixed A] only at that literal *)
    (* THE ERA IDENTIFICATION (lane APP-IFACE item (c), review-echo-plan
       finding 3).  These two used to be quantified over an ARBITRARY
       [γ : uart_names], so the ledger could learn nothing about THE ERA's
       UART ghosts at an event -- and the whole output side rests on doing
       exactly that ([SystemUartAccepted.v]'s header, app-echo.md O4).  They
       are quantified over the ERA's [fileG] instead, with the two equations
       the boot HAS and hands over: the era's application record, and
       [fsc_uart] -- the [γ] every kernel-side UART fact of this era is
       stated at.  This is [Hinit_boot]'s own shape, and it is not a new
       assumption about the world: it NARROWS the wands' domain from every
       [γ] to the era's. *)
    (* THE GENERATION BINDER (lane CONS-IO milestone C).  The two wands had
       none: they are the LEDGER's steps, and the ledger spans eras, so
       nothing in them could name the era an event belongs to.  They take
       one now, because the kernel STAMPS the history it hands over
       ([⌜obs_boots h = S gen_id⌝], out of [ObsTrace.obs_wf] at a live UART
       thread) and reads the two port claims at THAT era's index.  It is a
       [forall], so the application still owes the step at every era; what
       it buys is that the era is NAMED and the claim's index is pure. *)
    (Htx : forall (HR : riscvGS Σ) (GEN : GenId) `{HF : !fileG Σ}
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (* THE ERA IDENTIFICATION IS THE CONSOLE'S.  Only that port's ghosts
          are the era's [fsc_uart]; the other port has its own bundle and no
          kernel fact is stated at it, so the tie is conditional on which
          port the arm belongs to. *)
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       (* AT EVERY PORT.  The board has two 16550s and either may step, so
          the ledger owes an account of an event on EITHER -- an untagged
          obligation would let a byte on the kernel's port slip past the
          claim about the console's. *)
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
              (ho : list mobs) (H : LogEntryDefs.cons_hist),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              (* THE WIRE IS THE DRAINED SEQUENCE.  A clause of the UART
                 invariant's receive column since TX-TAG's rider
                 ([WpUart.uart_colE_wire_out]), handed over here because it
                 is what makes the accepted sequence an EXTENSION of the
                 wire: [uart_acc u = u_out u ++ u_tx u] and [u_wire u =
                 u_out u], so the wire is a prefix of [uart_acc u] and a
                 prefix-closed output claim transfers to it.  This closes
                 the premise TX-TAG left owed to E5. *)
              ⌜u_wire u = u_out u⌝ -∗
              (* ...AND THE ERA STAMP (lane CONS-IO milestone C): the era
                 this history belongs to is [S gen_id], which is the index
                 the two claims below are read at. *)
              ⌜obs_boots h = S gen_id⌝ -∗
              (* ...AND THE OUTPUT CLAIM at the drain (lane OUT-FUPD), at a
                 WITNESS HISTORY [ho] the console invariant holds a monotone
                 lower bound on -- so [ho] is a real prefix of the run's own
                 history, and the application lifts the claim from [ho] to
                 [h] by its own input-monotonicity.  Every accepted byte was
                 justified at its store by the writer's own view shift, so
                 this is where the kernel's output discipline reaches the
                 ledger -- and it is the only channel: the invariant carries
                 no application resource.  Conditional on the port, because
                 the kernel's own UART constrains nothing. *)
              ⌜ho `prefix_of` h⌝ -∗
              (* ...AND THE ACCEPTED BYTES ARE THE HISTORY'S OWN FIELD
                 (redesign R2).  It used to be an argument, because the
                 output claim was stated over them; the merged claim keeps
                 them inside, so the tie the drain needs is a premise. *)
              ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
              (* ...TAKEN LINEARLY AND GIVEN BACK.  The claim is the
                 application's own authority, so the ledger step reads it
                 against its own ledger and returns it to the invariant it
                 was borrowed from.  ONE claim at ONE witness, where there
                 were two at two. *)
              (if i is Uart0 then app_cons A c (S gen_id) ho H else emp) -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              (if i is Uart0 then app_cons A c (S gen_id) ho H else emp) ∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartOut i b])%list))
    (Hrx : forall (HR : riscvGS Σ) (GEN : GenId) `{HF : !fileG Σ}
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              (* the arrival's era, on [Htx]'s mould (milestone C) *)
              ⌜obs_boots h = S gen_id⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartIn i b])%list ∗
              app_tag A c (h ++ [ObsUartIn i b])%list))
    (* ---- the application's three obligations on its predicate
       (app-instances.md sections 1-3, round C): the TRANSPORT (its one
       durability obligation -- a copy of the claim at fresh instance names,
       under the later every crossing hands it over at), the ERA-0 claim
       at the image's own abstract state, and the supply ---- *)
    (* ...the TRANSPORT, which since lane APP-IFACE item (a) also hands the
       clone its own BOOT RESOURCE ([app_xfer_raw_of_boot] is the old
       obligation, and is what the commit's law and the era mint keep
       taking).  The transport is the producer because the era's instance is
       born there: the machine starts powered OFF, so every boot -- era 0's
       included -- founds its file system from the PowerOn arm's clone, and
       [Happ_init]'s instance never reaches one. *)
    (* ...AT EVERY ERA (lane CONS-IO milestone C): the boot resource is
       era-indexed, so the transport takes the era's NUMBER and yields it
       at that index.  [app_xfer_boot_raw] itself is unchanged -- the index
       is applied before it. *)
    (* ...AND IT FOUNDS NOTHING ELSE (lane CONS-IO milestone E): the two
       port claims rode here from OUT-FUPD until e5-design REVISION 8, and
       they are [Hpow]'s yield now. *)
    (Happ_boot : forall (c : app_fixed A) (k : nat),
       ⊢ app_xfer_boot_raw (app_pred A c) (app_boot A c k))
    (Happ_init : forall c : app_fixed A,
       ⊢ |==> ∃ r : app_names A,
           app_pred A c r (abs_view (fss_inodes (FsDurImg.img_state
              (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))))
    (* ...and THE FIRST PROCESS'S EXEC BUNDLE (ARM-c): the one thing the
       application owes the kernel about user execution.  Quantified over
       the era's ghost classes for the reason
       [SystemAdequacy.xv6_power_adequacy_gen]'s own [Hinit_boot] gives --
       they are born by the boot mint -- and its paragraph carries the
       argument for why it is not the GAP-premise trap. *)
    (Hinit_boot :
       forall (HR : riscvGS Σ) (GEN : GenId)
              `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
                HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
              (c : app_fixed A) (r : app_names A),
         @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
         (* (b) THE RX-TAG EQUATION (lane APP-IFACE): the machine's ambient
            input-tag family IS this application's.  A FACT about the
            instance the theorem is taken at -- the [boot_fixedGS] literal
            below fixes the field to [app_tag A c] -- not an assumption
            about the world, and the premise a pinned <init> discharges
            [UConsLine.ush_tag_law] from. *)
         riscv_rx_tag = app_tag A c ->
         (* ...and (K1) THE KILL-CREDENTIAL EQUATION, on the same mould:
            the machine's ambient kill credential IS this application's. *)
         riscv_kill_cred = app_kill A c ->
         (* ...and (b') THE GENERATION-COUNTER EQUATION (lane APP-IFACE, the
            same pattern as the rx-tag one above).  The era's [A] is FIXED
            before [HR] exists, so the camera [A]'s own predicate carries
            for the taint counter is the PRE-structure's, while [AppInv]'s
            laws ABOUT that predicate are at the FIXED layer's.
            [RiscvAdequacy.boot_fixedGS] fills every anonymous class slot
            from [riscvGpreS] (its header: "All resolve from
            [riscvGpreS]"), so at the instance this theorem is taken at the
            two are the SAME TERM -- a fact about that instance, not an
            assumption about the world, and the premise that lets the
            record's predicate meet [AppInv]'s laws. *)
         @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
         (* ...and (b'') THE CONSOLE-CLAIM EQUATION (redesign R2), the
            rx-tag equation's twin and true for the same reason: the
            [boot_fixedGS] literal below fixes the field to [app_cons A c].
            It is what lets a pinned <init> turn [Happ_out_sup] into the
            machine's [WpUart.out_licence] and so build its own generic
            slot ([SystemAdequacy.init_boot_of_sup]'s premise). *)
         @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = app_cons A c ->

         (* ...and (a) THE BOOT RESOURCE, LINEARLY, at the instance the
            record equation names *)
         ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot A c (S gen_id) r -∗
           (* ...and (a') THE ERA'S TURN beside it (lane CONS-IO milestone
              F): the application's own per-era credential, minted at the
              power-on step and carried here by the kernel.  <init> holds
              it; lane IO-LEAF spends it at the era's first banner byte. *)
           app_turn A c (S gen_id) -∗
           |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0)
    (* THE ECHO'S JUSTIFICATION (lane OUT-FUPD, F3), the SECOND thing this
       record owes the kernel about the console and [Hinit_boot]'s twin.
       consoleintr echoes an input byte through consputc at [Uart0] -- the
       port whose invariant carries THIS application's output claim -- and
       it runs on the interrupt path, holding nothing it could pay the
       store's view shift with.  So the payment is the application's:
       "the accepted bytes extended by the echo of an input byte stay
       good", once, persistently, minted into
       [SpecConsoleintr.console_caps] at main and re-used by every byte.

       WHAT IT MAY ASSUME, and it is everything consoleintr holds: the
       byte's own arrival history [h], the fact that the history ENDS in
       that byte ([ObsTrace.obs_ends_in Uart0 h c]), this record's tag at
       [h], the monotone bound [RiscvPtsto.obs_hist_lb h], and the ARM's
       SHAPE ([SpecConsoleintr.cons_echo]: nothing, the byte itself, or a
       run of erase triples AND ONLY FOR AN ERASE BYTE).  The two record
       equations are the ones [Hinit_boot] takes, and for the same reason:
       the shift reads the machine's AMBIENT tag family and its AMBIENT
       output claim, and at the [boot_fixedGS] literal below both ARE this
       record's.  Quantified over the context because nothing in the shift
       is context-relative and the boot chain runs at the boot hart's own
       [CtxIdDefs.CtxId]. *)
    (Happ_echo :
       forall (HR : riscvGS Σ) (c : app_fixed A),
         (* the shift FILES the accepted byte and justifies its echo out
            of ONE claim now (redesign R2), so one equation carries it *)
         @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = app_cons A c ->
         @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = app_tag A c ->

         (* AT EVERY ERA (milestone C): the shift is era-indexed and takes
            the era stamp on the byte's history, so the obligation is
            quantified over the generation as it is over the context. *)
         ⊢ ∀ (GEN : GenId) (XI : CurCtx),
             @SpecConsoleintr.cons_echo_shift Σ HR GEN XI)
    (* ---- the conclusion's proof, at the end of the run: it holds the
       COMPOSITE crash slot ([SystemAdequacy.xv6_slot]: the file system's
       record beside the application's durable claim at the same snapshot
       name) and the ledger side by side ---- *)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs γhist : gname) (c : app_fixed A)
                   (T : list mobs) (g' : gstate) (h : list mobs),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                  γd γsw γreg γstart c)
               γobs T (obs_ledger_at (app_R A c) γobs) γhist
               (app_tag A c) (Htagp c) (Htagt c)
               (app_kill A c) (Hkillp c) (Hkillt c)
               (app_cons A c) (Hconst c)
               (app_fixed A) c) g' -∗
         ghost_var γobs (1/2) h -∗ ⌜obs_wf h g'⌝ -∗
         ▷ xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
             γd γsw γreg γstart c -∗
         ▷ obs_ledger_at (app_R A c) γobs -∗
         ◇ ⌜app_phi A g' h⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ app_phi A g2 κs.
Proof.
  (* the permit at the ledger: the application's two wands, at the record
     the era boots over -- where [riscv_client] IS the fixed part the
     ledger was born with, by iota once the record's shape is destructed *)
  assert (Hperm : forall (HR : riscvGS Σ) (GEN : GenId) (HF : fileG Σ)
                         (r : app_names A) (i : uart_id) (γ : uart_names),
      (exists (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs γhist : gname)
              (c : app_fixed A) (T : list mobs),
         riscv_fixedGS =
           boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
             (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                γd γsw γreg γstart c)
             γobs T (obs_ledger_at (app_R A c) γobs) γhist
             (app_tag A c) (Htagp c) (Htagt c)
             (app_kill A c) (Hkillp c) (Hkillt c)
             (app_cons A c) (Hconst c)
             (app_fixed A) c
         /\ @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r
         /\ (i = Uart0 -> FsCfg.fsc_uart = γ)) ->
      ⊢ obs_inv -∗ uart_obs_permit i γ).
  { intros HRg GEN HFi ri i γ
      (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Ghist & Gcl & GT & Heq & Happ & Huart).
    refine (uart_obs_permit_ledger i (app_R A Gcl) (app_tag A Gcl)
              (app_cons A Gcl) γ (HRt Gcl)
              _ _ _ (Htx HRg GEN HFi Gcl ri i γ Happ Huart)
                    (Hrx HRg GEN HFi Gcl ri i γ Happ Huart));
      rewrite Heq; reflexivity. }
  exact (xv6_power_adequacy_gen Σ g sb nib cov
           (app_fixed A) (app_cl A) Hbirth
           (app_names A) (app_pred A) (app_boot A)
           (app_cons A) Hconst
           (app_turn A) Happ_boot Happ_init
           (app_tag A) Htagp Htagt
           (app_kill A) Hkillp Hkillt Happ_kill
           Happ_out_sup Hinit_boot
           Happ_echo
           (fun γobs c => obs_ledger_at (app_R A c) γobs)
           (fun γobs c =>
              obs_ledger_at_alloc_cl (app_R A c) γobs (app_cl A c) (HR0 c))
           (fun γd γobs c =>
              obs_ledger_at_step XV6_DISK_BYTES (app_R A c) (HRt c)
                (app_cons A c) (app_turn A c)
                (Hpow c) γd γobs)
           Hperm (app_phi A) Hphi Hgen0 Hpow0 Himg).
Qed.

(* ---------------------------------------------------------------------- *)
(* THE GENERIC APPLICATION PAYS EVERYTHING: the five obligations that       *)
(* mention its data, each in one line.  [xv6_trace_adequacy] is the record  *)
(* at these with a client's ledger in place of [emp].                       *)
(* ---------------------------------------------------------------------- *)
Section AppTriv.
  Context {Σ : gFunctors} `{!riscvGpreS Σ}.

  (* the birth step: no fixed part, so [()] and nothing about it *)
  Lemma app_triv_birth :
    ⊢ |==> ∃ c : app_fixed (app_triv Σ), app_cl (app_triv Σ) c.
  Proof.
    iModIntro. cbn [app_triv app_fixed app_cl].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  (* the transport: a predicate that holds of every view is its own copy,
     and the generic application hands its first process nothing *)
  Lemma app_triv_xfer (c : app_fixed (app_triv Σ)) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred (app_triv Σ) c) (app_boot (app_triv Σ) c k).
  Proof.
    cbn [app_triv app_pred app_boot].
    apply app_xfer_boot_raw_triv. intros r av. reflexivity.
  Qed.

  (* era 0: the claim at any view, at the one instance *)
  Lemma app_triv_init (c : app_fixed (app_triv Σ)) (av : aview) :
    ⊢ |==> ∃ r : app_names (app_triv Σ), app_pred (app_triv Σ) c r av.
  Proof.
    iModIntro. cbn [app_triv app_names app_pred].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  (* THE FIRST PROCESS'S EXEC BUNDLE: the generic application's predicate
     IS [True], so its supply is free ([AppInv.app_sup_raw_triv]) and the
     bundle is the trivial one over the generic mint
     ([SystemAdequacy.init_boot_of_triv]) -- every hop says yes, the
     observation hands the authority back, and both slot wands answer with
     the user-execution WP every key admits. *)
  (* the two classes the section does not carry: the bundle is an [iProp]
     over the kernel's ghost state, and its slot piece is [UexecRet.uslot],
     which reads the descriptor class *)
  Lemma app_triv_init_boot
      `{HX : !xv6G Σ, HU : !ufdG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (c : app_fixed (app_triv Σ)) (r : app_names (app_triv Σ)) :
    @file_app Σ HF
      = MkAppcfg (app_names (app_triv Σ)) (app_pred (app_triv Σ) c) r ->
    riscv_rx_tag = app_tag (app_triv Σ) c ->
    (* ...and the kill-credential equation (lane KILL-PAY, K1): the generic
       application's credential is [True], which is what pays
       [init_boot_of_triv]'s new side *)
    riscv_kill_cred = app_kill (app_triv Σ) c ->
    (* ...and the generation-counter equation (lane APP-IFACE (b')), which
       the generic application takes and does not use *)
    @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
    (* ...and the console-claim equation (redesign R2), which pays the
       other new side: the generic application's claim is [emp] *)
    @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = app_cons (app_triv Σ) c ->

    ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot (app_triv Σ) c (S gen_id) r -∗
      (* ...and the era's turn, likewise taken and not used *)
      app_turn (app_triv Σ) c (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof.
    intros Heq _ Hkc _ Hcons. iIntros "_ _ _". iModIntro.
    (* the rewrite goes BEFORE the [intros]: [r'] is typed at
       [app_names file_app], so rewriting under it is a dependent rewrite *)
    iApply init_boot_of_triv.
    - rewrite Heq. intros r' av.
      cbn [app_triv app_pred app_names]. reflexivity.
    - rewrite Hkc. cbn [app_triv app_kill]. reflexivity.
    - rewrite Hcons. cbn [app_triv app_cons]. reflexivity.
  Qed.

  Lemma app_triv_R0 (c : app_fixed (app_triv Σ)) :
    app_cl (app_triv Σ) c ⊢ |==> app_R (app_triv Σ) c [].
  Proof. iIntros "_". by iModIntro. Qed.
End AppTriv.

(* ---------------------------------------------------------------------- *)
(* THE ARBITRARY APPLICATION, CLOSED: at the real image, powered off,       *)
(* never booted, every run is reducible.  The application's conclusion is   *)
(* [True], so the statement says reducibility and nothing else -- and       *)
(* DELIBERATELY names no [Σ]: stated as [app_phi (app_triv xv6Σ) g2 κs] it  *)
(* would unfold through the record at the functor list and put the whole    *)
(* ghost layer (the camera classes [xv6Σ] names) into the STATEMENT's       *)
(* trusted base, ~500 lines nobody has to read for "every run is           *)
(* reducible" (tools/tcb; measured 2026-09-05).  Every obligation of the    *)
(* record is a line; the generic user-safety WP is what the boot mints, so  *)
(* user space does anything and the abstract state is anything.            *)
(* ---------------------------------------------------------------------- *)
Corollary xv6_app_adequacy_triv_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2.
Proof.
  intros n κs t2 g2 Hn.
  refine (proj1 (xv6_app_adequacy xv6Σ g fsimg_sb fsimg_nib fsimg_cov (app_triv xv6Σ)
           app_triv_birth
           ltac:(intros c h; cbn [app_triv app_R]; apply _)
           ltac:(intros c h; cbn [app_triv app_tag]; apply _)
           ltac:(intros c h; cbn [app_triv app_tag]; apply _)
           ltac:(intros c; cbn [app_triv app_kill]; apply _)
           ltac:(intros c; cbn [app_triv app_kill]; apply _)
           ltac:(intros c r; cbn [app_triv app_kill];
                 iIntros "_"; iModIntro; done)
           (* the console claim's timelessness, vacuous at the generic
              application's [emp] *)
           ltac:(intros c k h H; cbn [app_triv app_cons]; apply _)
           (* ONE LICENCE (redesign R2): the generic claim is [emp], so every
              event on it is free *)
           ltac:(intros c r; cbn [app_triv app_cons];
                 iIntros "_ !>" (k h H ev) "_"; by iModIntro)
           app_triv_R0
           ltac:(intros c h on dk _;
                 cbn [app_triv app_R app_cons app_turn];
                 iIntros "_"; iModIntro; iSplitR; [done |];
                 destruct on; by repeat iSplitR)
           ltac:(intros HR GEN HFi c r i γ _ _; cbn [app_triv app_R];
                 iIntros "!>" (h b u u' ho H)
                   "_ _ _ _ _ _ _ _ Ho Hg _"; iModIntro;
                 iFrame "Ho Hg"; done)
           ltac:(intros HR GEN HFi c r i γ _ _; cbn [app_triv app_R app_tag];
                 iIntros "!>" (h b u u') "_ _ _ Hg _"; iModIntro;
                 iFrame "Hg"; auto)
           app_triv_xfer
           ltac:(intros c; exact (app_triv_init c _))
           app_triv_init_boot
           (* the echo justifies itself at the trivial console claim *)
           ltac:(intros HR c Hcons _; iIntros (GEN XI);
                 iApply (SpecConsoleintr.cons_echo_shift_triv (XI := XI));
                 rewrite Hcons; cbn [app_triv app_cons]; reflexivity)
           ltac:(intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h;
                 iIntros "_ _ _ _ _"; iModIntro; iPureIntro; exact Logic.I)
           Hgen0 Hpow0 _ n κs t2 g2 Hn)).
  rewrite Hdisk. exact fsimg_image_wf.
Qed.
