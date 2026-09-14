# The trusted surface since 09-14 (688c4c1b7 -> origin/main 249b751c2)

Owner's review document, 2026-09-16.  Successor to
`trusted-surface-2026-09-14.md`, which was written at `688c4c1b7`.  Scope:
every TRUSTED-STATEMENT change the applications project landed on `main`
since -- the lanes SELF-KILL 4b'/P6/P6b/step 5, CONS-IO milestones D
(landed and then REVERTED), E and F, ECHO-OUT parts 1-5 with the part-4
addendum, TRAP-ROWS T1, FORK-REFUND and PROLOGUE-ALTS.  A TRUSTED STATEMENT
is the top theorem's statement and hypotheses, the pure predicates on the
run's trace that it is stated over, and the kernel-spec rows the program
proofs read.  Line numbers are of `249b751c2`.

WHAT THE THEOREM NOW SAYS, in plain terms.  At the real disk image, powered
off and never booted, every finite run of the machine is SAFE (no thread is
stuck), and: IF the console input kept the typing discipline throughout the
run, THEN in every power cycle everything that reached the console UART's
wire is a prefix of the session transcript that cycle's input calls for.
The transcript may now resolve some failures -- /init's "exec sh failed"
restart loop, its terminal "fork failed", and the shell's own `fork1` panic
followed by /init restarting it -- and the theorem is true under any of
them.  WHAT IT STILL ASSUMES: three Coq-level entailments about the SHELL's
program proof (`Hsh_owed`), the disk image facts, and thirteen ambient Coq
axioms (section 6).  `Hphi`, the last kernel/application gap, is CLOSED --
the application's own trace ledger now decides the conclusion.

## 1. THE THEOREM

`UInitBootAdequacy.echo_adequacy_modulo_phi` (iris/UInitBootAdequacy.v:98,
`Qed`), verbatim as of origin/main with comments elided:

```coq
  Theorem echo_adequacy_modulo_phi
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
         /\ (forall (c : app_fixed app_echo) (γp : gname)
                    (N : UkRun.uk_names Σ) (l : list FdSlots.fdstate),
               UkRun.ukn_pay N
                 = UserConsole.ucons_pay FsCfg.fsc_cons γp (echo_taint c) ->
               ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp
                   (echo_taint c) FsCfg.fsc_cons l))
      (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
      (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                sb nib cov)
      (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
      (Hsb : sb = fsimg_sb) (Hcov : cov = fsimg_cov) :
    forall (n : nat) (κs : list mobs) t2 g2,
      language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
        κs (t2, g2) ->
      (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
      /\ app_phi app_echo g2 κs.
```

| Hypothesis | 09-14 | 09-16 | What changed, and why |
|---|---|---|---|
| `Hphi` | present: a ~20-line entailment saying the application can read its conclusion off the power interpretation and the trace ledger, at a `boot_fixedGS` literal spelled out in full | **GONE** | ECHO-OUT part 5 (`cc76a5907`).  The trace LEDGER (`app_R`, echo's `EchoOut.echo_led`) now literally contains "the input was disciplined throughout, or the run is tainted", so `RiscvAdequacy.obs_ledger_at_phi` reads the conclusion out of it (`AppEcho.echo_Hphi_R` / `EchoOut.echo_led_phi`).  Nothing is assumed in its place. |
| `Hsh_owed` conjunct 1 | `⊢ UkSh.sh_deps (PS := uprogSG_free)` | unchanged, verbatim | sh's `write(16)` deposit law at the free program instance.  `sh_deps := udepw_law 16` (iris/UkSh.v:435) is textually identical. |
| `Hsh_owed` conjunct 2 | `⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh` | unchanged, verbatim | sh's tail (SH-LINE R2/R3) at the named resource family `sh_Rsh`. |
| `Hsh_owed` conjunct 3 | absent | **NEW** (quoted above) | ECHO-OUT part 5, ROUTE (B).  sh's console READ LEAF was discharged inside `UInitBoot.echo_Hinit_boot` out of the boundary's flat input licence `WpUart.in_licence` ("any process may append anything to the input log").  That licence is FALSE at echo's REAL input claim: `EchoOut.ein`'s two non-taint arms pin the delivered byte sequence and its count, so moving the delivered list needs the reader's half of `EchoOut.dl_cnt`, which only the taint arm gives away -- and sh's payload LEASE (`UserConsole.ucons_pay`) carries no taint.  `UShLine.ush_read_sup` and `ush_read_recv_leaf_holds` were DELETED and the leaf's statement moved here VERBATIM, owed by lane IO-LEAF. |
| `Hgen0`, `Hpow0`, `Himg`, `Hdk`, `Hsb`, `Hcov` | present | unchanged | facts about the starting state and the disk image. |

NET: the hypothesis list is one shorter (a big Iris entailment gone) and one
Coq-level program-proof premise longer.  Both moves are recorded as the
project's plan; neither weakens the conclusion.

## 2. THE PURE TRACE PREDICATES

### 2.1 `AppEcho.echo_phi` -- the conclusion

```coq
(* OLD, 09-14 (iris/AppEcho.v:1362) *)
Definition echo_phi : gstate -> list mobs -> Prop :=
  fun _ h => Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h).

(* NEW (iris/AppEcho.v:1377) *)
Definition echo_phi : gstate -> list mobs -> Prop :=
  fun _ h => disc h -> Forall good_out (cycles_of h).
```

The GUARD IS THE WHOLE RUN'S, not each power cycle's, per the owner's
ruling ("there's no per-cycle form -- once we get taint in one era, it's
tainted forever").  `cycles_of h` splits the run's observation trace into
one segment per power cycle, the open one last.  The per-cycle form was
unprovable and also unsound as a claim: a cycle whose input broke the
discipline licenses garbage, while a later input-free cycle satisfies
`disc_seg'` vacuously.  `AppEcho.echo_phi_disc` and
`EchoOutPure.echo_phi_of_good_out`, the two bridging lemmas, are DELETED.

### 2.2 `EchoDisc` -- the discipline and `good_out`

PROLOGUE-ALTS (`f5d63cbfa`+`d1b189277`+`833300de0`) admits, in the expected
transcript, three failures /init and sh can really produce.  The good run's
transcript is byte-for-byte unchanged.  A "prologue" is what the console
shows before a session's first prompt; a "resolution list" is a list of
small natural numbers naming which alternative each choice point took.

NEW, and there was nothing like them at 09-14:

```coq
Definition u_banner   : list (bv 8) := sb "init: starting sh"%string ++ nlb.   (* :235 *)
Definition pro_alts : list (list (bv 8)) := [ u_prompt; u_execfail; u_forkfail ]. (* :266 *)

Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=               (* :280 *)
  if decide (a = 1%nat) then t else [].
Fixpoint pro_of (ps : list nat) : list (bv 8) :=                               (* :282 *)
  match ps with
  | [] => u_banner
  | a :: ps' => u_banner ++ pro_alts !!! a ++ pro_more a (pro_of ps')
  end.
Definition pro_done (ps : list nat) : Prop := Exists (fun a => a <> 1%nat) ps. (* :288 *)

Definition pro_ok (ps cs : list nat) (q : nat) : Prop :=                       (* :789 *)
  Forall (fun a => (a < length pro_alts)%nat) ps
  /\ (pro_idx cs q < pro_rounds ps)%nat.
```

`pro_alts` is the three things the wire can show after each banner:
alternative 0 `"$ "` (sh runs, the session begins), alternative 1
`"init: exec sh failed\n"` (the child could not exec; it exits, /init reaps
it and the outer loop prints the banner AGAIN -- the ONLY alternative that
continues), alternative 2 `"init: fork failed\n"` (/init could not fork; it
exits and the kernel panics on the OTHER UART, so no process writes this
wire again).  `pro_of ps` is the prologue for a resolution `ps`: one banner
per round, then that round's alternative, recursing only while the choice is
1.  It is MONOTONE under append -- an unresolved `ps` owes only the banner
-- which is exactly what a writer's growing lower bound on `ps` is worth.
`pro_rounds` counts settled rounds, `pro_idx cs i` counts how many shells
died on their own fork panic before input line `i`, and `pro_ok ps cs q`
says every round the first `q` lines enter has settled.

`u_prologue` is UNCHANGED and keeps its name (`= pro_of [0]`).

CHANGED:

```coq
(* OLD, 09-14 (:250) *)
Definition line_alts : list (list (bv 8)) :=
  [ sb "hello world"%string ++ nlb ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ++ sb "init: starting sh"%string ++ nlb
      ++ sb "$ "%string ].

(* NEW (:594) *)
Definition line_alts : list (list (bv 8)) :=
  [ sb "hello world"%string ++ nlb ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ].
```

`line_alts !!! 3` -- what the wire shows when the shell's own `fork1`
panics -- HARD-CODED A SUCCESSFUL RESTART ("fork\ninit: starting sh\n$ ")
and was FALSE for exactly the reason the new prologue exists: /init's
restart can itself fail to exec or fork.  Alternative 3 is now the panic
line alone, and the transcript re-enters a fresh prologue block:

```coq
Definition alt_cont (ps cs : list nat) (i : nat) : list (bv 8) :=              (* :647 *)
  line_alts !!! (cs !!! i)
  ++ (if decide (cs !!! i = 3%nat)
      then pro_of (pro_from (S (pro_idx cs i)) ps) else []).
```
`pro_from r ps` drops `r` settled rounds, so the tail appended after a panic
is the prologue of the round that panic opened.

```coq
(* OLD (:285) *)  Definition sess_n (cs : list nat) (n : nat) : list (bv 8) :=
  u_prologue ++ alt_seq cs (n `div` length echo_line)
             ++ take (n `mod` length echo_line) echo_line.
(* NEW (:763) *)  Definition sess_n (ps cs : list nat) (n : nat) : list (bv 8) :=
  pro_of ps ++ alt_seq ps cs (n `div` length echo_line)
            ++ take (n `mod` length echo_line) echo_line.

(* OLD (:300) *)  Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists cs : list nat,
    Forall (fun c => c < length line_alts) cs /\ out `prefix_of` sess cs l.
(* NEW (:895) *)  Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok ps cs (length l `div` length echo_line)
    /\ Forall (fun c => c < length line_alts) cs
    /\ out `prefix_of` sess ps cs l.

(* OLD (:470/:478) *)
Definition disc_pt (cs : list nat) (i : nat) (p : list mobs) : Prop :=
  sess_n cs i `prefix_of` obs_wire Uart0 p.
Definition disc_seg' (seg : list mobs) : Prop :=
  disc_seg seg
  /\ exists cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p -> disc_pt cs i p.
(* NEW (:1092/:1104) *)
Definition disc_pt (ps cs : list nat) (i : nat) (p : list mobs) : Prop :=
  sess_n ps cs i `prefix_of` obs_wire Uart0 p.
Definition disc_seg' (seg : list mobs) : Prop :=
  disc_seg seg
  /\ exists ps cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p ->
            pro_ok ps cs (i `div` length echo_line) /\ disc_pt ps cs i p.
```

`pro_ok` is stated AT THE INPUT and not once per segment: a segment the
user never typed into enters no round, and quantifying it once made
`disc_seg' []` false.  UNCHANGED, verbatim: `disc_seg` (the input bytes are
a prefix of `(echo hello world\n)*`), `disc h := Forall disc_seg'
(cycles_of h)` (:1512), and

```coq
Definition good_out (seg : list mobs) : Prop :=                                (* :1673 *)
  expected_rel (ins seg) (obs_wire Uart0 seg).
```

whose meaning moved only through `expected_rel`.  The ten closure laws are
unchanged.  Prefix-freeness of the three prologue alternatives
(`pro_alts_prefix_det`, `pro_done_of_prefix`) replaces head-distinctness --
their first bytes are '$','i','i', not distinct -- while the LINE choice is
still pinned by one byte ('h','e','$','f').

WHAT RUNS ARE NOW ADMITTED THAT WERE NOT.  (1) /init failing to exec the
shell any number of times, each failure printing a banner and a diagnostic
before the session finally starts.  (2) /init failing to FORK, which is
terminal: /init exits, `kexit` panics on the kernel's own UART, and the
console wire is silent forever after (so, by the rate discipline, no further
input is admitted).  (3) The shell panicking in its own `fork1` after a
completed line, /init reaping it and starting a fresh round -- whose exec or
fork may fail exactly as round 0's may.  NOT admitted, and refuted rather
than allowed: "init: wait returned an error\n" (kernel row T4, section 5).

THE FOUR COMPUTED WITNESSES (`vm_compute`, closed, no assumptions) say the
discipline was not made vacuous and the claim not made trivial
(iris/EchoDisc.v:1461-1504 and :1684-1704):

| Witness | Trace | `disc_seg'` | `good_out` |
|---|---|---|---|
| `demo_seg` | the good prologue, then the first byte of "echo hello world\n" | `demo_disc_seg'` at `ps = [0]`, `cs = []` | `demo_good_out` |
| `demo_seg_exec` | `pro_of [1;0]` -- one exec failure, then the session | `demo_disc_seg'_exec` at `[1;0]`, `[]` | `demo_good_out_exec` |
| `demo_seg_fork` | `pro_of [2]` -- the terminal fork failure | `demo_disc_seg'_fork` at `[2]`, `[]` | `demo_good_out_fork` |
| `demo_seg_panic` | a whole line typed and echoed, sh's fork panic, /init's restart | `demo_disc_seg'_panic` at `[0;0]`, `[3]` | `demo_good_out_panic` |

## 3. THE APPLICATION RECORD

### 3.1 Two new fields: the era's turn and the echo window token

```coq
(* NEW, iris/App.v:225 and :236 *)
  app_turn  : app_fixed -> nat -> iProp Σ;
  app_win   : app_fixed -> nat -> iProp Σ;
```
`MkApp` now takes thirteen arguments (was eleven); `app_triv` fills both
with `fun _ _ => emp`.  Their machine-side counterpart is new too:

```coq
(* NEW, iris/RiscvPtsto.v:757 *)
  riscv_win_res : nat -> iProp Σ;
  riscv_win_res_timeless : forall k : nat, Timeless (riscv_win_res k);
```
with `win_res_triv` and a `Global Existing Instance`.

PLAIN READING.  `app_turn A c k` is the application's own per-power-cycle
credential -- "it is your turn to write on the console" -- minted once per
cycle and carried by the kernel to /init.  `app_win A c k`/`riscv_win_res k`
is a per-cycle EXCLUSIVE token the application LENDS the kernel; the kernel
parks it on the console interrupt's payload and hands it to the echo
obligation.  WHY IT EXISTS: `cons_echo_shift` is persistent (the kernel may
fire it any number of times) and the run it produces is split in two (store
the echoed byte, then file the log entry), so the application's spec has to
be total over interleavings the kernel actually forbids with `cons.lock` but
never states -- two echoes of one byte, an echo after the append, an append
twice.  Nothing pure refutes them.  The token is one linear thing per cycle:
the first firing stores its share where a second firing would have to find
it, and the append gives it back.

OWNER'S POSITION: **"ACCEPTED AS A WORKAROUND FOR THE TIME BEING"**
(2026-09-15, app-echo.md lane CONS-IO milestone F).  The post-Qed debt is
recorded as **POST-QED REDESIGN**: (a) restate the notion of an application
and the app-kernel interaction in terms of adequacy; (b) ONE I/O invariant
or resource in place of the split output/input claims and the lent window
token.  The owner's note: everything here is proof structure, not statement
-- the closed theorem mentions only the machine, the disk image and the pure
trace predicate.

### 3.2 `Hpow` -- the power step now founds the cycle

```coq
(* OLD, 09-14 *)
    (Hpow : forall (c : app_fixed A) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A c h ==∗
         app_R A c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list)

(* NEW, iris/App.v:386 *)
    (Hpow : forall (c : app_fixed A) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A c h ==∗
         app_R A c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
         (if on then emp
          else app_out A c (S (obs_boots h)) [] [] ∗
               app_in A c (S (obs_boots h)) [] [] [] ∗
               app_turn A c (S (obs_boots h)) ∗
               app_win A c (S (obs_boots h))))
```

WHY (CONS-IO milestone E, `a7f5e98a7`).  Until E the two console claims were
founded by the TRANSPORT, `Happ_boot`, and that was unsound as a discipline:
`app_xfer_boot_raw` is a `□` over a basic update that hands its own input
straight back, so "the claim at the empty run" was derivable UNBOUNDEDLY
from nothing and no ledger fact could refute a claim "reset" to the founded
arm.  The power-ON step is the one step of the machine that runs the
application's ledger and runs exactly ONCE PER CYCLE, so it is where a
linear per-cycle seed can be minted.  The cycle number is `S (obs_boots h)`
read off the PRE-event history, which `ObsTrace.obs_boots_app` makes the
boot count of the post-event history -- the number the kernel's own stamp
reads at every history of the new cycle.  Nothing is owed on the power-OFF
arm.  Consequently `Happ_boot` is back to two arguments:

```coq
    (Happ_boot : forall (c : app_fixed A) (k : nat),
       ⊢ app_xfer_boot_raw (app_pred A c) (app_boot A c k))
```
(09-14: four arguments, `... (app_out A c k) (app_in A c k)`).
`app_xfer_boot_raw_out`, the bridge for an application that founded from
nothing, is DELETED.  CONS-IO milestone D (a kernel-minted per-cycle
`era_tok` lent to /init) landed on 09-14 and was REVERTED whole in the same
commit as E; nothing unused stays.

One new class obligation: `(Hwint : forall (c : app_fixed A) (k : nat),
Timeless (app_win A c k))` (:341).

### 3.3 `Hinit_boot` -- the premise /init's boot is handed

```coq
(* NEW, iris/App.v:533; the two lines marked NEW are the change *)
         @riscv_in_res Σ (@riscv_fixedGS Σ HR) = app_in A c ->
         @riscv_win_res Σ (@riscv_fixedGS Σ HR) = app_win A c ->     (* NEW *)
         ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot A c (S gen_id) r -∗
           app_turn A c (S gen_id) -∗                                (* NEW *)
           |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0)
```

The equation is a FACT about the instance the theorem is taken at (the
`boot_fixedGS` literal fixes the field), not an assumption about the world.
The new resource premise is the cycle's turn, handed to a pinned /init and
spent by lane IO-LEAF at the cycle's first banner byte.  (The `era_tok`
premise that milestone D briefly added here is gone with D.)

### 3.4 `Happ_echo` -- the echo obligation

```coq
(* NEW, iris/App.v:606; one line added *)
    (Happ_echo :
       forall (HR : riscvGS Σ) (c : app_fixed A),
         @riscv_out_res Σ (@riscv_fixedGS Σ HR) = app_out A c ->
         @riscv_in_res Σ (@riscv_fixedGS Σ HR) = app_in A c ->
         @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = app_tag A c ->
         @riscv_win_res Σ (@riscv_fixedGS Σ HR) = app_win A c ->     (* NEW *)
         ⊢ ∀ (GEN : GenId) (XI : CurCtx),
             @SpecConsoleintr.cons_echo_shift Σ HR GEN XI)
```
matching the kernel row it is stated at:
```coq
(* iris/SpecConsoleintr.v:214; the [riscv_win_res] premise is NEW *)
  Definition cons_echo_shift `{XI : CurCtx} : iProp Σ :=
    (□ ∀ (h : list mobs) (c : bv 8) (cs : list (bv 8)) (Φ : iProp Σ),
        ⌜obs_ends_in Uart0 h c⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
        ⌜cons_echo c cs⌝ -∗
        riscv_rx_tag h -∗ obs_hist_lb h -∗ riscv_win_res (S gen_id) -∗
        Φ -∗ in_run (S gen_id) h c [] cs Φ)%I.
```
`Happ_echo` STAYS CLOSED: echo answers a firing out of a resource it owns.

### 3.5 The record's four claims stop being `emp`

At 09-14 `AppEcho.echo_out`/`echo_in` were the `emp` placeholders and every
console obligation was discharged vacuously.  ECHO-OUT parts 1-5 replaced
them: `echo_out := EchoOut.eout (echo_taint γ) γ`, `echo_in := EchoOut.ein
(echo_taint γ) γ`, `echo_turn := EchoOut.eturn γ`, `echo_win :=
EchoOut.ewin (echo_taint γ) γ`; `app_R` is `EchoOut.echo_led`, `app_tag` is
`EchoOut.etag`, and the fixed part is `EchoOut.echo_gn`.  The record's
statement did not move for this -- the field TYPES are unchanged -- but the
theorem's CONTENT did: the console obligations now have real claims to
preserve, and that is what pays `Hphi`'s removal.

## 4. THE KERNEL ROWS

### 4.1 TRAP-ROWS T1 -- the short console write says why (`6eafdaa54`)

The write side gets the twin of the read's swallow reason, one test weaker.
NEW pure predicate (iris/UserPtTree.v:361): `uva_rmapped P va` -- the
virtual address is mapped by page table `P` with the V (valid) and U (user)
bits set, which is exactly what `walkaddr` tests; `copyin` has no PTE_R
re-walk, so this is weaker than `uva_wmapped`.

```coq
(* NEW, iris/SpecCopyin.v:242 -- copyin's two exits in one predicate *)
Definition copyin_read (P : uptd) (M : gmap Z (bv 8)) (srcva : mword 64)
    (len : nat) (dst_new : nat -> bv 8) (res : mword 64) : Prop :=
  (res = (mword_of_int 0 : mword 64) /\ copyin_got M srcva len dst_new)
  \/ (res = (mword_of_int (-1) : mword 64)
      /\ exists d : nat, (d < len)%nat
           /\ ~ uva_rmapped P (uint (add_vec_int srcva (Z.of_nat d)))).
```
OLD: the post was the bare disjunction `⌜(a0 = 0 /\ copyin_got ...) \/ a0 =
-1⌝`.  `SpecEitherCopyin.either_copyin_post`'s user arm relays the same
existential, and `SpecConsolewrite`'s body gains (iris/SpecConsolewrite.v:284):

```coq
      ⌜(r < n)%Z ->
       exists d : nat, (r <= Z.of_nat d)%Z /\ (Z.of_nat d < n)%Z /\
         ~ uva_rmapped (pv_upt (us_V U))
             (uint (add_vec_int uaddr (Z.of_nat d)))⌝ -∗
```

```coq
(* NEW, iris/SpecFilewrite.v:692 *)
  Definition write_cons_short (P : uptd) (ua : mword 64) (k : nat) (n : Z) : Prop :=
    exists d : nat, (Z.of_nat k <= Z.of_nat d)%Z /\ (Z.of_nat d < n)%Z /\
      ~ uva_rmapped P (uint (add_vec_int ua (Z.of_nat d))).

  Definition write_cons_arms (P : uptd) (ua : mword 64) (Q : nat -> iProp Σ)
      (n : Z) (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝ ∗ Q (Z.to_nat n))
     ∨ (∃ k : nat, ⌜r = (mword_of_int (Z.of_nat k) : mword 64)⌝ ∗
                   ⌜Z.of_nat k < n⌝ ∗ ⌜write_cons_short P ua k n⌝ ∗ Q k)
     ∨ ⌜r = (mword_of_int (-1) : mword 64) /\ n < 0⌝)%I.
```
(OLD: no `P`/`ua` parameters, and the middle arm was `⌜Z.of_nat k < n⌝ ∗
Q k` with no reason.)  `filewrite_extra` and `filewrite_arms` gained `P` as
the read side already had it; `filewrite_in` did NOT (a deposit says nothing
about the answer).  PLAIN READING: consolewrite's loop has exactly ONE
break, `either_copyin(...) == -1`, so a count below the request means some
byte at or after the cursor and before the end of the request sits on a page
the kernel could not read through the writer's own page table.  THE OFFSET
IS EXISTENTIAL and cannot be the cursor: the chunk the break fired in is up
to 32 bytes and `copyin` walks it a page at a time.  ONE cause for the short
exit; a non-lazy process that owns its whole buffer refutes the arm from its
own permission map.

Row 16 of `UexecExecInst.xv6_sbundle` (the console write row the program
proofs read) becomes row 5's twin (iris/UexecExecInst.v:718):

```coq
       (∃ P : uptd,
          ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
          ⌜ProcPtOwn.proc_pt_wf P⌝ ∗
          ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
          filewrite_extra P (fd_st_of_key (xk_a W 0) (uvis_fd W))
            (sys_rw_count (xk_a W 2)) (uvis_M W) (xk_a W 1)
            (wf_Q f) r)
```
(OLD: `filewrite_extra (fd_st_of_key ...) ... (wf_Q f) r`, no table.)  The
key carries no page table, only the permission map it projects to, so the
table is existential at that projection, exhibited with the same
well-formedness and non-lazy claims the read row already uses.

### 4.2 FORK-REFUND -- a fork that creates no child gives back the lend (`e58f284a2`)

`Rc`, the resource a forking process LENDS its child to run with (as opposed
to what the child's exit owes back), becomes a FIELD of the process family:

```coq
(* NEW, iris/UexecSG.v (class uexecSG) *)
  sfork_lend : sfam -> iProp Σ;
  sfam_pay : (Z -> iProp Σ) -> iProp Σ -> sfam;                   (* OLD: (Z -> iProp Σ) -> sfam *)
  sfork_pay_pay : forall (Q : Z -> iProp Σ) (Rc : iProp Σ),
    sfork_pay (sfam_pay Q Rc) = Q;
  sfork_lend_pay : forall (Q : Z -> iProp Σ) (Rc : iProp Σ),
    sfork_lend (sfam_pay Q Rc) = Rc;
  sfork_lend_pt : sfork_lend sfam_pt = emp%I;
  sfork_lend_at : forall (Q : Z -> iProp Σ) (f : sfam),
    sfork_lend (sfam_at Q f) = sfork_lend f;
```

WHY A FIELD.  The lend goes DOWN on fork's deposit (the child's leg spends
it) and comes BACK on fork's arm (the failing leg refunds it), and
`uexec_ret_F_split` tears those two apart and carries them past each other
through the whole kernel excursion.  `f` is the one value both legs carry,
so only `f` can make the resource that went down and the one that comes back
the same resource.  A generic process lends `emp`.

```coq
(* NEW, iris/UexecRet.v:983 -- the -1 arm regained [Rc] *)
  Definition ufork_ans (Q : Z -> iProp Σ) (Rc : iProp Σ) (r : mword 64)
      (cs cs' : gset gname) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64) /\ cs' = cs⌝ ∗ Rc)
     ∨ ∃ (γ : gname) (pidv : mword 32),
         ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
         ⌜cs' = cs ∪ {[γ]}⌝ ∗
         child_tok γ pidv Q)%I.
```
(OLD: the -1 arm was the pure fact alone.)  `uexec_fork_child_F` now carries
the lend beside the child's continuation -- `□ (riscv_kill_cred -∗ Q (-1)) ∗
Rc ∗ ∀ g' pidc, my_pay g' Q -∗ Rc -∗ X (...)` -- the only shape the kernel
can refund from without building a child.  `SpecKfork.kfork_post` and
`SpecSysFork` take `Rc` as a plain parameter (neither reads it): `kfork`
feeds it to the slot wand on the success path and returns it on the -1 arm,
where `allocproc` found no slot or `uvmcopy` failed and `freeproc` undid the
slot, so no child ever ran.  `UkFork.wp_uk_ecall_fork`'s -1 arm is now
`(⌜r = -1⌝ ∗ UserChildren.uch (ukn_ch N) Sc ∗ Rc)`.  WHY IT MATTERS: /init's
"init: fork failed" and sh's "fork" are printed on exactly the console
credential the parent lends, so a parent that could not get it back could
not report the failure.  No consumer exists yet; IO-LEAF threads it.

### 4.3 SELF-KILL P6b and step 5 -- who pays for a death

THE PAYMENT SHAPES.  The old design charged every kill to a single
persistent application-wide credential.  The new one charges it to the
TARGET's own exit payload at -1.

```coq
(* OLD, iris/SchedCtx.v *)
  Definition kill_paid (kl : mword 32) : iProp Σ :=
    (⌜kl = (mword_of_int 0 : mword 32)⌝ ∨ □ riscv_kill_cred)%I.

(* NEW, iris/SchedCtx.v *)
  Definition kill_row (gn : gname) (kl : mword 32) : iProp Σ :=
    ((⌜kl = (mword_of_int 0 : mword 32)⌝ ∗ ChildTok.kill_pend gn)
     ∨ (ChildTok.kill_shot gn ∗
        (ChildTok.kill_owed gn ∨ ChildTok.taken_at gn)))%I.

  Definition kill_paid (pid : mword 32) (kl : mword 32) : iProp Σ :=
    ((⌜bv_unsigned pid = 0⌝ ∗ kill_free kl)
     ∨ (⌜bv_unsigned pid <> 0⌝ ∗
        ∃ (gn : gname) (Q : Z -> iProp Σ),
          pid_reg pid (DfracOwn qeighth) gn ∗
          ChildTok.my_pay gn Q ∗ □ (riscv_kill_cred -∗ Q (-1)) ∗
          kill_row gn kl))%I.
```
PLAIN READING.  A live process slot's `p->killed` row now says: the flag is
zero and no kill has been fired, OR the kill one-shot has fired and the
payment is either still owed (deposited by the killer, waiting for `kexit`)
or already taken.  The row also PUBLISHES a wand from the application's
taint to the target's exit payload at -1, so a third-party killer holding
only the taint can still pay.  `kill_shot gn` is persistent and monotone:
once set, the flag never reads zero again.

```coq
(* OLD, iris/UexecRet.v:1402 *)
  Definition ukill_cred_at (sc : mword 64) : iProp Σ :=
    (if decide (ukill_sc sc) then □ riscv_kill_cred else emp)%I.
(* NEW, iris/UexecRet.v:1440 *)
  Definition ukill_cred_at (gn : gname) (sc : mword 64) : iProp Σ :=
    (if decide (ukill_sc sc)
     then (□ riscv_kill_cred ∨ ChildTok.kill_owed gn) else emp)%I.
```
The deposit at a cause `usertrap` kills at is TWO-SIDED and indexed by the
trapping incarnation: a process may be entitled to the death either by the
application's taint (the generic route) or by depositing its OWN exit
payload -- which is what a verified program that faults ON PURPOSE does.

The -1 WAND leaves the trap route entirely (P6b, `d03988128`+`a33bf1a3d`):
`upay_neg` and the whole -1-wand vocabulary are GONE from the tree (15
removals), and

```coq
(* OLD *)  Definition uexec_kill_arm_F (X : uvis -d> iPropO Σ) (sc : mword 64)
      (W : uvis) (f : sfam) : iProp Σ :=
    ((uexec_pay_arm f -∗ X W)
     ∨ (⌜ukill_sc sc⌝ ∗ ((uexec_pay_arm f -∗ X W) ∧ sexit_pay f (-1))))%I.
(* NEW *)  Definition uexec_kill_arm_F (X : uvis -d> iPropO Σ) (sc : mword 64)
      (W : uvis) (f : sfam) : iProp Σ := (X W)%I.

(* OLD *)  ... then sexit_pay f (exit_xs tf) ∧ upay_neg (sexit_pay f)
           else upay_neg (sexit_pay f) ... else upay_neg (sexit_pay f)
(* NEW, upay_at (iris/UexecRet.v) *)
  Definition upay_at (gn : gname) (sc : mword 64) (tf : list (mword 64))
      (f : sfam) : iProp Σ :=
    (my_pay gn (sexit_pay f) ∗
     (if decide (sc = uecall_scause) then
        if decide (usys_num tf = USYS_exit)
        then sexit_pay f (exit_xs tf)
        else emp
      else emp))%I.
```
Nothing about the kill status travels the trap route any more; the process's
entitlement lives in the DEPOSIT (`ukill_cred_at`), and the resume arm is the
slot alone.  The kernel never resumes a non-lazy process from a killing trap.

The two writers of the flag change accordingly.  `SpecSetkilled` takes
either payment -- `(□ riscv_kill_cred ∨ ChildTok.kill_owed gn) -∗` -- plus
the caller's lent registration eighth and its lent quarter of `p->pid`
(which show the slot being written is LIVE, since the free arm of
`kill_paid` claims the flag is zero), and RETURNS both plus the fired
one-shot `ChildTok.kill_shot gn`.  (OLD: `□ riscv_kill_cred -∗` and an
empty postcondition.)  `SpecKkill`/`SpecSysKill` keep the taint.
`SpecKexit`'s payment premise becomes a disjunction:

```coq
(* OLD *)  Q (kexit_status m) -∗
(* NEW *)  (Q (kexit_status m)
            ∨ (⌜kexit_status m = -1⌝ ∗ ChildTok.kill_shot (pv_gen (us_V U)))) -∗
```
A process the kernel is tearing down at `exit(-1)` holds no `Q (-1)`: its
program never ran again, and what it owes its parent was deposited by
whoever killed it.  `kexit` is the one party that can take it.
`SpecKilled`'s postcondition is now caller-chosen: the call takes a read-only
accessor `(∀ pidr klr, p_pid ... -∗ SchedCtx.kill_paid pidr klr -∗ p_pid ...
∗ SchedCtx.kill_paid pidr klr ∗ Rout klr)` and returns `Rout kl` (OLD: the
fixed row `(⌜kl = 0⌝ ∨ □ riscv_kill_cred)`), because the useful fact beside
the flag is indexed by a GENERATION and `p->lock`'s payload names the
generation only existentially -- so the identification is the caller's.

THE DENIED-STORE LEAF (step 5, `b41a0075f`).  A new engine leaf for a fault
taken ON PURPOSE (iris/UkStore.v):

```coq
  Definition uk_store_denied (va : mword 64) : Prop :=
    exists q : uperm, uperm_at π va = Some q /\ up_W q = false.

  Lemma wp_uk_store_denied ... :
    ... uk_store_denied va -> ... ->
    (⊢ (Qp (-1) : iProp Σ)) ->
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv false M m pc -∗
    ChildTok.my_pay gn Qp -∗
    WP (Loop : expr riscv_lang).
```
The deposit's kill row is the RIGHT side of `ukill_cred_at` (the process's
own payload) and the resume slot beside it is the engine's Löb hypothesis,
so the leaf has NO continuation -- the process dies here.  Those two are
ADDITIVE, so the price is the Coq-level `(⊢ Qp (-1))`, free at a trivial
payload.  A new pure predicate names the other disposition:

```coq
Definition uk_store_retires (pt : uptd) (M : gmap Z (bv 8)) (va : mword 64)
    (kk : Z) : Prop :=
  exists w_st : mword 64,
    ud_um pt !! svpn_of va = Some w_st /\ uleaf_ok (Store Data) w_st /\
    ~ uva_text pt (uint va) /\
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb).
```
`uk_store_obl_base`/`_rvc` now guard their RETIRING continuation by it,
which the denied leaf refutes.  `uk_store_fault_post_fetch`'s kill premise
is two-sided for the same reason `ukill_cred_at` is.

WHAT THIS BOUGHT.  `UkShMalloc.ushm_sbrk_never_fails` -- "the 64 KiB `sbrk`
that `morecore` issues succeeds" -- is DELETED, and with it the `Hsbrk`
premise it rode on out of `UkShMain` (1 signature), `UkShFork` (4) and
`UkShEcho` (2).  It existed because sh's constructors do not test `malloc`:
`execcmd` goes straight into `memset(cmd, 0, 168)`, so a NULL return is a
FAULT in the shell rather than a branch.  The malloc contract now HAS a
failure arm, and the walk (`UkShParseLex.wp_kshp_execcmd` -> `memset`'s
prologue -> `UkSh.wp_ksh_memset_null`) reaches the store that dies.  THE SH
LANE'S LAST MEMORY ASSUMPTION IS GONE: the theorem now says what really
happens when the kernel is out of pages.

What the three parser files carry instead is one section hypothesis each
(iris/UkShParseLex.v:173, UkShParseExec.v:121, UkShParseCmd.v:123):

```coq
  Hypothesis ushp_pay_free : (⊢ ukn_pay N (-1)).
```
A Coq-level premise rather than a resource, and FREE at the record of every
process that runs this code: `execcmd` is reached only from `parsecmd`, and
only sh's FORKED CHILD parses, at a trivial payload
(`UkRun.ukn_pay_free_of_triv`).  These are discharged everywhere they are
instantiated; nothing reaches the top theorem.  `UkShRun`'s three
`(⊢ ukn_pay N (-1))` premises are KILL-PAY K4(a)'s and stay.

`UkSh.sh_deps := udepw_law 16` is UNCHANGED, verbatim.

## 5. WHAT IS IN FLIGHT AND WILL CHANGE TRUSTED STATEMENTS NEXT

All three below are PLANNED, not landed; nothing in them is on `main`.

**TRAP-ROWS M2** (kernel; `-tlw`, `lane/trap-rows`; T2+T3+T4 in one
milestone).  T2: the console READ's -1 exit gets a reason.  At the console
key there are two causes -- `fileread`'s own `n < 0` guard and
`consoleread`'s `killed()` test -- so the arm will carry the persistent
disjunction "the requested count was negative, OR this incarnation's kill
flag is set" (`⌜n < 0⌝ ∨ kill_shot gn`).  Per the owner's ruling of
2026-09-16 ("agreed with fixing the console read spec to never return -1 to
userspace") the killed case never reaches user mode: `usertrap`'s second
`if(killed(p)) exit(-1)` after `syscall()` exits the process before the
`sret`, so a new pure row on `usertrap_post` will say that a read at an open
readable console descriptor with a non-negative count returns something
other than -1, and the surviving user-visible cause is `n < 0` alone.  T3:
the deposit at a killing-cause trap becomes an ADDITIVE PAIR,
`ut_kill_in := ukill_cred_at ∧ uslot W` -- the process supplies either the
death payment or the resume slot, not both -- with a new `ut_kill_out` row
returning the untaken slot.  This is what a deliberate fault at a LINEAR
payload needs (step 5's leaf only works at a free one).  T4: `wait`'s -1 arm
gets a reason, `⌜rv = -1 /\ cs' = cs⌝ ∗ (⌜cs = ∅⌝ ∨ kill_shot gn)`,
conditioned on a null status pointer (every `wait` leaf in the tree forces
`a1 = 0`); the U-tier post keeps "`r = -1` implies the caller has no
children", which /init refutes from the shell's generation in its own child
set.  That is what turns "init: wait returned an error\n" into a REFUTED
arm rather than a fourth prologue alternative.

**PROLOGUE-ALTS-2** (application; `-sup`, `lane/prologue-alts-2`).  Three
things PROLOGUE-ALTS left owed on the application's claim, not on the pure
predicates: `ps_len_ok` in `eout_pure` (the current round is settled exactly
when the writer has written past the banner -- the twin of the landed
`cs_len_ok`), `echo_write_link_pro` (the link that resolves the prologue
choice at byte 19 of ANY round, with the round-opening premise `n0 = 0 ∨
cs0 !!! (n0/17-1) = 3`), and an arbitrary-round banner lemma.  These are
claim-internal; the discipline and `good_out` as landed do not move again.

**IO-LEAF** (programs; main checkout, `lane/io-leaf`; M1 launched
2026-09-16).  The programs start paying the console links they have so far
been given for free.  M1 is /init's banner, ROUND 0 only, through the chain
write leaf, with a new `EchoLinks.v` packaging the three link laws as ONE
persistent law in `sh_deps`' mould.  M2-M6 follow TRAP-ROWS M2 and
PROLOGUE-ALTS-2: echo's writes, the transport, sh's prompt and diagnostics,
then the READ LEAF -- which is what discharges `Hsh_owed`'s third conjunct
and takes the top theorem's owed list down to `sh_pay_rest` alone.  Along
the way the `_any` fork/wait wrappers are deleted and 14 signatures step 5
touched take a LINEAR payload, which is why T3 has to land first.

## 6. AUDIT

`make audit-only` (`SystemAssumptions.v`) reports THIRTEEN assumptions, and
the number and the list are UNCHANGED by every lane in this range -- each
landing note records "audit the thirteen".  They are:

```
PrimInt63.sub : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimString.string : Set
xv6iris_extras.resv_matches : forall n : BinNums.Z, Values.mword n -> bool
xv6iris_extras.resv_is_valid : bool
PrimInt63.lsr : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lsl : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lor : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.land : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.int : Set
PrimString.get : PrimString.string -> PrimInt63.int -> PrimString.char63
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
PrimInt63.eqb : PrimInt63.int -> PrimInt63.int -> bool
PrimString.cat : PrimString.string -> PrimString.string -> PrimString.string
```

Nine are Rocq's own primitive-integer and primitive-string operations, one
is functional extensionality, and two (`resv_matches`, `resv_is_valid`) are
the Sail model's load-reserved/store-conditional reservation hooks.  Nothing
in this range added, removed or changed one.  (Not re-run for this document,
per instruction; taken from the landing notes and the last recorded output.)
