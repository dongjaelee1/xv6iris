# The trusted surface as of main 7da574e81 (step 4 landed) -- REFRESH

Owner's review document, 2026-09-14 (third session).  Successor to
`trusted-surface-2026-09-16b.md` (written at `5c48c3aa2`), which extended
`trusted-surface-2026-09-16.md` (at `249b751c2`), which succeeded
`trusted-surface-2026-09-14.md` (at `688c4c1b7`).  Unlike the addendum, this
one is written to stand ALONE: it restates the theorem, every hypothesis, the
trace predicate, the audit, and what is computed versus assumed, and then
records the changes since `5c48c3aa2`.  Line numbers are of `7da574e81`
(`origin/main` is `81107fe83`, a notes-only commit on top; `git diff
7da574e81 81107fe83 -- iris` is empty).  Read-only: nothing was built or run
for this document; every "the audit prints" claim is taken from the landing
notes and the gate lines they record, and is marked as such.

A TRUSTED STATEMENT is, as in the predecessors, the top theorem's statement
and hypotheses, the pure predicates on the run's trace it is stated over, and
the kernel-spec rows and program-tier obligations the program proofs are
stated against.  Every term of art is defined where it first appears.

WHAT CHANGED SINCE THE ADDENDUM, IN ONE PARAGRAPH.  The theorem's hypothesis
list is ONE SHORTER: `Hsh_owed`'s third conjunct -- sh's console READ LEAF --
is gone (M5b, `32d7b6bbf`), discharged inside the proof.  Two conjuncts
remain, both about the shell's program proof: the free write law `sh_deps`
and the tail `sh_pay_rest sh_Rsh`.  The CONCLUSION changed once, by
PROLOGUE-ALTS-3 (`e4f254e70`): init's banner is now a LETTER of the prologue
rather than its fixed prefix, so a power cycle whose init could not open the
console -- and prints nothing -- is admitted, and with it a known widening
the owner has accepted for now (section 3.4).  Behind the two remaining
conjuncts, five lanes (M5(3), M6a(2)/(3), step 3, M6b, step 4) restated the
boot bundle `init_boot_pay` four times and the tail obligation `sh_pay_rest`
three times, deleted the round-0-only prompt machinery (`sh_prompt_*`,
`ush_prompt_in`, `kinit_round0`) and init's unpayable "wait returned an
error" arm (`die_dw`), and left exactly THREE affine `∨ True` arms in the
program tier, each named with its killer (section 7).  The audit of the
system theorem is unchanged at thirteen (section 4).

## 1. THE THEOREM

`UInitBootAdequacy.echo_adequacy_modulo_phi` (iris/UInitBootAdequacy.v:98-161,
`Qed` at :274), verbatim with comments elided:

```coq
  Theorem echo_adequacy_modulo_phi
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh))
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

The section binds the ghost-state PRE-classes only (:87-93); the proof is
`App.xv6_app_adequacy` (iris/App.v:272) applied at the echo record
`AppEcho.app_echo` (iris/AppEcho.v:1430) with every record obligation
discharged as a hole (:197-273), the one owed by the arc being `Hinit_boot`,
whose discharge `UInitBoot.echo_Hinit_boot` (iris/UInitBoot.v:589) takes
`Hsh_owed`'s two conjuncts as Coq premises (:599-600, applied at :254-255).

### 1.1 In plain words

THE MACHINE.  `g : gstate` is a whole machine state -- every hart's
registers, memory, the three devices (a 16550 UART on each of two ports, the
PLIC, the virtio disk) and the power state.  `PowerLoopE` (iris/RiscvLang.v:770)
is the one initial thread: the ghost POWER THREAD, whose steps turn the
machine on (spawning every hart's and device's thread at the reset vector)
and off.  `language.nsteps n (...) κs (t2, g2)` is Iris's step relation with
the observations kept: after `n` steps of ANY interleaving, the thread pool
is `t2`, the state is `g2`, and `κs : list mobs` is the sequence of
OBSERVATIONS the run emitted -- `ObsUartOut i b` when port `i` put byte `b`
on its transmit wire, `ObsUartIn i b` when port `i` accepted byte `b` from
the environment, `ObsPowerOff`/`ObsPowerOn` at the power arms
(iris/RiscvLang.v:471; design/adequacy.md:11).  So the theorem quantifies
over every finite run from `g`, with every scheduling and every input the
environment could push.

WHAT IT ASSUMES OF `g`: the machine is powered OFF (`Hpow0`) at generation 0
(`Hgen0`; a GENERATION is one power cycle's number), and the disk is the
mkfs image: its blocks are `fsimg_P` (`Hdk`; iris/FsImgDisk.v:75, the literal
2,048,000-byte image read as blocks), its superblock is the parsed `fsimg_sb`
(`Hsb`; iris/FsImgCheck.v:126), the block coverage is `fsimg_cov` (`Hcov`;
iris/SystemAdequacy.v:2128 -- blocks 1..1999), and the image is well-formed
in the sense `fs_boot_image_wf` states (`Himg`; iris/FsCfgBoot.v:585-595:
`fsimg_wf` and `fs_region_wf` hold, the inode region is exactly one block
run, the coverage is within the disk).  Section 5 says which of these are
COMPUTED facts about the tracked image and why they are nevertheless
hypotheses here.

"EVERY THREAD STAYS REDUCIBLE".  `language.reducible e2 g2` says the
thread `e2` can take a step in `g2`.  The conjunct says no thread of any
reachable pool is STUCK -- a stuck thread would be a hart whose next
instruction the model defines no step for (the Sail model's own `assert`
failing, an unmodelled instruction, a device step with no rule).  This is
SAFETY in the Iris sense; it is what every WP proof in the tree buys, and it
is unconditional: no discipline on the input is needed for it.

"THE UART WIRE IN EVERY POWER CYCLE IS A PREFIX OF AN ADMITTED TRANSCRIPT".
`app_phi app_echo g2 κs` is `AppEcho.echo_phi` (iris/AppEcho.v:1377):

```coq
Definition echo_phi : gstate -> list mobs -> Prop :=
  fun _ h => disc h -> Forall good_out (cycles_of h).
```

`cycles_of h` (iris/ObsTrace.v:564) splits the run's observations into one
segment per POWER CYCLE (the stretch between an `ObsPowerOn` and the next
`ObsPowerOff`, the open one last).  `disc h` (iris/EchoDisc.v:1799) is the
INPUT DISCIPLINE over the whole run: in every cycle the user typed only a
prefix of `(echo hello world\n)*` and typed each byte only after the echo of
the previous one was on the wire (section 3).  `good_out seg`
(iris/EchoDisc.v:1960) is the CLAIM: the bytes the CONSOLE UART (`Uart0`) put
on its wire during that cycle -- `obs_wire Uart0 seg` (iris/ObsTrace.v:53),
the `ObsUartOut Uart0` bytes in order -- are a PREFIX of the transcript the
cycle's input calls for, under SOME resolution of the choice points the
transcript admits (`expected_rel`, section 3).  Read together: IF the
console input kept the discipline throughout the run, THEN in every power
cycle everything the console showed is a prefix of an admitted session
transcript.  The guard is the WHOLE RUN's, not per cycle: once the input
breaks the discipline in one cycle nothing is claimed of any later cycle
(owner's ruling of 2026-09-14, "once tainted, tainted forever";
trusted-surface-2026-09-16.md §2.1).  Nothing is claimed about the kernel's
own port (`Uart1`), where `panic` and the boot messages go.

"MODULO PHI".  The name is historical.  Until ECHO-OUT part 5 the theorem
took `Hphi`, an Iris entailment saying the application could read its
conclusion off the trace ledger; that hypothesis is GONE (the file's own
note, :95-97 and :260-270: the conclusion is read off the application's
ledger by `AppEcho.echo_Hphi_R` through `RiscvAdequacy.obs_ledger_at_phi`).
What the theorem is still MODULO is `Hsh_owed`: two Coq-level entailments
about the SHELL's program proof, section 2.  Nothing else is owed.

## 2. EVERY HYPOTHESIS, VERBATIM, WITH ITS STATUS

### 2.1 `Hsh_owed` -- what the arc still owes on the shell's side

```coq
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh))
```
(iris/UInitBootAdequacy.v:123-140.)

THE BINDERS.  `HR : riscvGS Σ` is the ERA's Iris ghost-state instance (the
names of every ghost resource of one power cycle -- born by the boot mint,
which is why the hypothesis is quantified over them rather than taken at
one, :108-110), `GEN : GenId` the era's generation number, and the six
classes the file-system, descriptor, inode-reference, process-availability,
wait-channel and file ghosts.  `PS := uprogSG_free` (iris/UexecExecInst.v) is
the FREE PROGRAM INSTANCE: the process family in which every system call
whose deposit is `emp` is free and every other one is paid at its site --
the instance a VERIFIED program runs at (a generic, unverified program runs
at `uprogSG_gen`, on the application's supply).  Two conjuncts, Coq-level
and not one Iris conjunction, because `echo_Hinit_boot` takes each as a Coq
premise (:126-133).

#### Conjunct 1 -- `⊢ UkSh.sh_deps (PS := uprogSG_free)`, the free write law

```coq
  Definition sh_deps : iProp Σ := udepw_law 16.
```
(iris/UkSh.v:666.)

PLAIN READING.  A DEPOSIT is the Iris resource a process must hand the
kernel at an `ecall` to be allowed to make that system call; `udepw_law 16`
(iris/UkRun.v:467) is a persistent law producing the deposit for system-call
number 16, `write`, at any descriptor and any buffer.  At the console the
write deposit is the chain of OUT-LINKS -- one `WpUart.out_link` per byte,
the application's permission for that byte to reach the wire while its
transcript claim is preserved (trusted-surface-2026-09-14.md §2.6.3, §2.6.5).
So the conjunct says: "the shell may write anything to the console for free,
without the era's console credential".  The endgame audit records the four
leaves that actually spend it -- `UkSh.ksh_w_of_law` (iris/UkSh.v:1461),
`UkShDiag.ksh_w1_of_law` (iris/UkShDiag.v:460), `UkInit.kinit_w1_of_law`
(iris/UkInit.v:1311) and the prompt's fallback (endgame-audit.md §1) -- and
that init's own free law `UkInit.init_deps T := udepw_law 16 ∗ □ (T -∗
udepw_law 15) ∗ □ (T -∗ udepw_law 17)` (iris/UkInit.v:585-586) is built from
it at iris/UInitBoot.v:710 (`init_deps_of_laws`).  The two application sites
of the premise are iris/UInitBoot.v:712 and :905.

STATUS: OWED, and the plan is to make it UNNECESSARY, not to prove it.  No
proof of `⊢ udepw_law 16` at `uprogSG_free` exists in the tree; the only
mint of a free console write in the development is the application's SUPPLY
`app_sup`, which at echo is the TAINT `echo_taint` (iris/AppEcho.v:206 -- the
persistent fact "the input has broken the discipline"; UInitBoot.v's
`init_deps_of_sup` builds init's law from it under the taint).  The RESIDUALS
brief's own words: "a placeholder that counts a console write as paid
without the era's credential".  WHAT STILL SPENDS IT after step 4 and M6b,
by name (step4-sh-report.md §5; m6b-init-report.md "Spenders of udepw_law
16"): on the shell side, the prompt on `ush_wcp`'s affine arm
(`UkSh.ksh_w_of_wcp`, iris/UkSh.v:1614), getcmd's taint arm, the fork's PID
sub-arm (`sign_extend' 64 pidv = -1`) and its affine/taint arm running the
GENERIC child (`UkShMain.wp_kshm_child_alloc`, iris/UkShMain.v:692), the
generic runner's arms (`UkShRun.wp_kshr_fork1_any`, iris/UkShRun.v:1944, and
`ush_diag_leaf`), every `ksh_w1_of_law` site inside the generic diagnostics,
and the entry's hand-off; on the init side, the closed-ledger and affine arms
of `die_de`/`die_df` and the banner (`kinit_w1_of_law`), and the generic echo
entry `UShEcho.echo_slot_of_kexec_holds` (iris/UShEcho.v:1205).  WHO DELETES
IT: lane RESIDUALS (running now, in `-disc`; brief-residuals.md): (A) refute
the PID sub-arm from the fork leaf's pid-range row, (B) thread the exec-seam
rows (`uvis_ch W' = ∅`, `uvis_pid W' = pidv`) so the wait re-entry identifies
the reaped child, (C) kill the three affine arms of section 7, (D) restate
the shell's remaining need as `□ (T -∗ sh_deps)` -- free only under the
taint, derived at the top from `app_sup` exactly as init's law is -- and
DELETE this conjunct from `Hsh_owed` and from `echo_Hinit_boot`.  That
deletion changes the theorem's text and, per the brief, the audit line count
of the system theorem may not move (the echo theorem is not audited; section
4).

#### Conjunct 2 -- `⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh`, the shell's tail

```coq
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ)
       (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
       (Pm : nat -> iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T Wc Wb Pm
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.
```
(iris/UInitSh.v:524-531.)

```coq
  Definition sh_Rsh : gname -> gname -> gname -> iProp Σ :=
    fun _ γd γs => (UkShLoop.ushl_dat γd ∗ usz γs (kexec_sz ElfUser.sh_elf))%I.
```
(iris/UInitSh.v:646-647.)

The obligation it quantifies, `UkSh.ush_rest_l` (iris/UkSh.v:6810-6836),
verbatim:

```coq
  Definition ush_rest_l (R : iProp Σ) : iProp Σ :=
    (□ (∀ (l : list fdstate),
        ⌜ ukn_const N ⌝ -∗
        ⌜ forall i : nat, ⊢ ush_at i -∗ ush_lease i ⌝ -∗
        ⌜ forall i : nat, ush_bnd i -> ⊢ Pm i -∗ ush_at i ⌝ -∗
        shk_code γt -∗
        ush_jtab γt -∗
        ush_loop_head R l -∗
        ∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat) (n : nat),
          ⌜ ush_regs m ⌝ -∗
          ⌜ m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ⌝ -∗
          ⌜ m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ⌝ -∗
          ⌜ (k <= i2 < sh_nbuf)%nat /\ f i2 = ubyte0 ⌝ -∗
          ⌜ ush_fd0p l ⌝ -∗
          ush_rest_line f k -∗
          ush_bstate l -∗
          R -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun N h m (mword_of_int 0x97a) (16 + (ush_Dbody + n)) -∗
          WP (Loop : expr riscv_lang)))%I.
```

with the state it is handed (iris/UkSh.v:6631-6633) and the line fact
(:6704-6708):

```coq
  Definition ush_bstate (l : list fdstate) : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch_any γch
     ∗ UserChildren.upid_any γpid ∗ ush_posb l 3%nat)%I.

  Definition ush_rest_line (f : nat -> bv 8) (k : nat) : iProp Σ :=
    ((∀ len : nat,
        ⌜forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0⌝ -∗
        ⌜f (k + len)%nat = ubyte0⌝ -∗ ⌜ush_line_is f k len⌝)
     ∨ T)%I.
```

PLAIN READING.  `urun N h m pc avail` is "the process with record `N` is
running on hart `h` with registers `m` at user pc `pc`, with `avail` words of
stack budget" (design/user-heap.md); `WP (Loop : expr riscv_lang)` is the
weakest precondition of the hart's loop -- the process runs safely from here
on.  sh's `main` reads a line into its buffer at `sh_buf` (`getcmd`), skips
leading blanks, and at `0x97a` dispatches on the line: `cd`, or fork a child
that parses and execs it, wait, and loop.  `ush_rest_l R` says: for the
descriptor table `l` the loop entered with, GIVEN the record's constancy
(`ukn_const N`: sh's exit stub answers both payloads out of one resource),
the two LEASE LAWS (the loop holds the console lease as PIECES `Pm`, and a
payload at a line boundary `ush_bnd` is assembled from them), sh's text and
jump table, and the LOOP HEAD (`ush_loop_head R l`, :6678-6686: the
obligation to run the next turn from `0x938`), the rest of the body from
`0x97a` runs safely whenever the registers are the walk's, the buffer's
first NUL at or after `k` ends a line that is exactly `echo hello world\n`
OR the run is tainted (`ush_rest_line`), the state is the body's
(`ush_bstate`: the standard streams, the working directory pinned at the
root, the children set and the pid as handles, the cursor at the BLOCK-OWED
index 3 -- "a line was read, its output block is owed, nothing chosen yet"),
and `R` -- the opaque per-turn resource, fixed at `sh_Rsh`: the two lexer
tables at `DfracDiscarded` (persistently readable) and the process size at
the exec'd break.

STATUS: OWED.  The only prover of `ush_rest_l` in the tree is
`UkShFork.ushf_rest_of_body` (endgame-audit.md §3), and the R3 survey of
2026-09-14 (app-echo.md "SH-LINE R3 SURVEYED") found it cannot discharge
this `∀ N` statement as it stands for three reasons: (A) it spends the
generic exec supply `UkRun.uxsup`, which at the echo era exists only under
the taint; (B) it needs `UkSh.ush_gen_slot N T` (iris/UkSh.v:6376-6378, "the
taint buys a generic slot"), which is per-record and must move INSIDE
`ush_rest_l`'s box -- a TEXT change to the obligation, ahead; (C) the working
directory was `ucwd_any` -- DONE by step 4 (`ush_bstate` pins `ROOTINO`).
WHO CLOSES IT: lane R3-SURVEY (read-only, running now, in `-sup`;
brief-r3-survey.md) is to state the exact discharger after step 4; the ruling
of record is R3 = `ush_gen_slot` into the box, the pinned composer, then
`UShRest.sh_rest_holds` and the conjunct deleted at `echo_Hinit_boot` and
here.  The sibling `sh_pay_state sh_Rsh 0` IS proved (`sh_pay_state_holds`,
iris/UInitSh.v:649), which is what fixes the family `sh_Rsh`.

### 2.2 The six facts about the starting state and the disk

| Hypothesis | Verbatim | Plain reading | Status |
|---|---|---|---|
| `Hgen0` | `g.(ggen) = 0%nat` | generation counter at zero | part of "start powered off" |
| `Hpow0` | `g.(gpow) = false` | the machine starts OFF; the first step is a power-on | ditto |
| `Himg` | `fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES sb nib cov` | the disk is a well-formed xv6 image: `fsimg_wf` (nine conjuncts: superblock geometry, clean log, inode sanity, bitmap consistency, one directory, dots) and `fs_region_wf`, the inode region is exactly `nib` blocks, the coverage is inside the disk (iris/FsCfgBoot.v:585-595) | COMPUTED for the tracked image (`FsImgCheck.fsimg_wf_ok`, :147; `fsimg_region_wf`, :340), but taken as a hypothesis here |
| `Hdk` | `fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P` | the disk's blocks are the literal image's (iris/FsImgDisk.v:75) | the one real assumption: "the initial disk is the mkfs image" |
| `Hsb` | `sb = fsimg_sb` | the superblock is the parsed one (iris/FsImgCheck.v:126, `fsimg_parse_sb` :129) | computed |
| `Hcov` | `cov = fsimg_cov` | the coverage is blocks 1..1999 (iris/SystemAdequacy.v:2128) | a definition |

The closed SYSTEM theorem `SystemAdequacy.xv6_fs_adequacy_xv6Σ`
(iris/SystemAdequacy.v:2363-2370) takes only `Hgen0`, `Hpow`, and `Hdisk :
v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk`, and discharges every
image fact by computation; the echo theorem still lists the four separately,
and iris/UInitBootAdequacy.v ends at the theorem (:274-277) -- no corollary at
the literal image follows it.  Closing them is the same computation the
system theorem already does; nobody has taken the step because the theorem
is still modulo `Hsh_owed`.

## 3. THE TRACE PREDICATE, AS IT STANDS AFTER PROLOGUE-ALTS-3

All in iris/EchoDisc.v unless noted.  A BYTE is `bv 8`; `sb s` (:71) is a
string's bytes, `nlb` (:73) is `[10]`, the newline.

### 3.1 The input side: `disc`

```coq
Definition echo_line : list (bv 8) :=                                        (* :83 *)
  Z_to_bv 8 <$> [101; 99; 104; 111; 32; 104; 101; 108; 108; 111; 32;
                 119; 111; 114; 108; 100; 10]%Z.
Definition ins (h : list mobs) : list (bv 8) :=                              (* :98 *)
  omap (fun e => match e with ObsUartIn Uart0 b => Some b | _ => None end) h.
Definition star_prefix (pat l : list (bv 8)) : Prop :=                        (* :113 *)
  l = take (length l) (concat (replicate (length l) pat)).
Definition disc_seg (seg : list mobs) : Prop := star_prefix echo_line (ins seg).  (* :198 *)
```

`ins seg` is the bytes the user typed on the console in this cycle;
`disc_seg` (D3) says they are a prefix of `echo hello world\n` repeated.
`echo_line_string` (:93) checks the transcription against the string.

```coq
Fixpoint in_pres (seg : list mobs) : list (list mobs) := ...                   (* :1260 *)
Definition disc_pt (ps cs : list nat) (i : nat) (p : list mobs) : Prop :=      (* :1318 *)
  sess_n ps cs i `prefix_of` obs_wire Uart0 p.
Definition disc_seg' (seg : list mobs) : Prop :=                               (* :1330 *)
  disc_seg seg
  /\ exists ps cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p ->
            pro_ok ps cs (i `div` length echo_line) /\ disc_pt ps cs i p.
Definition disc (h : list mobs) : Prop := Forall disc_seg' (cycles_of h).      (* :1799 *)
```

`in_pres seg !! i` is the cycle's observation prefix strictly before the
`i`-th input byte -- what the user had seen when they typed it.  `disc_pt`
(D1/D2, the RATE discipline) says that at that moment the transcript for `i`
bytes was already on the wire: the user waits for the echo of each byte
before typing the next, and for the whole prompt before typing a line.
`disc_seg'` fixes ONE resolution `(ps, cs)` of the choice points for the
whole cycle and requires every prologue the first `i` bytes enter to have
SETTLED (`pro_ok`, below).  `disc` is that in every cycle.  The predicate is
DECIDABLE (`bounded_lists`, :1341, builds the finite search), which is how the witnesses
of 3.5 are checked by `vm_compute`.

### 3.2 The output side: the transcript

A SESSION TRANSCRIPT is: a PROLOGUE (what the console shows before the
first prompt), then one BLOCK per completed input line, then the echo of the
line in progress.

THE PROLOGUE.  Its four LETTERS (:235-238), the list of them (:291), which
of them CONTINUE a round (:298), and the prologue of a resolution (:312-321):

```coq
Definition u_banner   : list (bv 8) := sb "init: starting sh"%string ++ nlb.
Definition u_prompt   : list (bv 8) := sb "$ "%string.
Definition u_execfail : list (bv 8) := sb "init: exec sh failed"%string ++ nlb.
Definition u_forkfail : list (bv 8) := sb "init: fork failed"%string ++ nlb.

Definition pro_alts : list (list (bv 8)) :=
  [ u_prompt; u_execfail; u_forkfail; u_banner ].

Definition pro_cont (a : nat) : Prop := a = 1%nat \/ a = 3%nat.

Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (pro_cont a) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => []
  | a :: ps' => pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => ~ pro_cont a) ps.
```

PLAIN READING.  A prologue ROUND is one turn of /init's outer loop: it
prints its banner (letter 3, `user/init.c:27`) IF its console open succeeded,
forks, and either the child execs sh and sh prints `$ ` (letter 0 -- the
session begins, the round ENDS), or the child's exec fails and it prints
"init: exec sh failed" and exits, init reaps it and runs another round
(letter 1 -- CONTINUES), or init's fork fails and it prints "init: fork
failed" and exits, after which the kernel panics on the OTHER port and no
process writes this wire again (letter 2 -- ENDS).  `ps` is the list of
letters in wire order; `pro_of ps` is their bytes up to and including the
first ending letter; an OPEN round (no ending letter yet) predicts exactly
the letters filed and nothing more -- `pro_of [] = []`.  That monotonicity
is what a writer's persistent LOWER BOUND on `ps` is worth, and it is why
the banner is a letter and not a prefix (the file's own account, :245-290).
`pro_tail`/`pro_from r ps` (:327, :333) drop one/`r` settled rounds;
`pro_rounds ps` (:340) counts settled rounds; `pro_idx cs i` (:703) counts
how many shells died on their own fork panic before line `i`, i.e. which
round line `i` is in.  The good run is `[3; 0]`
(`pro_of_good : pro_of [3;0] = u_prologue`), the banner-less round `[0]`,
one exec failure and a restart `[3; 1; 3; 0]`, the terminal fork failure
`[3; 2]`.  The four letters are pairwise PREFIX-FREE (the three diagnostics
part at byte 6), which is what pins the resolution off the wire.

THE BLOCKS.  Per completed line (:690-694, :743-753):

```coq
Definition line_alts : list (list (bv 8)) :=
  [ sb "hello world"%string ++ nlb ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ].

Definition alt_cont (ps cs : list nat) (i : nat) : list (bv 8) :=
  line_alts !!! (cs !!! i)
  ++ (if decide (cs !!! i = 3%nat)
      then pro_of (pro_from (S (pro_idx cs i)) ps) else []).

Definition alt_blk (ps cs : list nat) (i : nat) : list (bv 8) :=
  echo_line ++ alt_cont ps cs i.

Definition alt_seq (ps cs : list nat) (q : nat) : list (bv 8) :=
  concat (alt_blk ps cs <$> List.seq 0 q).
```

Line `i`'s block is the echo of its seventeen bytes, then ONE of: echo ran
(alternative 0), sh's child could not exec echo (1), sh's `malloc`/`sbrk`
failed and the child died on its NULL store so nothing was printed but the
next prompt (2), or sh's own `fork1` panicked (3, `user/sh.c` `panic`) --
after which /init reaps the shell and starts a fresh ROUND, whose prologue
is appended.  Their first bytes 'h','e','$','f' are distinct, so the line
choice is readable off one byte.

THE SESSION AND THE CLAIM (:989-994, :1015-1017, :1121-1125, :1960-1961):

```coq
Definition sess_n (ps cs : list nat) (n : nat) : list (bv 8) :=
  pro_of ps ++ alt_seq ps cs (n `div` length echo_line)
            ++ take (n `mod` length echo_line) echo_line.
Definition sess (ps cs : list nat) (l : list (bv 8)) : list (bv 8) :=
  sess_n ps cs (length l).

Definition pro_ok (ps cs : list nat) (q : nat) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps
  /\ (pro_idx cs q < pro_rounds ps)%nat.

Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok ps cs (length l `div` length echo_line)
    /\ Forall (fun c => c < length line_alts) cs
    /\ out `prefix_of` sess ps cs l.

Definition good_out (seg : list mobs) : Prop :=
  expected_rel (ins seg) (obs_wire Uart0 seg).
```

`sess_n ps cs n` is the transcript for `n` input bytes: the prologue, one
block per completed line, the echo of the partial line.  It depends on the
input only through its LENGTH, which is what D3 buys.  `pro_ok ps cs q` says
every letter of `ps` is one of the four and every round the first `q` lines
enter has settled.  `expected_rel l out`: `out` is a prefix of the
transcript for `l` under SOME resolution.  `good_out`: that, at the cycle's
input and wire.  `disc_pt_good_out_pin` (:2006) is the meeting point: at an
input point the two prefix bounds make the wire EQUAL to `sess_n`.

### 3.3 What is admitted, and what is refuted

ADMITTED: the good session; any number of exec failures each printing a
banner and a diagnostic before the session starts; the terminal fork
failure; the shell's own fork panic after a completed line, reaped and
restarted (with the new round's exec or fork failing as round 0's may); a
round with NO banner (init's console open failed, `[0]`); echo's exec
failing in the child; the child dying silently on a NULL `malloc`.
REFUTED, not admitted: "init: wait returned an error\n" (`user/init.c:47`) --
at user level `wait` returns -1 only to a caller with no children (kernel
row T4, `SpecUsertrap.ut_live_out`, iris/SpecUsertrap.v:720; the U-tier row
of `UkRunSys.wp_uk_ecall_wait_null_live`), and init holds the shell's
generation; sh's "cannot cd" (refuted from the line fact) and "open %s
failed" (unreachable on the paid walk, step4-sh-report.md §2).

### 3.4 THE KNOWN WIDENING, and the ruling

Per round the predicate admits EVERY word over `{1, 3}` followed by `0` or
`2` -- e.g. `[3; 3; 0]` (two banners before a prompt) and `[1; 0]` (an exec
diagnostic with no banner) -- because `pro_cont` makes 1 and 3
interchangeable continuers.  The machine never produces those: a banner is
printed exactly once per round on the console arm and never on the closed
arm, and a round with an exec failure always restarts.  So the theorem is
WEAKER than the ruling's literal shape ("a prologue round may be `$ ` alone")
by exactly that: more wires count as good.  It is NOT vacuous (3.5).
OWNER'S RULING, 2026-09-14: "the weaker trace predicate seems alright for
now; let's land it first and then we'll go back and clean things up and
possibly strengthen it" (checkpoint-2026-09-14-step3.md §1; app-echo.md
"PROLOGUE-ALTS-3 LANDED").  Tightening is post-Qed cleanup: a
well-formedness conjunct on `ps` through `pro_ok` plus a premise on
`echo_link_pro`.

### 3.5 The five machine transcripts and their witnesses

All closed, checked by `vm_compute`, no assumptions (:1735-1797,
:1963-1997):

| Witness | The wire | `disc_seg'` at (`ps`, `cs`) | `good_out` |
|---|---|---|---|
| `demo_seg` (:1735) | `u_prologue`, then the first input byte | `demo_disc_seg'` (:1738) at `[3;0]`, `[]` | `demo_good_out` (:1972) |
| `demo_seg_exec` (:1749) | `pro_of [3;1;3;0]` -- banner, exec failure, banner, prompt | `demo_disc_seg'_exec` (:1753) at `[3;1;3;0]`, `[]` | `demo_good_out_exec` (:1977) |
| `demo_seg_fork` (:1759) | `pro_of [3;2]` -- banner, terminal fork failure | `demo_disc_seg'_fork` (:1763) at `[3;2]`, `[]` | `demo_good_out_fork` (:1983) |
| `demo_seg_panic` (:1771) | a whole line typed and echoed, sh's `fork\n`, init's restart round | `demo_disc_seg'_panic` (:1777) at `[3;0;3;0]`, `[3]` | `demo_good_out_panic` (:1988) |
| `demo_seg_noban` (:1786) | `$ ` alone, then the first input byte | `demo_disc_seg'_noban` (:1789) at `[0]`, `[]` | `demo_good_out_noban` (:1994) |

`good_out_nil` (:1963) at `ps = [0]` says a cycle with no output is good.

## 4. THE THIRTEEN AMBIENT ASSUMPTIONS OF `make audit-only`

WHAT THE AUDIT IS.  `make audit-only` (Makefile:301) compiles
`iris/SystemAssumptions.v`, which is one line of content (:69-71):

```coq
Require Import SystemAdequacy.

Print Assumptions xv6_fs_adequacy_xv6Σ.
```

`Print Assumptions` walks every opaque proof in the transitive cone of the
named constant and lists every axiom, `Parameter` and `Hypothesis` it rests
on -- the ONE check that sees through every sealed functor (the file's
header, :3-13).  NOTE THE TARGET: it is the closed SYSTEM theorem
`SystemAdequacy.xv6_fs_adequacy_xv6Σ` (safety and the file system's
durability at the mkfs image), NOT `echo_adequacy_modulo_phi`.  The echo
theorem's cone is a superset (`App`, `AppEcho`, `EchoOut`, `EchoLinks*`,
`EchoDisc`, the whole `Uk*`/`USh*`/`UInit*`/`UEcho*` program tier, and the
kernel rows they read) and no `Print Assumptions` of it exists in the tree;
the file deliberately holds ONE such command (:60-63: consecutive calls
share nothing and each costs ~100 s).  What the lanes' "audit the thirteen"
gate line therefore certifies is that nothing they landed leaked an axiom
into the system theorem's cone; for the echo cone the evidence is section 7
(no `Admitted`, no `Axiom`, every `Hypothesis` discharged).  A second audit
target for the echo theorem would be a one-file addition; this document
recommends it and does not make it.

THE LIST.  Not re-run for this document; taken from durable-notes.md
:854-880 ("The adequacy-print baseline"), SystemAssumptions.v:15-22, and
the last recorded gate (m6b-init-report.md "Gate": md5
`57f7327206c4b276d05035342fea8ecf`, the same md5 the checkpoint and the
step-4 and RESIDUALS briefs name).  Each with why it is an assumption and
not a proof:

```
PrimInt63.int : Set
PrimInt63.eqb : PrimInt63.int -> PrimInt63.int -> bool
PrimInt63.sub : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lsl : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lsr : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.land : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lor : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimString.string : Set
PrimString.get : PrimString.string -> PrimInt63.int -> PrimString.char63
PrimString.cat : PrimString.string -> PrimString.string -> PrimString.string
xv6iris_extras.resv_matches : forall n : BinNums.Z, Values.mword n -> bool
xv6iris_extras.resv_is_valid : bool
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

1-7. `PrimInt63.int`, `.eqb`, `.sub`, `.lsl`, `.lsr`, `.land`, `.lor` --
   Rocq's PRIMITIVE 63-bit integers and the five operations the image
   reader uses.  A `Primitive` has no Rocq body (it is implemented by the
   OCaml runtime), so the assumption traversal classifies it like an axiom.
   They are in the cone because the STATEMENT names the literal disk image
   (`FsImgDisk.fsimg_dk`, iris/FsImgDisk.v:65) as a `PrimString`-backed
   constant read through `PrimString.get`/`PrimInt63` arithmetic.  What is
   trusted: that the runtime's 63-bit integer operations mean what
   `PrimInt63`'s specification says.
8-10. `PrimString.string`, `.get`, `.cat` -- Rocq's PRIMITIVE strings, the
   vehicle for the 2,048,000-byte image and the four ELF binaries (design/
   elf.md: "the PrimString import vehicle for whole binaries").  Same
   reason.
11-12. `xv6iris_extras.resv_matches`, `resv_is_valid` -- this project's own
   two `Parameter`s (model-xv6iris/xv6iris_extras.v:93-94): the Sail model's
   load-reserved/store-conditional RESERVATION predicates ("does this address
   match the reservation", "is the reservation valid").  Sail declares them
   `pure` with no body, so the honest reading is "an arbitrary but fixed
   platform predicate"; every proof that reads one case-splits both ways
   (:48-58), so their CONTENT is never assumed -- only that they are
   functions.  The other four platform hooks of the pinned sail-riscv fork
   are REALISED here as no-ops on the modelled state and are not
   assumptions (:39-47).
13. `functional_extensionality_dep` -- Rocq's standard axiom that two
   functions agreeing on every argument are equal; used in PROOFS (stdpp's
   and this tree's), not in the statement (durable-notes.md:866).  Consistent
   with Rocq's logic; a proof-only assumption.

Anything else on that list is a regression (SystemAssumptions.v:31-33): in
particular any `Link*` entry, since every deliberately-unproven kernel
function is discharged in the theorem's cone.

WHAT THE TWO GATE TOOLS COUNT (the brief's question).
`tools/lemma_diff.py` reports, per file changed against a git ref, GONE (a
top-level declaration present at the ref and absent now), ADMITTED (a proof
closed with `Admitted`/`admit`/`Abort`) and NEWAXIOM (an `Axiom`, `Parameter`
or `Hypothesis` not present at the ref) -- "a prompt to justify each line";
this is why every landing note lists its GONE names and records section
hypotheses as "NEWAXIOM ... discharged at `echo_Hinit_boot`".
`tools/proof_coverage.py` reports, per xv6 kernel function, whether some
`Spec<F>`/`Wp<F>`/`Link<F>` triple PROVES it (a whole-function spec
implemented by a `Module <F>Proof` and instantiated by a `Link*.v`) or only
ASSUMES it (an interface nobody has discharged), keyed off `iris/_CoqProject`
so that a `.v` in the tree but absent from the build can claim nothing
(:548-588); a descoped `# Foo.v` row exempts that file from the "unlisted"
error and counts nothing from it.

## 5. COMPUTED FROM THE REAL ARTIFACTS vs ASSUMED; TRUST IN THE TOOLS

### 5.1 Computed

Everything here is a `vm_compute`d equation or decidable check against
bytes generated from the pinned build, so a mismatch is a build failure.

THE DISK IMAGE.  `kernel-rocq/FsImgRaw.v` is the literal `fs.img` (2,048,000
bytes, deterministic since xv6's `-ffile-prefix-map`) as hex `PrimString`
chunks; `FsImgDisk.fsimg_dk` (iris/FsImgDisk.v:65) reads it as a byte
function, `fsimg_P` (:75) as blocks.  `FsImgCheck.v` computes: the
superblock (`fsimg_parse_sb`, :129), well-formedness (`fsimg_wf_ok`, :147;
`fsimg_region_wf`, :340; the link-count and free-region sweeps, :268-335),
and -- the fact the application rests on -- that the files `/init`, `/sh`,
`/echo`, `/sync` exist at their inode numbers and their CONTENTS are
byte-for-byte the tracked ELF raws (`fsimg_init_path` :438, `fsimg_sh_path`
:442, `fsimg_echo_path` :434, `fsimg_sync_path` :446; design/fs-img.md).
`fsimg_recovery` (iris/FsImgDisk.v:106) proves the recovery hypothesis from
the clean log header (:87).

THE ELF BINARIES.  `user-rocq/{Init,Sh,Echo,Sync}ElfRaw.v` are the literal
`user/_init` etc. (DWARF included); `ElfUser.v` reads each through the
general ELF64 semantics of `ElfFile.v` and proves it well-formed, its entry
(`initEntry = 0xbc`, `shEntry = 0x9d0`), its two `PT_LOAD` segments, its
file image and its zero image (iris/ElfUser.v:110-160 for `sync`, :243-320
`echo`, :334- `sh`, then `init`).  The header (:1-70) is the account of why
this catches a dumper bug: the dumper's reasoning IS what the proofs call
"the program".

THE INSTRUCTION BYTES.  `user-rocq/*Instrs.v` and `*Data.v` are the dumped
text and data; `UCode{Init,ShK,ShM,ShP,Echo,Sync}.v` (generated by
`tools/gen_ucode.py`) prove one `uinstr` fact per instruction -- at this pc
the program's bytes sit in the image and the fetched word DECODES, by
`vm_compute` of the Sail model's own decoder, to the named instruction
(iris/UCodeInit.v:1-66); `init_syms_pins` (:273) pins every symbol address
the walk names (`InitSyms.printf = 0x7c0`, ...).  The kernel side is the
same shape: `kernel-rocq/KernelSyms.v`/`KernelInstrs.v` and the `Code*.v`
layer, checked by `make check-decode`.  Sh's two lexer tables are read off
`ShData.sh_data` (`sh_tbl_parts`, iris/UInitSh.v:366).

THE TRANSCRIPT LITERALS.  `u_banner`, `u_execfail`, `u_forkfail`,
`u_prompt`, `line_alts` (iris/EchoDisc.v:235-238, :690) are TRANSCRIBED
from `user/init.c` and `user/sh.c`.  On the PAID walks the link laws take
the byte as a premise pinned against these lists (`echo_link_pro`'s
`⌜pro_alts !!! a !! 0 = Some b⌝`, quoted in trusted-surface-2026-09-16b.md
§2.1) while the program proof supplies it out of the binary's `.rodata`
(`init_lit_str`, `LIT_START = 0x978`, iris/UkInitMain.v:179-181), so a
mistranscription breaks the build rather than the theorem's truth -- on the
paid walks only; the free-law arms (section 2.1) check nothing.  The reader
still has to agree that these strings are what they mean by "the session".

THE COLD BOOT.  `RiscvLang.reset_regs` is a THEOREM: `ColdBoot.v` runs the
model's own cold-boot chain (`sail_model_init`, the board's reset vector
`0x80000000` and `mhartid`, `init_model`, `init_boot_requirements`) with the
executable semantics and proves the sixteen per-hart reset facts of it
(iris/ColdBoot.v:1-35).  There is no boot ROM beyond that chain; xv6's own
`_entry`/`start`/`timerinit` are whole-function proofs
(design/execution-model.md:7).

### 5.2 Assumed

- The THIRTEEN of section 4 -- ten Rocq primitives, two reservation
  predicates, functional extensionality.
- `Hsh_owed`'s two conjuncts (section 2.1) -- the only hypotheses of the
  echo theorem that are not facts about the image.
- `Hdk` -- that the machine's disk IS the image (a fact about the world the
  theorem is applied to, not about the artifacts).
- The SIX DESCOPED ROWS of `iris/_CoqProject`: `# SystemAssumptions.v`
  (:1075) -- out of the build for cost, compiled by `make audit-only`, so
  not an assumption; `# SpecNamexTr.v`, `# ProofNamexTr.v`, `# LinkNamexTr.v`,
  `# ProofNameiTr.v`, `# LinkNameiTr.v` (:1229-1233) -- the "dv-firing"
  statements of the retired `dview` ghost column, off-build with their source
  intact since the dview retirement of 2026-08-30 (projects/
  fs-syscall-specs.md:363-366; "their `.vo`s were deleted and a full `make`
  rebuilt NOTHING and stayed green").  They are in NO theorem's cone --
  nothing on-build imports them -- so they are not assumptions either; they
  are provenance.  `proof_coverage.py --check` counts nothing from a
  descoped row (:565-588).
- Every `Parameter` in the tree is a field of a `Module Type` (208 files;
  e.g. iris/UtResFits.v:60/:73, iris/UexecWp.v:199): a spec INTERFACE, realised
  by a `Proof<F>` functor and instantiated by a `Link<F>.v`.  An unrealised
  one would show as ASSUMED in the coverage report and, if in the cone, as a
  `Link*` entry in the audit; the audit shows none.

### 5.3 Trust in the tools

- ROCQ 9.0.1, coq-iris 4.4.0, coq-stdpp 1.12.0, coq-sail-stdpp 0.20.1 (the
  opam switch, durable-notes.md:66-68): the proof checker and the logic.
  Iris's adequacy theorem (`wp_strong_adequacy`, instantiated by
  `RiscvAdequacy.riscv_power_adequacy`; design/adequacy.md:5-18) is what
  turns the WPs into the two conclusions.
- THE SAIL RISC-V MODEL IS THE OPERATIONAL SEMANTICS.  `model-xv6iris/rv64d.v`
  and `rv64d_types.v` are GENERATED from the pinned fork
  `zeldovich/sail-riscv` (Makefile:76, `make sail-rev-check` :29) with the
  module list in `model-xv6iris/sail-modules.txt` -- the rv64gc families
  (`I`, `M`, `Zaamo`/`Zalrsc`, `Zca`/`Zcb`, `Zicsr`, `Zifencei`, the counters,
  `Svinval`/`Sstc`, PMP, ...) plus `Zb*`/`B` and `V`, which are compiled in
  and then DISABLED by `sail-config-rv64d.json` (:35-63): the kernel is
  rv64gc, and with B/V on the reset `misa` and the U-mode decode image
  (`DecodeSetU.decodable_u`, "the COMPLETE 32-bit decode image reachable in
  U-mode") would describe a machine the kernel does not run on.  The ISA
  SLICE the theorem is about is therefore what `hartSupports` answers true
  for under that config.  The model's built-in interrupt-generator device is
  disabled because its MMIO window collides with xv6's PLIC (:64-76).  What
  is trusted: that the Sail model, so configured, is the RISC-V machine
  QEMU/`virt` runs xv6 on.
- THE DEVICE MODEL (`DevModel.v`: 16550 UART, PLIC, virtio-mmio disk;
  design/device.md) is this project's own and is DIFFERENTIALLY TESTED
  against QEMU captures (`make vtest-check-ci`, Makefile §5: "These are NOT
  proofs ... is what the real hardware did an execution our model ALLOWS?").
  What is trusted: that the modelled devices admit the real ones' behaviour.
- `boot_fixedGS` (iris/RiscvAdequacy.v:1237) is NOT a boot ROM: it is the
  FIXED GHOST LAYER the power theorem builds -- the Iris ghost names and the
  application's fixed part, filled from the pre-classes so that every field
  reduces.  The "equations" `Hinit_boot` takes (`riscv_rx_tag = app_tag A c`,
  `riscv_kill_cred = app_kill A c`, the out/in/win claims;
  iris/App.v:533-560, iris/SystemAdequacy.v:1306-1345) are FACTS about that
  literal, not assumptions about the world; they are what lets a pinned
  `/init` turn the record's laws into the machine's licences.
- THE GENERATORS (`tools/dump_elf.py`, `gen_ucode.py`, `gen_code.py`) are
  untrusted in the sense that their output is re-derived: `ElfKernel.v`/
  `ElfUser.v` prove the dump IS the ELF, and the decode facts are computed
  from the model, not transcribed.
- THE TRUSTED BASE OF THE STATEMENT.  `Print Assumptions` says what the
  PROOF assumes; what a reader must READ for the statement to mean what
  they think is measured by `tools/tcb/tcb-report.sh` + `tcb_report.py`
  (design/adequacy.md:21-32): as of 2026-08-27, for `xv6_fs_adequacy_xv6Σ`,
  26 `iris/` files, 446 definitions, ~3.46 k lines, plus the four model
  files and three of five `kernel-rocq` files.  NO SUCH REPORT HAS BEEN
  RECORDED FOR THE ECHO THEOREM; its statement additionally unfolds
  `App.xv6_app`'s record, `AppEcho.app_echo`'s fields, `EchoDisc` (section
  3) and, through `Hsh_owed`, `UkSh`'s `ush_rest_l` and its cone.  Section 8
  is the human-readable substitute.

## 6. CHANGES SINCE `trusted-surface-2026-09-16b.md` (5c48c3aa2 -> 7da574e81)

Commits touching trusted files in the range (`git log 5c48c3aa2..HEAD`):
`32d7b6bbf` IO-LEAF M5b; `49cd3b5d1` M5(3); `31aff80ee`/`274483946`
TRAP-ROWS-4 B1a/b; `e8b61dc6a` M6a(2)b; `b39fd4d48` M6a(3)b;
`a583457a6`/`a860c399d`/`eab906990` step 3; `e4f254e70` PROLOGUE-ALTS-3;
`290f05cf0` M6b (B); `2426ca438`/`7da574e81` step 4.  Diff over the eleven
files: +4169/-1255 (`iris/UInitBootAdequacy.v` +46/-; `UInitKernel.v`;
`UInitSh.v`; `EchoDisc.v` +634 net; `UkSh.v` +1606; `UkInitMain.v`;
`UkInit.v`; `UShKernel.v`; `UserConsole.v`; `EchoLinks.v`; `EchoOut.v`).
INIT-DIAG, WRITE-CLOSED and SH-LINE-CRED landed in the range with an EMPTY
trusted diff (their notes say so).

For each: OLD/NEW verbatim, and whether the THEOREM -- its statement --
became STRONGER (fewer or weaker hypotheses, or a stronger conclusion),
WEAKER, or is EQUIVALENT (statement unchanged; the change is inside the
proof or inside an obligation's cone).

### 6.1 `Hsh_owed` lost its third conjunct (M5b, `32d7b6bbf`)

```coq
(* OLD, 5c48c3aa2, iris/UInitBootAdequacy.v *)
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
         /\ (forall (c : app_fixed app_echo) (γp : gname)
                    (N : UkRun.uk_names Σ) (l : list FdSlots.fdstate),
               UkRun.ukn_pay N
                 = UserConsole.ucons_pay FsCfg.fsc_cons γp (echo_taint c) ->
               ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp
                   (echo_taint c) FsCfg.fsc_cons l))

(* NEW, iris/UInitBootAdequacy.v:139-140 *)
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
```

The read leaf is discharged inside `echo_Hinit_boot` by
`UShLine.ush_read_recv_leaf_holds` (iris/UShLine.v:1257, applied at
iris/UInitBoot.v:776).  What made it provable is the change the addendum
announced as planned (§4 there): the console lease carries the era's read
credential --

```coq
(* OLD, 5c48c3aa2, iris/UserConsole.v *)
  Definition ucons_pay (cn : cons_names) (γ : gname) (T : iProp Σ)
    : Z -> iProp Σ :=
    fun _ => ((∃ n : nat, ucons_reader cn n ∗ upos_a γ n) ∨ T)%I.

(* NEW, iris/UserConsole.v:288-291 *)
  Definition ucons_pay (cn : cons_names) (γ : gname) (T : iProp Σ)
      (Rd : nat -> iProp Σ)
    : Z -> iProp Σ :=
    fun _ => ((∃ n : nat, ucons_reader cn n ∗ upos_a γ n ∗ Rd n) ∨ T)%I.
```

-- with `Rd` instantiated at the top at the reader's half of the delivered
count (`UShLine.ush_rd_pin`), under the same existential as the cursor so it
round-trips through /init's `wait` as the reader token does (the file's own
account, iris/UInitBootAdequacy.v:141-151).  STRONGER: one hypothesis fewer,
conclusion unchanged.  `ucons_pay` itself is no longer named by any
hypothesis, so its restatement is proof-internal from the theorem's point of
view.

### 6.2 `init_boot_pay` -- the boot bundle, four times

`UInitKernel.init_boot_pay` is what the boot hands `/init`'s entry
constructor (`init_boot_con`, iris/UInitKernel.v:656-) and what
`echo_Hinit_boot` pays; it is trusted in the predecessors' sense -- the
contract /init's walk is proved against -- but it is NOT a hypothesis of the
theorem (`Hinit_boot` is discharged, iris/UInitBootAdequacy.v:220-256).

```coq
(* OLD, 5c48c3aa2, iris/UInitKernel.v:585 *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Rt : iProp Σ) : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat
     ∗ ∀ N' : uk_names Σ, UkInitMain.kinit_banner0 N' stc Rt)%I.

(* M5b, 32d7b6bbf: the read credential at 0 *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Rt : iProp Σ) (Rd : nat -> iProp Σ) : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Rd 0%nat
     ∗ ∀ N' : uk_names Σ, UkInitMain.kinit_banner0 N' stc Rt)%I.

(* M6a(2)b, e8b61dc6a: the banner paid from a credential Bn and a persistent conversion *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Rt Bn : iProp Σ) (Rd : nat -> iProp Σ) : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Rd 0%nat
     ∗ Bn ∗ □ (∀ N' : uk_names Σ, Bn -∗ UkInitMain.kinit_banner0 N' stc Rt))%I.

(* STEP 3, eab906990: the credential is a FAMILY indexed by the line boundary *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Wc : nat -> nat -> iProp Σ) (Wb Rdl : nat -> iProp Σ)
      : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Rdl 0%nat
     ∗ Wb 0%nat
     ∗ □ (∀ (n : nat) (N' : uk_names Σ),
            Wb n -∗ UkInitMain.kinit_banner0 N' stc (Wc n 0%nat)))%I.

(* NEW, M6b, 290f05cf0, iris/UInitKernel.v:643-654 (comments elided) *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Wp Wb Rdl : nat -> iProp Σ)
      : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Rdl 0%nat
     ∗ Wb 0%nat
     ∗ □ (∀ (n : nat) (N' : uk_names Σ),
            Wb n -∗ UkInitMain.kinit_banner0 N' stc (Wp n))
     ∗ UkInitMain.kinit_diag_law stc Wp Wb)%I.
```

with the new law (iris/UkInitMain.v:192-196):

```coq
  Definition kinit_diag_law (stc : fdstate) (Wp Wb : nat -> iProp Σ) : iProp Σ :=
    (□ (∀ (n : nat) (N' : uk_names Σ),
          Wp n -∗ UkInit.kinit_banner_pay N' stc 21%nat (init_lit LIT_EXEC) (Wb n))
     ∗ □ (∀ (n : nat) (N' : uk_names Σ),
            Wp n -∗ UkInit.kinit_banner_pay N' stc 18%nat (init_lit LIT_FORK) emp))%I.
```

PLAIN READING OF THE NEW SHAPE.  The boot hands /init: the console dance
(open/mknod/dup at the pinned table `stc`), the console ring's reader token
at cursor 0, the era's READ credential at 0 (`Rdl 0`, the reader's half of
the delivered count), the BANNER-OWED credential at 0 (`Wb 0`: "the round's
banner is owed at line boundary 0"), a persistent conversion turning the
banner-owed credential at ANY boundary `n` into the payment for the eighteen
banner bytes leaving the ROUND-OPEN credential `Wp n` ("the round is open,
its next letter unchosen"), and the two DIAGNOSTIC conversions: from `Wp n`,
"init: exec sh failed\n" (21 bytes) is payable leaving `Wb n` (the next
sub-round's banner is owed at the same count), and "init: fork failed\n" (18
bytes) is payable leaving nothing (the round is terminal).  `Wp`, `Wb`, `Rdl`
are opaque families because what a byte leaves behind is the application's
to say; at the top they are `UInitDiag.kinit_pro`, `UInitBanner.kinit_ban`,
`UShLine.ush_rd_pin` (the M6b and step-3 notes).  The four intermediate
shapes are the lane history: M5b added the read half; M6a(2) made the
banner's payment a credential plus a `□` conversion instead of a bare
obligation; step 3 indexed everything by the line boundary so that EVERY
round of /init's restart loop (not only round 0) is paid, and made the
child's exit hand back the pair `init_rd Rdl Wb n := Rdl n ∗ (Wb n ∨ True)`
(iris/UkInit.v:1656-1660); M6b replaced the shell's prompt credential
`Wc n 0` by the round-open shape `Wp n` on the lend (because nothing /init
holds separates the two arms of the prompt credential,
`EchoLinksPro.wr_owed_ambiguous`; iris/UkInit.v:1685) and added the
two diagnostics.  THEOREM: EQUIVALENT at every step -- the statement did not
move.  The PROOF's reliance on the free law shrank: round-k banners and the
two payable diagnostics now go through the era's links on the console row,
and the free law is spent there only on the closed-ledger and affine arms
(m6b-init-report.md).

### 6.3 `sh_pay_rest` -- the tail obligation, three times

```coq
(* OLD, 5c48c3aa2, iris/UInitSh.v *)
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ),
       ush_rest (PS := uprogSG_free) N γp
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.

(* M5(3), 49cd3b5d1: the obligation WITH the line fact, quantified over the taint *)
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.

(* M6a(3)b, b39fd4d48: ...and over the era's write-credential family *)
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ)
       (Wc : nat -> nat -> iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T Wc
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.

(* NEW, step 3, eab906990, iris/UInitSh.v:524-531: ...and over the banner-owed
   family and the lease's pieces *)
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ)
       (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
       (Pm : nat -> iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T Wc Wb Pm
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.
```

`Hsh_owed`'s TEXT (`⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh`) did not change;
the definition it names did, three times, and so the theorem's statement
did.  `ush_rest` (the obligation without the line fact) is GONE; the loop
takes `ush_rest_l` (M5(3)).  STRENGTH: as a HYPOTHESIS the new one is
STRONGER -- universally quantified over the taint `T` and three opaque
families the old one did not mention -- so the theorem, as a conditional
statement, is WEAKER by exactly that until the conjunct is discharged.  The
restatements were made so that the obligation names what the loop actually
carries (the credential beside the cursor, `UkSh.ush_posb`,
iris/UkSh.v:1851) and can be paid where it is instantiated; the endgame
audit's finding that the `∀ T` form is unprovable as stated (because
`ush_gen_slot N T` is per-record) stands and is R3's first item (section
2.1).

### 6.4 `ush_rest_l`'s body: the inner state and the lease laws (M5(3), M6a(3), step 3, step 4)

```coq
(* OLD, 5c48c3aa2, iris/UkSh.v *)
  Definition ush_rest_l (R : iProp Σ) : iProp Σ :=
    (□ (∀ (l : list fdstate),
        ⌜ ukn_const N ⌝ -∗
        shk_code γt -∗
        ush_jtab γt -∗
        ush_loop_head R l -∗
        ∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat) (n : nat),
          ⌜ ush_regs m ⌝ -∗
          ⌜ m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ⌝ -∗
          ⌜ m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ⌝ -∗
          ⌜ (k <= i2 < sh_nbuf)%nat /\ f i2 = ubyte0 ⌝ -∗
          ⌜ ush_fd0p l ⌝ -∗
          ush_rest_line f k -∗
          ush_pstate l -∗
          R -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun N h m (mword_of_int 0x97a) (16 + (ush_Dbody + n)) -∗
          WP (Loop : expr riscv_lang)))%I.

  Definition ush_pstate (l : list fdstate) : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd_any γcwd ∗ UserChildren.uch_any γch
     ∗ ush_pos)%I.

  Definition ush_loop_head (R : iProp Σ) (l : list fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ ush_regs m ⌝ -∗
       ⌜ ush_fd0p l ⌝ -∗
       ush_prompt_in l -∗
       ush_pstate l -∗
       R -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h m (mword_of_int 0x938) (16 + (ush_Dbody + n)) -∗
       WP (Loop : expr riscv_lang))%I.
```

NEW: `ush_rest_l` as quoted in section 2.1 (iris/UkSh.v:6810-6836), with two
pure premises added (`⌜∀ i, ⊢ ush_at i -∗ ush_lease i⌝`, `⌜∀ i, ush_bnd i ->
⊢ Pm i -∗ ush_at i⌝` -- the lease's two laws, premises of the obligation
because the fork arm's payload assembly cannot supply them for an opaque
`Pm`; step-3 note), the state `ush_bstate` (:6631-6633, quoted in 2.1) in
place of `ush_pstate`, and the section parameters `Wc`, `Wb`, `Pm`
(:1514, :1523, :1768).  The head state is now

```coq
(* NEW, iris/UkSh.v:6622-6624 *)
  Definition ush_pstate (l : list fdstate) : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch_any γch
     ∗ UserChildren.upid_any γpid ∗ ush_posb l 0%nat)%I.
```

and `ush_loop_head` (:6678-6686) lost `ush_prompt_in l -∗`: the prompt's
credential rides `ush_posb`'s slot inside the state.  In plain terms the
body is now handed: the cwd PINNED at the root (the disciplined line is
never `cd`; the `cd` arm is refuted at the dispatch), sh's own pid as a
handle (what `wp_kshr_wait_pid`'s reaping row is read against), and the
cursor at the BLOCK-OWED index 3 with the era's write credential beside it
(`ush_posb l 3 := (∃ n, ⌜ush_bnd n⌝ ∗ Pm n ∗ ush_wcp l n 3) ∨ (T ∗
ush_pos)`, :1851) -- a line was read, its output block is owed, and the
fork LENDS that credential to the child (`Rc := Wc np 3`) and the wait
REDEEMS the child's payload back into the slot (step-4 note (A)).  THEOREM:
this is a change INSIDE the second conjunct's obligation, so the statement
changed; strength is not comparable term-for-term (the body is GIVEN more --
the pinned cwd, the pid, the credential -- and ASKED for the lease laws,
which the top supplies).  What it bought is that the shell's proof no longer
needs the affine prompt entry and its child no longer runs at a trivial
payload: `UkShFork.wp_kshf_fork_any`, `ushf_pstate_at`, and the closed
generic supply `UShEcho.sh_exec_sup_of_echo_slot{,_holds,_closed}` are GONE
(lemma_diff, step-4 note).

### 6.5 `EchoDisc`: the banner is a letter (PROLOGUE-ALTS-3, `e4f254e70`)

```coq
(* OLD, 5c48c3aa2, iris/EchoDisc.v:266-288 *)
Definition pro_alts : list (list (bv 8)) := [ u_prompt; u_execfail; u_forkfail ].

Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (a = 1%nat) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => u_banner
  | a :: ps' => u_banner ++ pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => a <> 1%nat) ps.

(* NEW, iris/EchoDisc.v:291-321 *)
Definition pro_alts : list (list (bv 8)) :=
  [ u_prompt; u_execfail; u_forkfail; u_banner ].

Definition pro_cont (a : nat) : Prop := a = 1%nat \/ a = 3%nat.

Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (pro_cont a) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => []
  | a :: ps' => pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => ~ pro_cont a) ps.
```

`pro_rounds` (:340) and `pro_tail` (:327) now test `pro_cont` where they
tested `= 1`.  UNCHANGED, textually: `u_banner`, `u_prompt`, `u_execfail`,
`u_forkfail`, `u_prologue`, `line_alts`, `alt_cont`, `alt_blk`, `alt_seq`,
`sess_n`, `sess`, `pro_ok`, `expected_rel`, `disc_pt`, `disc_seg'`, `disc`,
`good_out`, `echo_phi`.  `pro_of_good` now reads `pro_of [3;0] =
u_prologue`; `pro_of_banner` ("every prologue starts with the banner") is
GONE because it is now false; `demo_seg_noban` and its two witnesses are
NEW (3.5).  THEOREM: WEAKER, deliberately and by ruling (3.4).  Every wire
the old predicate admitted is still admitted -- an old resolution
`[a1; ...; ak]` is the new `[3; a1; 3; a2; ...; 3; ak]` byte for byte -- and
the new one admits more: the banner-less round the ruling asked for, and the
widening of 3.4 the ruling accepted.  `expected_rel` and `disc_pt` being
textually unchanged means the SHAPE of the claim (a prefix test under some
resolution) is what it was; only the set of transcripts grew.

### 6.6 Deleted: `sh_prompt_*`, `ush_prompt_in`/`ush_promptw`, `kinit_round0`, `die_dw`

All gone at HEAD (`grep` over `iris/*.v` for the names returns nothing).
OLD, verbatim:

```coq
(* 5c48c3aa2, iris/UShKernel.v:390-407 *)
  Definition sh_prompt_pay : iProp Σ :=
    (∃ C : iProp Σ,
       C ∗ □ (∀ (N : uk_names Σ) (l : list fdstate),
                ⌜ UkSh.ush_fd2p l ⌝ -∗
                shk_rodata (ukn_t N) -∗
                UkSh.ksh_w N (mword_of_int 2)
                  (mword_of_int UkSh.sh_prompt_pv) 2%nat
                  (ustd (ukn_fd N) l ∗ C) (ustd (ukn_fd N) l)))%I.
  Definition sh_prompt_at (l : list fdstate) : iProp Σ :=
    ((⌜ UkSh.ush_fd2p l ⌝ ∗ sh_prompt_pay) ∨ True)%I.

(* 5c48c3aa2, iris/UkSh.v *)
  Definition ush_promptw : iProp Σ :=
    (∃ C : iProp Σ,
       C ∗ □ (∀ l : list fdstate,
                ⌜ ush_fd2p l ⌝ -∗
                ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
                  (ustd γfd l ∗ C) (ustd γfd l)))%I.
  Definition ush_prompt_in (l : list fdstate) : iProp Σ :=
    ((⌜ ush_fd2p l ⌝ ∗ ush_promptw) ∨ True)%I.

(* 5c48c3aa2, iris/UkInitMain.v:1019-1020 *)
  Definition kinit_round0 (stc : fdstate) (Rt : iProp Σ) : iProp Σ :=
    (kinit_banner0 stc Rt ∨ True)%I.

(* 5c48c3aa2, iris/UkInitMain.v:159 and :391 *)
  Local Notation LIT_WAIT  := 0x9c8.   (* "init: wait returned an error\n" *)
  Lemma wp_kinit_main_die_dw (N' : uk_names Σ) `{!ukn_const N'} (hdw : CpuId) (mdw0 : regfile) (n : nat) :
    ukn_pay N' (-1) -∗
    udepw_law 16 -∗
    init_code (ukn_t N') -∗ init_rodata (ukn_t N') -∗
    urun N' hdw mdw0 (mword_of_int 0x52) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
```

WHAT REPLACED THEM.  The round-0-only prompt pair (an opaque credential `C`
plus a conversion, affine at the entry) is replaced by the loop-resident
credential slot and the prompt's persistent LAW:

```coq
(* NEW, iris/UkSh.v:1571-1574 *)
  Definition ush_wcp (l : list fdstate) (n p : nat) : iProp Σ :=
    ((⌜ ush_fd0c l /\ ush_fd1p l /\ ush_fd2p l ⌝ ∗ Wc n p)
     ∨ (⌜ (exists j : nat, (j <= 2)%nat /\ ush_lcl l j) /\ (p < 3)%nat ⌝ ∗ Wb n)
     ∨ True)%I.  (* AFFINE -- two named producers, see the header *)

(* NEW, iris/UkSh.v:1542-1551 *)
  Definition ush_prompt_law : iProp Σ :=
    (□ ((∀ (n : nat) (l : list fdstate),
           ⌜ ush_fd2p l ⌝ -∗
           ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
             (ustd γfd l ∗ Wc n 0%nat) (ustd γfd l ∗ Wc n 2%nat))
        ∗ (∀ l : list fdstate,
             ⌜ l !! 2%nat = Some FdClosed ⌝ -∗
             ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
               (ustd γfd l) (ustd γfd l))))%I.
```

-- at every line boundary `n`, on the console row the prompt moves the
credential from "0 prompt bytes out" to "2 out", and on a closed fd 2 the
write needs nothing (`UkWriteClosed.ksh_w_of_closed`).  `kinit_round0` is
replaced by `kinit_ban_law`/`kinit_diag_law` (6.2).  `die_dw` is REFUTED:
`UkInit.wp_kinit_wait` now calls `UkRunSys.wp_uk_ecall_wait_null_live`,
whose row `⌜ret = -1 -> cs' = ∅⌝` contradicts init's `γsh ∈ cs` at the wait
head (M6b (A); app-echo.md "DIE-DW CORRECTED": in xv6 a killed process never
returns to user mode, `SpecUsertrap.ut_live_out`, so the only user-level
reason for a -1 is an empty child set, which init refutes from the token of
the shell it forked).  THEOREM: EQUIVALENT (statement unchanged).  The
affine-arm inventory shrank from the addendum's five prompt-related arms
(`ush_prompt_in`, `sh_prompt_at`, `kinit_round0`, the six `Rt ∨ True`,
`ush_wcp`'s) to the three of section 7, and one whole diagnostic arm that
could never be paid -- there is no transcript alternative for it -- is gone
from the proof rather than admitted by the predicate.

### 6.7 Summary table

| Change | Lane / commit | Theorem |
|---|---|---|
| `Hsh_owed` third conjunct deleted; `ucons_pay` gains `Rd` | M5b `32d7b6bbf` | STRONGER |
| `init_boot_pay` x4 (+`Rd 0`; `Bn` + `□` conversion; `Wc Wb Rdl` families; `Wp` + `kinit_diag_law`) | M5b, M6a(2), step 3, M6b | EQUIVALENT (proof-internal; fewer free-law writes) |
| `sh_pay_rest` x3 (`ush_rest_l`, `∀ T`; `∀ Wc`; `∀ Wb Pm`) | M5(3), M6a(3), step 3 | hypothesis STRONGER, theorem WEAKER as a conditional until discharged; the shape R3 must prove |
| `ush_rest_l`'s body: lease laws, `ush_bstate` (cwd pinned, pid, slot 3) | M5(3), step 3, step 4 | inside conjunct 2; not comparable term-for-term |
| `pro_alts`/`pro_cont`/`pro_more`/`pro_of`/`pro_done`; `demo_seg_noban` | PROLOGUE-ALTS-3 `e4f254e70` | WEAKER (conclusion admits more), by ruling |
| `sh_prompt_pay`/`sh_prompt_at`, `ush_promptw`/`ush_prompt_in`, `kinit_round0`, `die_dw`/`LIT_WAIT` deleted | step 3, M6b | EQUIVALENT; three affine arms left |

## 7. PLACEHOLDERS ON THE TRUSTED PATH

Grep over `iris/Uk*.v iris/USh*.v iris/UInit*.v iris/UEcho*.v iris/Echo*.v`
for `∨ True`, `Admitted`, `admit`, `Axiom`, `Parameter`, `Hypothesis`, comment
lines excluded.  Every hit, classified.

### 7.1 `∨ True` -- THREE, all named, all lane RESIDUALS (C)'s

| Site | Text | Stands in for | Killer |
|---|---|---|---|
| iris/UkSh.v:1571-1574 `ush_wcp`'s third arm | `∨ True` | the loop's credential slot with NO credential: two producers left -- init's affine lend arm mapped at the entry (`UInitSh`), and the wait re-entry when the reaped generation cannot be identified as the forked one (`UkShFork`) | (B) the exec-seam rows `uvis_ch W' = ∅`, `uvis_pid W' = pidv` threaded to sh's entry, then (C) delete the arm and `ush_wcp_triv` (:1576) |
| iris/UkInit.v:1656-1657 `init_rd_cred Wb n := (Wb n ∨ True)` | `∨ True` | a shell exit that hands init back no banner-owed credential | (C): every shell exit hands back `Wb n` after (A)/(B); becomes `Wb n` |
| iris/UkInit.v:1696-1700 `init_lend_cred`'s third arm | `∨ True` | the lend on a row with neither credential nor taint (built at `wp_kinit_banner` from `init_rd_cred`'s affine arm) | (C): becomes `T`; "dies with `init_rd_cred`'s arm" (the file's own comment) |

(The step-4 report §4 also names the affine arms of `ush_gets_done_0`/
`ush_gets_done_line` as instances of `ush_wcp_triv`; they are the first row's
producers, not separate `∨ True` texts.)

### 7.2 `Admitted`, `admit`, `Axiom`, `Parameter` -- NONE

`grep -c '^\s*Admitted\.' iris/*.v` is 0 for every file in the tree; the
`admit` grep finds nothing; the only `Axiom` token under `iris/` is in a
comment (iris/LinkSysWrite.v:14); no `Parameter` appears in the five file
families (every `Parameter` in the tree is a `Module Type` field, section
5.2).

### 7.3 `Hypothesis` -- section hypotheses, every one discharged where the section is instantiated

A SECTION HYPOTHESIS is a premise every lemma of a `Section` carries
implicitly; when the section closes it becomes an explicit argument, so
`Print Assumptions` never sees it as an axiom -- but `lemma_diff` reports a
new one as NEWAXIOM, which is why landing notes name them.  None below
reaches the top theorem; the two Coq-level premises that DO reach it are
`Hsh_owed`'s conjuncts (section 2.1), which are theorem premises, not
`Hypothesis`es.

| Hypothesis | Sites | What it says | Discharged by |
|---|---|---|---|
| `Hpsok_free : forall k, free_num k -> psok k` | UkSh.v:634, UkInit.v:131, UkInitMain.v:133, UkShRun.v:247, UkShMain.v:129, UkShFork.v:151, UkShEcho.v:348, UkShCd.v:193, UkShMalloc.v:109, UkShDiag.v:528/1073/3387/6375/7877/7959/8419, UShKernel.v:350, UkSync.v:95; UkCat*.v x6 (a DEAD subtree, endgame-audit.md §1) | every system call whose deposit is `emp` is admitted by the program's instance | at `uprogSG_free` it is the identity (UkInitMain.v:125-133); passed through UInitBoot.v:455/462, UInitSh.v:1138/1275, UShKernel.v:644 |
| `Hpayfree : ⊢ ukn_pay N (-1)` | UkInitMain.v:143 | /init's own exit payload is free | `UkRun.ukn_pay_free_of_triv` (UkRun.v:215) at init's trivial record; used at UkInitMain.v:1404 |
| `ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'` | UkShParseLex.v:162, UkShParseCmd.v:119, UkShParseExec.v:117, UkShParseRedir.v:112, UkShParseTok.v:105 | the allocator's contract (UkShParse.v:3552-3570), WITH its failure arm | `UkShMalloc.ushm_malloc_ok_holds`, applied at UkShMain.v:734 |
| the era laws of `UkSh`: `ush_wb_wc` :1533, `ush_wc_blk_line` :1534, `ush_pm_of_at` :1776, `ush_at_of_pm` :1778, `ush_at_of_pm_taint` :1785, `ush_at_of_pm_wb` :1790, `ush_wb_read` :1802, `ush_wc_read` :1812 | UkSh.v | conversions between the opaque families (`Wb n -∗ Wc n 0`; `Wc n 3 -∗ Wc n 0`; the payload from the pieces at a boundary, with the banner credential, or under the taint; "a line read at an unwritten prompt is the taint"; "a line's read moves the prompt credential to the next boundary") | at `echo_Hinit_boot`, from `UShLine` and `EchoLinks{Ban,Line}`: `ush_wb_read_holds` (UShLine.v:664, applied UInitBoot.v:884), `ush_mid_wc_read`, `ush_at_of_mid_wb`, `ewc_ban_line`, `ewc_lcred_blk_line`; the premises `Hpm1 Hpm2 Hpm3 Hpmwb Hwc Hwbwc Hwbl Hwbr` at UInitBoot.v:455 and UInitSh.v:1138.  `ush_at_of_pm` (the affine assembler) is one RESIDUALS (C) deletes |
| `ush_read_leaf : forall l, ⊢ ush_read_recv_leaf cn l` | UkSh.v:2375 | sh's console read leaf (the former third conjunct) | `UShLine.ush_read_recv_leaf_holds` (UShLine.v:1257), applied at UInitBoot.v:776 |
| `ush_diag_leaf` | UkShRun.v:1280 | sh's three diagnostics (fd 2, `exit(1)`) run safely on the free law | `UkShDiag.ush_diag_leaf_holds` (UkShDiag.v:8444) -- SPENDS `sh_deps`; on the generic runner's path only after M4b(2) |
| the ENGINE's: `Hlo`, `Hpm`, `HRut`, `Hlf0` (UkLeaf.v:182-190, UkBranch.v:68-76, UkLoad.v:1283-1291, UkLoadText.v:686-693, UkStore.v:1481-1489, UkStep.v:1075/1595/2025, UkStepGen.v:833/1112/1719), `HQ0` (UkStepGen.v:839/1117/1724), `X_unfold` :179, `Ret_transparent` :198 | the per-instruction engine | the loop invariant and permission projection of the running process, the borrowed running token, the non-lazy fill row, the slot's unfolding at the U tier's keys | where `urun` is opened: UkRun.v:1050-1054 and :1132-1139; UkStepGen.v:212 and :562 |

Section VARIABLES the top instantiates (not hypotheses, but opaque here):
`T` (UkSh.v:605) := `echo_taint γ`; `Wc` (:1514) := `EchoLinksLine.ewc_lcred`;
`Wb` (:1523) := `UInitBanner.kinit_ban`; `Pm` (:1768) := `UShLine.ush_mid γ
γp`; `cn` (:2373) := `FsCfg.fsc_cons` (the step-3/step-4/M6b notes).

## 8. WHAT YOU ARE TRUSTING -- one page, in plain English

You have a RISC-V machine described by the Sail RISC-V model (a
community-maintained executable specification of the architecture),
configured as the rv64gc machine xv6 is compiled for, with this project's
own model of three devices -- two 16550 UARTs, the PLIC interrupt
controller, a virtio disk -- that has been tested against what QEMU does but
is not itself proved against anything.  Into that machine you load the
xv6 kernel at the pinned revision (Makefile:122) and a disk holding the
mkfs image, both taken as literal bytes and checked, by computation, to be
what the build produced.  You power it on.

THE THEOREM SAYS (section 1): whatever the environment types into the
console and however the harts and devices interleave, (i) the machine never
reaches a state the model has no step for -- no hart executes something
undefined, no device protocol is violated; and (ii) if the person at the
console types `echo hello world` followed by Enter, over and over, waiting
each time for the echo of what they typed before typing more, then in every
power cycle everything that appears on the console is the beginning of a
genuine session transcript: init's banner if init could open the console,
a prompt, the echoed line, `hello world`, the next prompt -- with the
failures that xv6 can really produce (init failing to exec or fork the
shell, the shell failing to fork or exec echo, the shell dying on an
out-of-memory fault) admitted in exactly the forms init and sh print them,
and nothing else ever appearing.  Nothing is claimed if the typist ever
breaks the discipline, and nothing is claimed about the second UART where
the kernel's own messages go.

WHAT THE THEOREM RESTS ON that is not a checked proof (sections 2, 4, 5):

1. Rocq (the proof checker), the Iris separation logic library, and three
   Rocq primitives -- 63-bit integers, primitive strings, and functional
   extensionality -- ten of whose operations show in the audit because the
   disk image and the binaries are stored as primitive strings.
2. The Sail model IS the machine: two reservation predicates of its
   load-reserved/store-conditional mechanism are left as "arbitrary but
   fixed" functions whose content no proof relies on; everything else the
   model leaves to the platform is realised as a no-op on modelled state.
3. The device model admits the real devices' behaviour (tested, not
   proved).
4. The disk in the machine is the mkfs image (`Hdk`); the other three image
   hypotheses are computed facts left as hypotheses for now.
5. TWO STATEMENTS ABOUT THE SHELL'S PROGRAM PROOF (`Hsh_owed`), and this is
   the part to weigh:
   (a) `sh_deps` -- "the shell (and init, and echo's generic entry) may
       write to the console for free".  Every console write that still goes
       through this law is a write the transcript claim does NOT account
       for.  As of step 4 that is: the prompt on the affine arm, a tainted
       turn, the fork's impossible-pid sub-arm and its taint arm, the
       generic runner's diagnostics, init's diagnostics on the closed-ledger
       and affine arms, and the generic echo entry -- every one on a path
       the DISCIPLINED run should never take, but none yet REFUTED or paid.
       Until lane RESIDUALS deletes this conjunct, the theorem's console
       claim is only as good as this hypothesis, and no proof of it is
       expected: the only honest source of a free console write is the
       taint.  This is the single most important line in the document.
   (b) `sh_pay_rest sh_Rsh` -- "the rest of the shell's main loop, from the
       dispatch after a line is read, is correct at the named resource
       family, for every record, taint and credential family".  What has
       been PROVED is everything up to that point (the preamble, the
       prompt, the read of the line at the era's link), the fork arm's
       lend and the wait's redemption, the paid echo child, and sh's own
       diagnostics; what is owed is that this obligation, as stated,
       composes those pieces -- and the R3 survey says its `∀ N`/`∀ T` form
       must first move `ush_gen_slot` inside the obligation before it can.
6. The TRANSCRIPT PREDICATE's definitions (section 3): that `echo_line`,
   the four prologue letters and the four line alternatives are the strings
   you mean, and that "prefix of the transcript under some resolution" is
   the claim you want.  Known and accepted for now: it admits prologue
   rounds the machine never produces (two banners; a diagnostic without a
   banner).
7. The BOOT-BUNDLE and program-tier OBLIGATIONS (`init_boot_pay`,
   `ush_rest_l`, the kernel rows) are not hypotheses -- they are inside
   proofs -- but they are what the program proofs are proved AGAINST, so a
   reader who wants to know what "init's walk is verified" means reads
   them.

WHAT IS NOT TRUSTED: no `Admitted`, no `Axiom`, no unrealised interface,
no section hypothesis left open (section 7); every kernel function in the
boot cone is proved (SystemAssumptions.v:31-33); the dumped binaries and
instructions are re-derived from the ELF files and the model's decoder, not
transcribed; the three remaining `∨ True` arms (section 7.1) are inside the
proof of a hypothesis that is itself still owed, so they weaken nothing the
theorem does not already leave open through `Hsh_owed`'s first conjunct.
