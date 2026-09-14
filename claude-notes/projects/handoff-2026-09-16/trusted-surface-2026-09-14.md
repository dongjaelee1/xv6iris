# The trusted surface since E2 (bde2b8659 -> origin/main 688c4c1b7)

Owner's review document, 2026-09-14.  Scope: every TRUSTED-STATEMENT change the
applications project landed on `main` after E2 INIT-BOOT (`bde2b8659`,
2026-09-13), i.e. the lanes DISC-SIMPLIFY, CONS-ROWS, LAZY-ROW, KILL-PAY (B1,
B2, K4(b), K4(a)), SH-LINE 2b R1'/(a)/(b), OUT-FUPD, SH-STATE, ECHO-PURE,
WRITE-LEAF, CONS-IO milestones A, B, C, SELF-KILL steps 1-4a.  Read against
the checkout at `688c4c1b7`; all line numbers are of that revision.  ECHO-PURE
and WRITE-LEAF touched no trusted statement (ConsLog/EchoOutPure/UkWriteLeaf
are pure leaves and a U-tier program proof); they appear only where a trusted
statement now refers to their vocabulary.  The owner's own commits in the
range ("Proof performance", "Links:", "bump XV6_REV", "prputc",
`3ec850fca`, `5a9154deb`) touch none of the sixteen trusted files.

## 1. What the theorem says today, and what it will say

`UInitBootAdequacy.echo_adequacy_modulo_phi` (iris/UInitBootAdequacy.v:81-253,
`Qed`) is `App.xv6_app_adequacy` at `AppEcho.app_echo` with every obligation
of the record discharged except `Hsh_owed` (two Coq-level entailments at
`uprogSG_free`: sh's write(16) deposit law and sh's tail at the named family
`sh_Rsh`) and `Hphi` (E5's).  Its conclusion is unchanged since E2: at the
real image, powered off at generation 0, every `nsteps` run is safe and
satisfies `AppEcho.echo_phi` =
`Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of κs)` -- per
power cycle, if the console INPUT kept the discipline then the console WIRE
is a prefix of the expected transcript.  What changed is the interface the
kernel offers for the console: the fixed record carries a kill credential, an
OUTPUT claim (`riscv_out_res`: every byte the console UART accepted) and an
INPUT log (`riscv_in_res`: every byte consoleintr accepted with the kernel's
echo choice, and the list a read consumed), both indexed by the generation
number; the kernel updates them only through view shifts the application
supplies (`cons_echo_shift`, `cons_out_chain`, `read_link`), and `Htx` is
handed both claims at every drained byte.  TODAY BOTH CLAIMS ARE THE `emp`
PLACEHOLDERS (iris/AppEcho.v:1403-1418), so every new console obligation is
discharged vacuously and the theorem's console content is what it was at
E2.  When E5 closes (ECHO-OUT, IO-LEAF, SH-LINE R2/R3, PHI) the placeholders
become echo's real claim, `Hphi` is proved from `Htx`'s claim at the drain,
`Hsh_owed` disappears, and -- per the owner's ruling of 2026-09-14
(scratchpad `e5-design.md` REVISION 4, "no per-cycle form; once tainted in
one era, tainted forever") -- the conclusion becomes
`echo_phi g h := disc h -> Forall good_out (cycles_of h)`.

## 2. Per trusted file

### 2.1 `iris/RiscvPtsto.v` -- the fixed record

`riscvFixedGS` (iris/RiscvPtsto.v:399) gained three fields after
`riscv_rx_tag` (:568-570, unchanged):

```coq
  riscv_kill_cred : iProp Σ;                                     (* :591 *)
  riscv_kill_cred_persistent : Persistent riscv_kill_cred;
  riscv_kill_cred_timeless : Timeless riscv_kill_cred;
  riscv_out_res : nat -> list mobs -> list (bv 8) -> iProp Σ;    (* :687 *)
  riscv_out_res_timeless :
    forall (k : nat) (h : list mobs) (acc : list (bv 8)),
      Timeless (riscv_out_res k h acc);
  riscv_in_res : nat -> list mobs -> list ConsLog.log_entry ->   (* :726 *)
                 list (list mobs * bv 8) -> iProp Σ;
  riscv_in_res_timeless :
    forall (k : nat) (h : list mobs) (pops : list ConsLog.log_entry)
           (dl : list (list mobs * bv 8)), Timeless (riscv_in_res k h pops dl);
```

with `Global Existing Instance` for the four class fields (:745-752).  The
first argument `k` of the two resources is the ERA NUMBER, instantiated by the
kernel at `S gen_id` (milestone C); `h` is a witness history the port
invariant holds a monotone lower bound on; `acc` is every byte stored to the
console UART; `pops : list (list mobs * bv 8 * list (bv 8))` is the log of
accepted inputs as `(history, byte, echo)`; `dl` is every input the read path
consumed.  The credential is persistent and timeless; the two resources are
timeless and NOT persistent (they are meant to hold an authority).  The
trivial instances (:1025, :1039, :1048):

```coq
Definition kill_cred_triv {Σ : gFunctors} : iProp Σ := True%I.
Definition out_res_triv {Σ : gFunctors} :
    nat -> list mobs -> list (bv 8) -> iProp Σ := fun _ _ _ => emp%I.
Definition in_res_triv {Σ : gFunctors} :
    nat -> list mobs -> list ConsLog.log_entry ->
    list (list mobs * bv 8) -> iProp Σ :=
  fun _ _ _ _ => emp%I.
```

One new lemma on the history ghost, `obs_hist_lb_cmp` (:989): two lower
bounds on the `mono_list` history are prefix-comparable.  `RiscvPtsto.v` now
imports `ConsLog` (:15) for `log_entry`.

### 2.2 `iris/App.v` -- the record and its obligations

The record `xv6_app` (iris/App.v:120-217).  Unchanged fields: `app_fixed`,
`app_cl`, `app_names`, `app_pred`, `app_R`, `app_tag`, `app_phi`.  Changed
and new:

```coq
  (* OLD *) app_boot  : app_fixed -> app_names -> iProp Σ;
  (* NEW *) app_boot  : app_fixed -> nat -> app_names -> iProp Σ;              (* :144 *)
  app_kill  : app_fixed -> iProp Σ;                                             (* :169 *)
  app_out   : app_fixed -> nat -> list mobs -> list (bv 8) -> iProp Σ;         (* :205 *)
  app_in    : app_fixed -> nat -> list mobs -> list ConsLog.log_entry ->       (* :213 *)
              list (list mobs * bv 8) -> iProp Σ;
```

`app_boot` carries the era number (milestone C); `app_kill` is the record's
entry for `riscv_kill_cred` (echo: `echo_taint`); `app_out`/`app_in` are the
entries for the two resources (echo: the `emp` placeholders).  `MkApp` has
eleven arguments; `app_triv` (:229-233) fills the new slots with
`fun _ => True`, `fun _ _ _ _ => emp`, `fun _ _ _ _ _ => emp`.

`xv6_app_adequacy` (:242).  Unchanged obligations: `Hbirth`, `HRt`, `Htagp`,
`Htagt`, `HR0`, `Hpow`, `Happ_init`, `Hgen0`, `Hpow0`, `Himg`.  New:

```coq
    (Hkillp : forall c : app_fixed A, Persistent (app_kill A c))              (* :266 *)
    (Hkillt : forall c : app_fixed A, Timeless (app_kill A c))
    (Happ_kill : forall (c : app_fixed A) (r : app_names A),
       AppInv.app_sup_raw (app_pred A c) r ⊢ □ app_kill A c)
    (Houtt : forall (c : app_fixed A) (k : nat) (h : list mobs)
                    (acc : list (bv 8)),
       Timeless (app_out A c k h acc))                                         (* :283 *)
    (Happ_out_sup : forall (c : app_fixed A) (r : app_names A),               (* :299 *)
       AppInv.app_sup_raw (app_pred A c) r
         ⊢ □ (∀ (k : nat) (h : list mobs) (acc : list (bv 8)) (b : bv 8),
                app_out A c k h acc ==∗ app_out A c k h (acc ++ [b])))
    (Hinpt : forall (c : app_fixed A) (k : nat) (h : list mobs)
                    (pops : list ConsLog.log_entry)
                    (dl : list (list mobs * bv 8)),
       Timeless (app_in A c k h pops dl))                                      (* :306 *)
    (Happ_in_sup : forall (c : app_fixed A) (r : app_names A),                (* :318 *)
       AppInv.app_sup_raw (app_pred A c) r
         ⊢ □ (∀ (k : nat) (h : list mobs) (pops : list ConsLog.log_entry)
                (dl : list (list mobs * bv 8)) (e : ConsLog.log_entry),
                app_in A c k h pops dl ==∗ app_in A c k h (pops ++ [e]) dl)
           ∗ □ (∀ (k : nat) (h : list mobs) (pops : list ConsLog.log_entry)
                  (dl ws : list (list mobs * bv 8)),
                  app_in A c k h pops dl ==∗ app_in A c k h pops (dl ++ ws)))
```

`Happ_kill`: the application's supply (the credential an unverified process
runs on) buys the kill credential, so the kernel's kill price is payable by
the generic slot and by no verified program.  `Happ_out_sup`/`Happ_in_sup`:
the supply buys the two LICENCES (append any byte to the output claim; file
any log entry; consume any window) -- the price of a generic process's
`write(2)`, of consoleintr's shift on its behalf, and of its `read(2)`.

`Htx` (:353) OLD vs NEW.  OLD:

```coq
    (Htx : forall (HR : riscvGS Σ) `{HF : !fileG Σ}
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartOut i b])%list))
```

NEW:

```coq
    (Htx : forall (HR : riscvGS Σ) (GEN : GenId) `{HF : !fileG Σ}
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
              (ho hi : list mobs) (pops : list ConsLog.log_entry)
              (dl : list (list mobs * bv 8)),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              ⌜u_wire u = u_out u⌝ -∗
              ⌜obs_boots h = S gen_id⌝ -∗
              ⌜ho `prefix_of` h⌝ -∗
              ⌜hi `prefix_of` h⌝ -∗
              (if i is Uart0 then app_out A c (S gen_id) ho (uart_acc u)
               else emp) -∗
              (if i is Uart0 then app_in A c (S gen_id) hi pops dl else emp) -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              (if i is Uart0 then app_out A c (S gen_id) ho (uart_acc u)
               else emp) ∗
              (if i is Uart0 then app_in A c (S gen_id) hi pops dl else emp) ∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartOut i b])%list))
```

The ledger step is now handed, at the console port, the kernel's wire fact
`u_wire u = u_out u`, the era stamp, and the two claims at witness histories
that are real prefixes of `h`, linearly, and must return them -- this is the
ONLY channel from the console's discipline to `Hphi`.  `Hrx` (:418) gains the
`GEN` binder and the premise `⌜obs_boots h = S gen_id⌝ -∗` and nothing else.

`Happ_boot` (:447) OLD `forall c, ⊢ app_xfer_boot_raw (app_pred A c) (app_boot A c)`;
NEW:

```coq
    (Happ_boot : forall (c : app_fixed A) (k : nat),
       ⊢ app_xfer_boot_raw (app_pred A c) (app_boot A c k) (app_out A c k)
           (app_in A c k))
```

`Hinit_boot` (:460) gains three record equations beside the rx-tag one and
takes the boot resource at the era:

```coq
         riscv_rx_tag = app_tag A c ->
         riscv_kill_cred = app_kill A c ->
         @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
         @riscv_out_res Σ (@riscv_fixedGS Σ HR) = app_out A c ->
         @riscv_in_res Σ (@riscv_fixedGS Σ HR) = app_in A c ->
         ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot A c (S gen_id) r -∗
           |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0)
```

(OLD: `app_boot A c r`, no kill/out/in equations.)  The equations are facts
about the `boot_fixedGS` literal, not assumptions; they are what lets a
pinned `/init` turn `Happ_out_sup`/`Happ_in_sup` into the machine's licences.

New obligation `Happ_echo` (:524):

```coq
    (Happ_echo :
       forall (HR : riscvGS Σ) (c : app_fixed A),
         @riscv_out_res Σ (@riscv_fixedGS Σ HR) = app_out A c ->
         @riscv_in_res Σ (@riscv_fixedGS Σ HR) = app_in A c ->
         @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = app_tag A c ->
         ⊢ ∀ (GEN : GenId) (XI : CurCtx),
             @SpecConsoleintr.cons_echo_shift Σ HR GEN XI)
```

The application must justify, once and persistently, the console interrupt's
echo of every accepted byte and the filing of that byte in the log (section
2.6.1).  `Hphi` (:541) is unchanged in shape; its `boot_fixedGS` literal now
lists `(app_kill A c) (Hkillp c) (Hkillt c) (app_out A c) (Houtt c) (app_in A c) (Hinpt c)`
after the tag triple (:549-551).

### 2.3 `iris/SystemAdequacy.v` and `iris/RiscvAdequacy.v` -- transport and boot

`app_xfer_boot_raw` (iris/SystemAdequacy.v:259) is the four-component
transport:

```coq
Definition app_xfer_boot_raw {Σ : gFunctors} {N : Type}
    (A : N -> FsAbsDefs.aview -> iProp Σ) (B : N -> iProp Σ)
    (O : list mobs -> list (bv 8) -> iProp Σ)
    (I : list mobs -> list ConsLog.log_entry ->
         list (list mobs * bv 8) -> iProp Σ) : iProp Σ :=
  (□ (∀ (r : N) (av : FsAbsDefs.aview),
        ▷ A r av ==∗ ▷ A r av ∗
        ∃ r' : N, ▷ A r' av ∗ B r' ∗ O [] [] ∗ I [] [] []))%I.
```

The OLD form (two components, `∃ r', ▷ A r' av ∗ B r'`) survives as the
premise of the bridge `app_xfer_boot_raw_out` (:281), which bolts on `O [] []`
and `I [] [] []` for an application that founds them from nothing -- echo's
`echo_xfer_boot` today.  THE FOUNDING IS THE TRANSPORT'S: there is no `_nil`
field or obligation; the era's claim at the empty run is what the transport
yields, and the PowerOn lend carries it to the boot (:1578-1581):

```coq
           (fun c k dk => ∃ (gt : gname) (r : app_names),
              P_fs_lend_at gt cov (FsImg.sb_logstart sb) dk ∗
              ▷ app_dur_at (app_fs c) gt r ∗ app_boot c (Datatypes.S k) r ∗
              Ores c (Datatypes.S k) [] [] ∗ Ires c (Datatypes.S k) [] [] [])%I
```

`xv6_boot_era` (:534) hands `O [] []`/`I [] [] []` to `uart_ghosts_alloc
Uart0`, under two new equations `riscv_out_res = O ->` (:647) and
`riscv_in_res = I ->` (:651), and takes `Hecho` (:620) at every `GEN0`/`XI`.

Because the lend is era-indexed, `RiscvAdequacy.Rb` gained the generation:
`(Rb : nat -> (Z -> bv 8) -> iProp Σ)` (iris/RiscvAdequacy.v:682), `Hswap`
yields `Rb gen dk` (:722), `Hboot` receives `(Rb gen)` (:754); in
`riscv_power_adequacy` `(Rb : CT -> nat -> (Z -> bv 8) -> iProp Σ)` (:1525),
`Rb c gen dk` (:1542), `(Rb c gen)` (:1709).  `boot_fixedGS` (:1150) takes,
after `HTgt`, `(Kc : iProp Σ) (HKc : Persistent Kc) (HKct : Timeless Kc)`
(:1174), `Ores`/`HOrest` (:1183), `Ires`/`HIrest` (:1191), filled into the
literal after `HTgt` (:1208); `riscv_power_adequacy` threads the seven as
`CT`-indexed parameters (:1568-1589), `riscv_trace_adequacy` at the trivial
instances (:1923-1927).

`xv6_power_adequacy_gen` (iris/SystemAdequacy.v:1141) gained, in order:
`Happ_boot : forall (c : CT) (k : nat), ⊢ app_xfer_boot_raw (app_fs c) (app_boot c k) (Ores c k) (Ires c k)`
(:1216); `Kc`/`HKc`/`HKct` (:1238-1240) and

```coq
    (Hkill_sup : forall (c : CT) (r : app_names),
       AppInv.app_sup_raw (app_fs c) r ⊢ □ Kc c)                            (* :1252 *)
    (Hout_sup : forall (c : CT) (r : app_names),                             (* :1258 *)
       AppInv.app_sup_raw (app_fs c) r
         ⊢ □ (∀ (k : nat) (h : list mobs) (acc : list (bv 8)) (b : bv 8),
                Ores c k h acc ==∗ Ores c k h (acc ++ [b])))
    (Hin_sup : forall (c : CT) (r : app_names),                              (* :1266 *)
       AppInv.app_sup_raw (app_fs c) r
         ⊢ □ (∀ ... e, Ires c k h pops dl ==∗ Ires c k h (pops ++ [e]) dl)
           ∗ □ (∀ ... dl ws, Ires c k h pops dl ==∗ Ires c k h pops (dl ++ ws)))
```

plus `Hinit_boot` (:1292) with the kill/out/in equations and
`app_boot c (Datatypes.S gen_id) r`, and `Happ_echo` (:1339).  `Hkill_sup`,
`Hout_sup`, `Hin_sup` are SPENT at `init_boot_of_sup` (:1077): the generic
slot's mint takes `app_sup -∗ □ riscv_kill_cred -∗ init_boot_bundle` under
the two Coq premises `(app_sup ⊢ out_licence)` and `(app_sup ⊢ in_licence)`.
`xv6_trace_adequacy` (:1785) gained `Hecho` (:1872), `Hxfer` (:1889),
`Hout_lic` (:1899), `Hin_lic` (:1905): the generic ledger client's own
account of its arbitrary `Ores`/`Ires`.

### 2.4 `iris/UInitBootAdequacy.v` -- the top theorem

The statement as of today (iris/UInitBootAdequacy.v:81-158; comments elided):

```coq
  Theorem echo_adequacy_modulo_phi
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh))
      (Hphi : forall (Hinv : invGS Σ)
                     (γgen γstart γreg γd γsw γobs γhist : gname)
                     (c : app_fixed app_echo)
                     (T : list mobs) (g' : gstate) (h : list mobs),
         ⊢ @power_interp Σ
              (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
                 (xv6_slot (app_names app_echo) (app_pred app_echo) cov
                    (FsImg.sb_logstart sb) γd γsw γreg γstart c)
                 γobs T (obs_ledger_at (app_R app_echo c) γobs) γhist
                 (app_tag app_echo c) (echo_Htagp c) (echo_Htagt c)
                 (app_kill app_echo c) (echo_Hkillp c) (echo_Hkillt c)
                 (app_out app_echo c) (echo_Houtt c)
                 (app_in app_echo c) (echo_Hinpt c)
                 (app_fixed app_echo) c) g' -∗
           ghost_var γobs (1/2) h -∗ ⌜obs_wf h g'⌝ -∗
           ▷ xv6_slot (app_names app_echo) (app_pred app_echo) cov
               (FsImg.sb_logstart sb) γd γsw γreg γstart c -∗
           ▷ obs_ledger_at (app_R app_echo c) γobs -∗
           ◇ ⌜app_phi app_echo g' h⌝)
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

`Hsh_owed` OLD (at E2):

```coq
         exists Rsh : gname -> gname -> gname -> iProp Σ,
           (⊢ UkRun.udepw_law (PS := uprogSG_free) 16)
           /\ (⊢ UkSh.sh_deps (PS := uprogSG_free))
           /\ (⊢ UInitSh.sh_pay_state Rsh 0%nat)
           /\ (⊢ UInitSh.sh_pay_rest Rsh))
```

The two residues: `UkSh.sh_deps : iProp Σ := udepw_law 16` (iris/UkSh.v:435;
OLD `udepw_law 5 ∗ udepw_law 16`, :297 at E2) -- sh's write(16) deposit law
at the free instance, which `udepw_law 16` (the first old conjunct) now
duplicates and so is gone; and `UInitSh.sh_pay_rest sh_Rsh` (iris/UInitSh.v:493)
-- `∀ γp N, ush_rest (PS := uprogSG_free) N γp (sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N))`,
sh's tail (R2/R3) at the NAMED family
`sh_Rsh := fun _ γd γs => UkShLoop.ushl_dat γd ∗ usz γs (kexec_sz ElfUser.sh_elf)`
(:606).  `sh_pay_state sh_Rsh 0` is proved (`sh_pay_state_holds`, :609).  The
proof applies `xv6_app_adequacy` with twenty-three holes (:190-191) and
discharges `Happ_kill`, `Happ_out_sup`, `Happ_in_sup` (:193-195) and
`Happ_echo` (:248) from `AppEcho`.  `Hsbrk` is NOT a hypothesis of this
theorem: it is a premise of the U-tier lemmas `UkShMain.v:670`,
`UkShFork.v:238`, `UkShEcho.v:782`.

### 2.5 `iris/EchoDisc.v` and `AppEcho.echo_phi` -- the discipline

DISC-SIMPLIFY removed the boot-message machinery (`subseqb`/`k_done`/
`k_point`/`k_pt`, `shuffle`, `boot_stream`, the digit-freeness argument; 62
names GONE) and states the discipline on the console UART's wire alone.
The current definitions:

```coq
Definition disc_seg (seg : list mobs) : Prop := star_prefix echo_line (ins seg).   (* :198 *)

Definition u_prologue : list (bv 8) :=                                             (* :232 *)
  sb "init: starting sh"%string ++ nlb ++ sb "$ "%string.

Definition line_alts : list (list (bv 8)) :=                                       (* :250 *)
  [ sb "hello world"%string ++ nlb ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ++ sb "init: starting sh"%string ++ nlb
      ++ sb "$ "%string ].

Definition sess_n (cs : list nat) (n : nat) : list (bv 8) :=                       (* :285 *)
  u_prologue ++ alt_seq cs (n `div` length echo_line)
             ++ take (n `mod` length echo_line) echo_line.

Definition expected_rel (l out : list (bv 8)) : Prop :=                            (* :300 *)
  exists cs : list nat,
    Forall (fun c => c < length line_alts) cs /\ out `prefix_of` sess cs l.

Definition disc_pt (cs : list nat) (i : nat) (p : list mobs) : Prop :=             (* :470 *)
  sess_n cs i `prefix_of` obs_wire Uart0 p.

Definition disc_seg' (seg : list mobs) : Prop :=                                   (* :478 *)
  disc_seg seg
  /\ exists cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p -> disc_pt cs i p.

Definition disc (h : list mobs) : Prop := Forall disc_seg' (cycles_of h).          (* :574 *)

Definition good_out (seg : list mobs) : Prop :=                                    (* :737 *)
  expected_rel (ins seg) (obs_wire Uart0 seg).
```

D3 (`disc_seg`): the input bytes are a prefix of `(echo hello world\n)*`.
D1/D2 (`disc_pt`): before input byte `i` is typed, the transcript for `i`
bytes is already on the wire, measured from the start of the wire (there is
no kernel prefix to skip: nothing but the session writes `Uart0`).
`good_out`: the wire is a prefix of the transcript for the input's length,
under some resolution of the per-line alternatives (`line_alts`, the owner's
O5 list).  `disc_pt_good_out_pin` (:758) is the anti-vacuity meeting point:
at an input point the wire IS `sess_n cs i`.  ECHO-PURE added lemmas only
(`disc_prefix` :720, `star_prefix_prefix` :150, `disc_seg_prefix` :210, the
periodicity lemmas :163-197).  The conclusion (iris/AppEcho.v:1362):

```coq
Definition echo_phi : gstate -> list mobs -> Prop :=
  fun _ h => Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h).
```

with `echo_phi_disc : disc h -> echo_phi g h -> Forall good_out (cycles_of h)`
(:1367).  PER THE OWNER (e5-design.md REVISION 4, 2026-09-14) this is about
to be restated to `echo_phi g h := disc h -> Forall good_out (cycles_of h)`:
the guarded per-cycle form is unprovable, because a taint in cycle 1 licenses
garbage in cycle 2 while `disc_seg'` of an input-free cycle 2 holds
vacuously.

### 2.6 The kernel specs the application pays into

#### 2.6.1 `SpecConsoleintr.cons_echo_shift` (iris/SpecConsoleintr.v:214)

```coq
  Definition cons_echo_shift `{XI : CurCtx} : iProp Σ :=
    (□ ∀ (h : list mobs) (c : bv 8) (cs : list (bv 8)) (Φ : iProp Σ),
        ⌜obs_ends_in Uart0 h c⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
        ⌜cons_echo c cs⌝ -∗
        riscv_rx_tag h -∗ obs_hist_lb h -∗ Φ -∗ in_run (S gen_id) h c [] cs Φ)%I.
```

New with OUT-FUPD; there was no such statement at E2 (consoleintr's post then
carried the located receipt `uart_sent_sub γu cs ∗ ⌜cons_echo cb cs⌝`, and
`console_caps` carried `uart_sent_sub γu []`).  The application pays, for
every byte `c` that arrived at history `h` in this era, a stoppable run
`in_run` = the `echo_link`s for the bytes the arm will emit (an upper bound
`cs`, of shape `ConsLog.cons_echo c cs`: `[]`, `[echo_of c]`, or backspace
triples only for an erase byte) followed by `in_append (h, c, cs')`, the log
entry at what was emitted.  The kernel promises to fire it once per accepted
byte from every consoleintr arm (drop, store, erase), with the byte's tag,
its history bound and the era stamp in hand; it is a conjunct of
`console_caps` (:266) minted at main.

#### 2.6.2 `SpecFileread.fileread_in` / `console_receipt` (iris/SpecFileread.v:928, :1031)

```coq
  Definition fileread_in (st : fdstate)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ) (P : iProp Σ) : iProp Σ :=
    (P -∗
     match st with
     | FdOpen true _ (FdInode i γo) =>
         P ∗ pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F
     | FdOpen true _ (FdDevice mj) =>
         if decide (mj = CONSOLE)
         then cons_acc fsc_cons app_sup (fun cur dc => P ∗ Rd cur dc)
              ∗ WpUart.cons_read_pay (S gen_id) Rin
         else P
     | _ => P
     end)%I.
```

OLD had no `Rin` and no `cons_read_pay`.  The process pays, on the console
arm, the ring's payment (its reader token or the dirty credential
`app_sup`) and ONE `read_link` at every window `ws` (`cons_read_pay k R :=
∀ ws, read_link k ws (R ws)`, iris/WpUart.v:2432); the kernel promises to fire
it at consoleread's final release on the clean arm and hand `Rin ws` back at
the consumed window.  `console_receipt P Rd Rin n r M' addr` (:1031-1137)
gained the count `n` (CONS-ROWS), the -1 arm's reason (K4(b)), the two
control-flow rows, the run bound and, on the clean window arm, the consumed
window and `Rin ws` (milestone B):

```coq
    ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
      (⌜(n < 0)%Z⌝ ∨ □ riscv_kill_cred) ∗
      ∃ cur d' : nat, Rd cur d')
     ∨ ∃ (d dc cur : nat) (hs : list (list mobs))
         (sl : list (list mobs * bv 8)),
         ⌜Z.of_nat d = bv_unsigned r⌝ ∗
         ⌜(Z.of_nat d <= Z.max 0 n)%Z⌝ ∗
         ⌜Z.of_nat d = Z.max 0 n -> dc = d⌝ ∗
         ⌜d = 0%nat -> (0 < n)%Z -> dc = (d + 1)%nat⌝ ∗
         ⌜length hs = d⌝ ∗
         ⌜... per-byte ledger ...⌝ ∗
         ([∗ list] h ∈ hs, riscv_rx_tag h) ∗
         cons_stored_lb fsc_cons sl ∗
         (⌜forall j : nat, (j < d)%nat -> ... sl !! (cur + j)%nat = Some (h, b)⌝ ∗
           ⌜length sl = (cur + d)%nat⌝ ∗ ⌜cons_chain sl⌝ ∗
           cons_swallow fsc_cons
             (~ uva_wmapped P (uint (add_vec_int addr (Z.of_nat d)))) sl d dc
           ∗ (∃ (sl' ws : list (list mobs * bv 8)),
                cons_stored_lb fsc_cons sl' ∗ ⌜sl `prefix_of` sl'⌝ ∗
                ⌜length sl' = (cur + dc)%nat⌝ ∗ ⌜length ws = dc⌝ ∗
                ⌜forall j : nat, (j < dc)%nat ->
                   ws !! j = sl' !! (cur + j)%nat⌝ ∗
                Rin ws)
          ∨ cons_dirty_cred app_sup) ∗
         Rd cur dc)%I.
```

The kernel promises: a -1 from a non-negative request carries the kill
credential (`n < 0` is fileread's own guard); a filled request popped exactly
its run (B1); an empty run against a positive request popped one byte (B4);
the consumed window `ws` is the stored sequence at `[cur, cur + dc)`.
`fileread_ret` (:229, `pipe_rw_ret n r`) is restored in front of row 5's post
(`xv6_spost`, iris/UexecExecInst.v:688), and `fileread_dev_env`'s per-cell
row is exclusive, `(mj <> CONSOLE /\ slot = 0) \/ (mj = CONSOLE /\ slot = consoleread)`
(:435-444), so the `devsw.read == NULL` exit cannot be the console's.

#### 2.6.3 `SpecConsolewrite.cons_out_chain` (iris/SpecConsolewrite.v:158)

```coq
  Fixpoint cons_out_chain (k : nat) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (j cnt : nat) : iProp Σ :=
    match cnt with
    | O => Q j
    | S cnt' =>
        (Q j
         ∧ (∀ b : bv 8,
              ⌜M !! uint (add_vec_int ua (Z.of_nat j)) = Some b⌝ -∗
              out_link Uart0 k b (cons_out_chain k M ua Q (S j) cnt')))%I
    end.
```

New with OUT-FUPD, replacing the trace-seed/located-receipt pair
(`uart_sent_from`, `cons_sent_cnt`, `wcons_ok`/`wcons_short`, `wf_tr0`).  A
writer pays one `out_link` per byte at its own cursor, the byte pinned
against the image it lent, and may be stopped at any prefix (`Q j`, an
additive conjunction); the kernel promises consolewrite stores exactly those
bytes and returns the cursor at the count it pushed.  Row 16 of
`xv6_sbundle` is `filewrite_in ... (wf_Q f)` (iris/UexecExecInst.v:541-543);
the generic write is `cons_out_chain_of_licence` (:215) at `fun _ => True`.

#### 2.6.4 `SpecConsoleread`'s contract (iris/SpecConsoleread.v:126)

Three new premises and four new rows.  Premises: `cons_pay cn Wd ord -∗`
(:193, unchanged), `WpUart.cons_read_pay (S gen_id) Rin -∗` (:197) and
`WpUart.uart_inv Uart0 (cn_uart cn) -∗` (:203, ruling F6: the fire opens the
port invariant inside the WP).  Post (all `-∗` premises of the continuation):

```coq
      (⌜(0 <= r)%Z⌝ ∨ □ riscv_kill_cred) -∗                                   (* :240 *)
      ⌜(Z.of_nat d <= Z.max 0 n)%Z⌝ -∗
      ⌜(0 <= r)%Z -> r = Z.of_nat d⌝ -∗
      ⌜Z.of_nat d = Z.max 0 n -> dc = d⌝ -∗                                    (* :264 *)
      ⌜(0 <= r)%Z -> d = 0%nat -> (0 < n)%Z -> dc = (d + 1)%nat⌝ -∗           (* :275 *)
      ...
      (⌜cons_window sl cur d bs hs⌝ ∗ ⌜cons_chain sl⌝
         ∗ cons_swallow cn (...) sl d dc
         ∗ (∃ (sl' ws : list (list mobs * bv 8)),                              (* :342 *)
              cons_stored_lb cn sl' ∗ ⌜sl `prefix_of` sl'⌝ ∗
              ⌜length sl' = (cur + dc)%nat⌝ ∗ ⌜length ws = dc⌝ ∗
              ⌜forall j : nat, (j < dc)%nat ->
                 ws !! j = sl' !! (cur + j)%nat⌝ ∗
              Rin ws)
       ∨ cons_dirty_cred Wd) -∗
```

The process pays the ring's payment and the input link; the kernel promises
the -1 exit is the `killed` test (so it carries the credential off
`proc_pub`'s row), the two cursor rows, and that on the clean arm the link
was fired at the consumed window.

#### 2.6.5 `WpUart` -- links, licences, `store_ob`

The port indexing and the invariant's two clauses (iris/WpUart.v:852, :894,
:944, :1052):

```coq
  Definition out_res_at (iu : uart_id) (k : nat) (ho : list mobs)
      (acc : list (bv 8)) : iProp Σ :=
    match iu with Uart0 => riscv_out_res k ho acc | Uart1 => emp end%I.
  Definition out_claim_at (iu : uart_id) (acc : list (bv 8)) : iProp Σ :=
    (∃ o : option (list mobs),
       obs_hist_lb_o o ∗ out_res_at iu (S gen_id) (default [] o) acc)%I.
  Definition in_res_at (iu : uart_id) (k : nat) (ho : list mobs)
      (pops : list ConsLog.log_entry)
      (dl : list (list mobs * bv 8)) : iProp Σ :=
    match iu with Uart0 => riscv_in_res k ho pops dl | Uart1 => emp end%I.
  Definition in_claim_at (iu : uart_id) (γ : uart_names) : iProp Σ :=
    (∃ (o : option (list mobs)) (pops : list ConsLog.log_entry)
       (dl : list (list mobs * bv 8)),
       obs_hist_lb_o o ∗ in_res_at iu (S gen_id) (default [] o) pops dl ∗
       uart_log_hi γ (1/2) (log_top pops) ∗ uart_deliv γ (1/2) dl ∗
       in_log_auth γ pops ∗ uart_logm γ (1/2) pops ∗
       ⌜ConsLog.log_ok pops⌝)%I.
```

The kernel's own port (`Uart1`) claims nothing.  The links (:1966, :2191,
:2216, :2307):

```coq
  Definition out_link (i : uart_id) (k : nat) (b : bv 8) (Φ : iProp Σ) : iProp Σ :=
    (∀ (o : option (list mobs)) (acc : list (bv 8)),
       obs_hist_lb_o o -∗ out_res_at i k (default [] o) acc
       ={⊤ ∖ ↑uartN i}=∗
       ∃ o' : option (list mobs),
         obs_hist_lb_o o' ∗ out_res_at i k (default [] o') (acc ++ [b]) ∗ Φ)%I.

  Definition in_append (k : nat) (h : list mobs) (c : bv 8) (cs : list (bv 8))
      (Φ : iProp Σ) : iProp Σ :=
    (∀ (o : option (list mobs)) (pops : list ConsLog.log_entry)
       (dl : list (list mobs * bv 8)),
       obs_hist_lb_o o -∗ in_res_at Uart0 k (default [] o) pops dl -∗
       ⌜forall e, e ∈ pops -> hist_ext (ConsLog.le_hist e) h⌝
       ={⊤ ∖ ↑uartN Uart0}=∗
       ∃ o' : option (list mobs),
         obs_hist_lb_o o' ∗
         in_res_at Uart0 k (default [] o') (pops ++ [(h, c, cs)]) dl ∗ Φ)%I.

  Definition echo_link (k : nat) (h : list mobs) (b : bv 8) (Φ : iProp Σ) : iProp Σ :=
    (∀ (o o' : option (list mobs)) (acc : list (bv 8))
       (pops : list ConsLog.log_entry) (dl : list (list mobs * bv 8)),
       obs_hist_lb_o o -∗ out_res_at Uart0 k (default [] o) acc -∗
       obs_hist_lb_o o' -∗ in_res_at Uart0 k (default [] o') pops dl -∗
       ⌜forall e, e ∈ pops -> hist_ext (ConsLog.le_hist e) h⌝ -∗
       ⌜obs_wire Uart0 (open_seg h) `prefix_of` acc⌝
       ={⊤ ∖ ↑uartN Uart0}=∗
       ∃ o'' : option (list mobs),
         obs_hist_lb_o o'' ∗ out_res_at Uart0 k (default [] o'') (acc ++ [b]) ∗
         obs_hist_lb_o o' ∗ in_res_at Uart0 k (default [] o') pops dl ∗ Φ)%I.

  Definition read_link (k : nat) (ws : list (list mobs * bv 8))
      (Φ : iProp Σ) : iProp Σ :=
    (∀ (o : option (list mobs)) (pops : list ConsLog.log_entry)
       (dl : list (list mobs * bv 8)),
       obs_hist_lb_o o -∗ in_res_at Uart0 k (default [] o) pops dl -∗
       ⌜ConsLog.read_ok pops dl ws⌝
       ={⊤ ∖ ↑uartN Uart0}=∗
       ∃ o' : option (list mobs),
         obs_hist_lb_o o' ∗
         in_res_at Uart0 k (default [] o') pops (dl ++ ws) ∗ Φ)%I.
```

`in_run k h c pre bs Φ` (:2290) is `in_append k h c pre Φ` at `bs = []` and
`in_append k h c pre Φ ∧ echo_link k h b (in_run k h c (pre ++ [b]) bs' Φ)`
otherwise -- chain-first, append-last, stoppable at every prefix.  The
kernel's promises inside the links: a writer's byte is appended to `acc`; an
appended log entry is above every logged history; the echo's link also sees
the wire at the byte's own history below `acc`; a read's window satisfies
`ConsLog.read_ok pops dl ws` (iris/ConsLog.v:73: every delivered entry is an
echoed log entry, `dl ++ ws` is a strictly increasing chain, and `gap_ok`
(:65): between consecutive consumed inputs every logged input got no echo or
an erase byte was logged).  The licences (:2110, :2372) are the generic
process's payment:

```coq
  Definition out_licence : iProp Σ :=
    (□ ∀ (k : nat) (h : list mobs) (acc : list (bv 8)) (b : bv 8),
        riscv_out_res k h acc ==∗ riscv_out_res k h (acc ++ [b]))%I.
  Definition in_licence : iProp Σ :=
    (□ (∀ (k : nat) (h : list mobs) (pops : list ConsLog.log_entry)
          (dl : list (list mobs * bv 8)) (e : ConsLog.log_entry),
          riscv_in_res k h pops dl ==∗ riscv_in_res k h (pops ++ [e]) dl)
     ∗ □ (∀ (k : nat) (h : list mobs) (pops : list ConsLog.log_entry)
            (dl ws : list (list mobs * bv 8)),
            riscv_in_res k h pops dl ==∗ riscv_in_res k h pops (dl ++ ws)))%I.
```

`store_ob` (:2646) is the THR leaf's premise, the kernel-internal ghost step
one level below `out_link` (built by `store_ob_of_out_link`, :2676, and by
`store_ob_of_echo_link`); it is what lets the write path and the echo path
share one transmit leaf.  `uart_rx_writer` (:1585) carries a third half,
`uart_log_hi`, the log's high-water history, beside the ring's.

#### 2.6.6 `UexecExecInst.xv6_ssupply` / `xfam` (iris/UexecExecInst.v:853, :219)

```coq
  (* OLD *) Definition xv6_ssupply : iProp Σ := app_sup.
  (* NEW *) Definition xv6_ssupply : iProp Σ :=
    (app_sup ∗ □ riscv_kill_cred ∗ □ out_licence ∗ □ in_licence)%I.
```

The generic user-execution slot runs on this; the kill conjunct is bought by
`Happ_kill`, the licences by `Happ_out_sup`/`Happ_in_sup`.  `xfam` gained,
LAST, `rf_in : list (list mobs * bv 8) -> iProp Σ` (:312), a process's chosen
`Rin` for row 5; `wf_Q : nat -> iProp Σ` (:245) serves both arms of row 16
(the trace-seed field is gone).  `xv6_sbundle` (:509) row 5 is a PLAIN deposit
`fileread_in (fd_st_of_key ...) (rf_F f) (rf_ret f) (rf_in f) True` (K4(a):
the console lease no longer rides the payload row); row 6 is `□ riscv_kill_cred`
(:560-569, B1: kill(2) costs the credential).

#### 2.6.7 `UexecRet` -- the trap deposit (iris/UexecRet.v)

```coq
Definition ukill_sc (sc : mword 64) : Prop :=                                (* :724 *)
  sc <> uecall_scause /\
  sc <> (mword_of_int 0x8000000000000009 : mword 64) /\
  sc <> (mword_of_int 0x8000000000000005 : mword 64).

  Definition ukill_cred_at (sc : mword 64) : iProp Σ :=                      (* :1402 *)
    (if decide (ukill_sc sc) then □ riscv_kill_cred else emp)%I.

  Definition uexec_kill_arm_F (X : uvis -d> iPropO Σ) (sc : mword 64)        (* :1317 *)
      (W : uvis) (f : sfam) : iProp Σ :=
    ((uexec_pay_arm f -∗ X W)
     ∨ (⌜ukill_sc sc⌝ ∗ ((uexec_pay_arm f -∗ X W) ∧ sexit_pay f (-1))))%I.
```

`uexec_dep_F`'s non-ecall branch is `ukill_cred_at sc` (:1441; OLD: nothing
there) and `uexec_ret_F`'s transparent arm is
`(ukill_cred_at sc ∗ uexec_kill_arm_F X sc W f)` (:1489; OLD
`(uexec_pay_arm f -∗ X W)`).  A process that traps at a cause usertrap kills
at (anything but the ecall and the two delegated S-mode interrupts) deposits
the credential; the U-tier store/load leaves refute the fault arm at
`uvis_lazy W = false` through LAZY-ROW's guard row in `uslot_F`,
`⌜uvis_lazy W = false -> lazy_free (ud_um pt) (uvis_sz W)⌝ -∗` (:1644).  The
-1 payload is a wand (K4(a)): `uexec_pay_arm f := upay_neg (sexit_pay f)`
(:836; OLD `sexit_pay f (-1)`), with
`UexecSlot.upay_neg Q := (□ riscv_kill_cred -∗ Q (-1))%I` (iris/UexecSlot.v:383),
and `upay_at` (:808) carries `upay_neg (sexit_pay f)` in all three branches
(OLD `sexit_pay f (-1)`).  `uexec_kill_arm_F` is SELF-KILL's INTERIM shape
(step 2); the owner's ruling (section 4) replaces its right arm.

#### 2.6.8 `SchedCtx.proc_pub` / `pid_tie` (iris/SchedCtx.v:222, :219)

```coq
  (* OLD *)
  Definition proc_pub (pa : mword 64) : iProp Σ :=
    (∃ (kl xs pid : mword 32),
       p_killed pa ↦₄ kl ∗ p_xstate pa ↦₄{DfracOwn (1/2)} xs ∗
       p_pid pa ↦₄{DfracOwn (1/4)} pid)%I.
  (* NEW *)
  Definition pid_tie (pid : mword 32) : iProp Σ :=
    (⌜bv_unsigned pid = 0⌝ ∨ ∃ gn : gname, pid_reg pid (DfracOwn qeighth) gn)%I.
  Definition proc_pub (pa : mword 64) : iProp Σ :=
    (∃ (kl xs pid : mword 32),
       p_killed pa ↦₄ kl ∗ p_xstate pa ↦₄{DfracOwn (1/2)} xs ∗
       p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
       (⌜kl = (mword_of_int 0 : mword 32)⌝ ∨ □ riscv_kill_cred) ∗
       pid_tie pid)%I.
```

`p->killed` is nonzero only against the credential (B2; kkill/setkilled take
it, sys_kill relays it out of row 6, killed() hands the row back --
`kill_paid kl`, :230); `pid_tie` (SELF-KILL 4a) says which generation the
slot's pid currently is, so a party holding a share of its own registration
learns the row it read is its own.

#### 2.6.9 `ChildTok.genF` (iris/ChildTok.v:98)

```coq
  (* OLD *)
  Definition genF : oFunctor :=
    prodOF (constOF (leibnizO (Values.mword 64 * Values.mword 32)))
           (Z -d> ▶ ∙).
  (* NEW *)
  Definition genF : oFunctor :=
    prodOF (constOF (leibnizO (Values.mword 64 * Values.mword 32 * gname)))
           (prodOF (Z -d> ▶ ∙) (prodOF (▶ ∙) (▶ ∙))).
```

A generation now records the alive token's gname `ga` (`alive_tok ga :=
own ga (Excl Alive)`, :157, camera `atokR := exclR (leibnizO alive_val)`,
:116), the incarnation's credential part `K` and the killer's payment `Kp`,
read by `gen_alive`/`kcred`/`kpay` (:216-222); `gen_fresh` (:591) is at
`K = Kp = emp` with the token; the derived readings (`gen_slot`, `gen_pid`,
`my_pay`, `child_tok`, `gen_kq`, `exit_tok`) keep their signatures.  SELF-KILL
step 3; per the owner's ruling the alive token and `K` are removed again in
4b'.

#### 2.6.10 `SlotGen.pid_reg_*` (iris/SlotGen.v:76, :290, :311)

```coq
Notation qeighth := ((1/4)/2)%Qp (only parsing).
  Lemma pid_reg_eighths pid g :
    pid_reg pid (DfracOwn (1/4)) g ⊣⊢
    pid_reg pid (DfracOwn qeighth) g ∗ pid_reg pid (DfracOwn qeighth) g.
  Definition pid_reg_rest pid g : iProp Σ :=
    (pid_reg pid (DfracOwn (3/4)) g ∗ pid_reg pid (DfracOwn qeighth) g)%I.
```

The block's quarter of a pid's registration is split so one eighth rides
`proc_pub`'s tie; `pid_reg_rest` names the seven eighths at the seven sites
that used to carry the whole (not allocproc).

## 3. What the owner has to accept

W = WEAKENING of the theorem; S = STRENGTHENING of an obligation (a new or
stronger hypothesis, discharged by echo); N = NEUTRAL plumbing; "vacuous" =
discharged at the `emp` placeholder; "promise" = a kernel post the kernel
proves.

| File | Statement | Lane | Rationale | Class |
|---|---|---|---|---|
| EchoDisc.v | `disc_pt`, `good_out`, `disc_seg'` on `obs_wire Uart0` alone; boot-message machinery gone | DISC-SIMPLIFY | owner's ruling: console UART only | W (by ruling) |
| SpecConsoleread.v, SpecFileread.v | rows B1/B4, `n` on `console_receipt`; `fileread_ret` at row 5's post | CONS-ROWS | the cursor's two control-flow facts | N (promise) |
| UexecRet.v | `uslot_F` guard row `uvis_lazy W = false -> lazy_free ...` | LAZY-ROW | a non-lazy program never page-faults | N (promise) |
| RiscvPtsto.v, RiscvAdequacy.v, App.v, SystemAdequacy.v | `riscv_kill_cred`, `Kc`; `app_kill`, `Hkillp/t`, `Happ_kill`, `Hkill_sup`; the equation on `Hinit_boot` | KILL-PAY B1 | the supply buys the kill price; echo's is the taint | S (discharged) |
| UexecExecInst.v | `xv6_ssupply` gains `□ riscv_kill_cred`; row 6 | KILL-PAY B1 | the generic slot pays kill(2) | S (generic slot) |
| SchedCtx.v, UexecRet.v | `proc_pub`'s row `⌜kl = 0⌝ ∨ □ riscv_kill_cred`; `ukill_sc`, `ukill_cred_at` in the deposit's transparent arm | KILL-PAY B2 | a kill, and a trap the kernel kills at, cost the credential | S (kill path; fault arms refuted) |
| SpecConsoleread.v, SpecFileread.v | `(⌜0 <= r⌝ ∨ □ riscv_kill_cred)`; -1 arm `(⌜n < 0⌝ ∨ □ riscv_kill_cred)`; exclusive `fileread_dev_env`; `d <= max 0 n` | KILL-PAY K4(b) | a -1 from read(0) says why | N (promise) |
| UexecSlot.v, UexecRet.v, UexecExecInst.v | `upay_neg`; `uexec_pay_arm := upay_neg (sexit_pay f)`; row 5 a plain deposit | KILL-PAY K4(a) | the -1 payload is a wand; the lease leaves the payload row | N |
| UInitBootAdequacy.v, UkSh.v | `sh_deps := udepw_law 16`; `Hsh_owed` loses `udepw_law 16` | SH-LINE 2b (a) | read(5) pays from the lease | N (theorem stronger) |
| RiscvPtsto.v, RiscvAdequacy.v | `riscv_out_res`, `out_res_triv`, `obs_hist_lb_cmp`, `Ores` | OUT-FUPD | the output claim is a resource | N (record slot) |
| App.v, SystemAdequacy.v | `app_out`, `Houtt`, `Happ_out_sup`, `Happ_echo`, `Hout_sup`; out equations; `app_xfer_boot_raw` yields `O [] []`; `Hecho`/`Hxfer`/`Hout_lic` | OUT-FUPD | every console store is justified by its writer | S (vacuous) |
| App.v | `Htx` gains `u_wire u = u_out u`, `ho prefix_of h`, the out claim taken and returned | OUT-FUPD | the only channel to `Hphi` | N (promise) |
| SpecConsoleintr.v, SpecConsolewrite.v, WpUart.v, UexecExecInst.v | `cons_echo_shift`; `cons_out_chain`; `out_link`/`out_chain`/`out_licence`; `xv6_ssupply` gains `□ out_licence`; `wf_Q`; retired `uart_sent_*`/`cons_sent_cnt`/`wcons_*`/`wf_tr0` | OUT-FUPD | writers bring justification, get no receipt | S (writers, generic slot) |
| UInitBootAdequacy.v | `Hsh_owed` = `sh_deps ∧ sh_pay_rest sh_Rsh`, `sh_pay_state` proved | SH-STATE | the family is fixed by the proof | N (theorem stronger) |
| EchoDisc.v | `disc_prefix`, `star_prefix_prefix`, periodicity lemmas | ECHO-PURE | lemmas only | N |
| RiscvPtsto.v, RiscvAdequacy.v | `riscv_in_res`, `in_res_triv`, `Ires` | CONS-IO A | the input log is a resource | N (record slot) |
| App.v, SystemAdequacy.v | `app_in`, `Hinpt`, `Happ_in_sup`, `Hin_sup`; in equations; `app_xfer_boot_raw A B O I`; `Htx`'s input claim at `hi`; `Hin_lic` | CONS-IO A | the shift files, read hands out, both licensed | S (vacuous) |
| SpecConsoleintr.v, WpUart.v, UexecExecInst.v | `cons_echo_shift` over `in_run`; `echo_link`, `in_append`, `in_licence`, `store_ob`, `in_claim_at`, `uart_log_hi`; `xv6_ssupply` gains `□ in_licence` | CONS-IO A | one fupd per accepted input; every arm logs | S (the shift) / N (internals) |
| SpecFileread.v, SpecConsoleread.v, UexecExecInst.v, WpUart.v | `fileread_in ... Rin`, `cons_read_pay`, `read_link`; `console_receipt`'s `Rin ws` row; consoleread's `uart_inv Uart0` premise; `xfam.rf_in` | CONS-IO B | the read side; `read_ok` is the kernel's pure fact | S (reader) / N (promise) |
| RiscvPtsto.v, App.v, RiscvAdequacy.v, SystemAdequacy.v, WpUart.v, Spec*.v | era index `k` on both resources, `app_out/in/boot`, every link and licence; `GenId` and `⌜obs_boots h = S gen_id⌝` on `Htx`/`Hrx`/`cons_echo_shift`; `Happ_boot : ∀ c k`; `Rb c gen` | CONS-IO C | a dead era's writer cannot pay the current era; the kernel stamps histories | N (index; promise) |
| UexecRet.v, ChildTok.v | `uexec_kill_arm_F`'s two-sided arm; `genF` with `ga`, `K`, `Kp`; `atokR` | SELF-KILL 2, 3 | interim; superseded in part by the ruling | N |
| SchedCtx.v, SlotGen.v | `pid_tie` in `proc_pub`; `qeighth`, `pid_reg_eighths`, `pid_reg_rest` | SELF-KILL 4a | the killed row learns whose row it is | N |

No row adds a hypothesis to `echo_adequacy_modulo_phi`; its statement moved
only by the two shrinkings of `Hsh_owed` and the seven extra arguments in
`Hphi`'s `boot_fixedGS` literal.

## 4. Open items that will touch the trusted surface

- SELF-KILL 4b'/4c (kernel; app-echo.md:55-68; the earlier plan in
  scratchpad `self-kill-4b-plan.md` is superseded in part).  The owner's
  ruling: the kill credential IS the target's exit payload at -1 -- "the
  process gname resource already tracks Q, and Q(-1) becomes the
  precondition for kill() of that PID"; no `K'`, no alive token, no `∧`, no
  -1 wand at ecalls.  4b': `ChildTok` simplified to `Q` + `kpay` (the taken
  token); `proc_pub`'s row becomes `kl = 0 ∨ kill_owed gn ∨ taken_tok gn`;
  `SpecKilled` as the one-shot accessor of the killed row; the killing-cause
  arm of `uexec_ret_F` is deposit-only (a process supplies `Q(-1)` where it
  may trap at a killing cause, the syscall precondition at the ecall cause);
  `upay_neg` and the -1 payload row are removed.  4c: B1's rollback --
  `riscv_kill_cred` leaves the fixed record, `app_kill`/`Hkillp`/`Hkillt`/
  `Happ_kill`/`Hkill_sup` and the `riscv_kill_cred = app_kill A c` equation
  leave App.v/SystemAdequacy.v, `xv6_ssupply` loses its second conjunct
  (app-echo.md, "RULINGS AFTER CONS-IO PHASE 1" (4)).
- CONS-IO milestone D -- ERA-TOK (scratchpad `brief-cons-io-6.md`,
  e5-design.md REVISION 7): `era_tok (k : nat) : iProp`, exclusive per
  generation (`era_tok k ∗ era_tok k ⊢ False`, unmintable twice for one `k`
  across the run), minted at the boot of generation `gen` as `era_tok (S gen)`
  and LENT TO INIT beside `app_boot c (S gen) r`; `App.Hinit_boot`'s premise
  gains `era_tok (S gen_id)` beside `app_boot A c (S gen_id) r`;
  `app_xfer_boot_raw` untouched.
- ECHO-OUT (scratchpad `brief-echo-out-3.md`, `echo-out-handover.md` §5):
  `echo_out`/`echo_in` replace the `emp` placeholders (three arms: taint,
  fresh, paired at the era index); `app_boot`'s payload gains the era's
  ghosts with full ownership, allocated in `echo_xfer_boot`'s bupd
  (REVISION 7 (b)); `echo_fixed` becomes a record of gnames; the four
  console obligations and `echo_Htx` re-proved at the real claims; the
  CONCLUSION restated, `echo_phi := fun _ h => disc h -> Forall good_out (cycles_of h)`,
  with `AppEcho.echo_phi_disc` and `EchoOutPure.echo_phi_of_good_out` deleted.
- IO-LEAF (e5-design.md REVISION 6, S10): sh's quiet write leaves are
  swapped for the chain leaf, so `sh_deps` is DELETED and `Hsh_owed`'s first
  conjunct disappears; the read leaf on `read_link`; the turn in the
  WAIT-EXIT payloads.  Then SH-LINE R2/R3 (`sh_pay_rest sh_Rsh`) and PHI
  (`Hphi`), after which `echo_adequacy_modulo_phi` has no named hypothesis
  beyond the image facts.
