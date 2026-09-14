# OPEN-ROW survey (2026-09-14; read-only; the lane was WITHDRAWN by the banner-optional ruling)

Kept as the map of the kernel's boot / park / syscall plumbing for a counted resource, should a kernel row ever be reopened (the `die_dw` question).  Paths were read in the -tlw checkout at 6fb3dbaa6.

Survey complete. All paths below are absolute; all quoted Coq is verbatim.

---

# 1. Boot: where the ftable is born, and how the proc-token rides to userinit

## 1a. `fileinit` call and the `is_ftable` creation — `/shared/xv6iris-2-tlw/iris/ProofMain.v`

The whole fs group is `mn_grp_fs` (`ProofMain.v:1565`), covering `main+0x8e .. 0xa2`. Its header comment (`ProofMain.v:37`) is `mn_grp_fs 0x8e -> 0xa2 binit iinit fileinit virtio_disk_init userinit`.

**The three raw ftable rows it takes** (`ProofMain.v:1720-1727`):

```coq
    lk_raw (mword_of_int KernelSyms.ftable) -∗
    (* THE OPEN-FILE TABLE'S HUNDRED ENTRIES, and the two ghost rows a FREE
       table costs beside them -- [SpecMain.main_globals_raw]'s three new
       rows.  They become [FileInv.ftable_res] at the [newlock] right after
       fileinit; see there. *)
    ([∗ list] k ∈ seq 0 NFILE, fentry_raw k) -∗
    iref_slots NFILE -∗
    fd_slots_auth -∗
```

plus `flive_own ((● ∅) : fliveUR)` at `ProofMain.v:1700` (bound as `Hfolauth` at `ProofMain.v:1768`).

**The `fileinit` call, `ProofMain.v:1924-1943`**:

```coq
    (* ---- +0x96 jal fileinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x96)) (mword_of_int 1 : mword 5)
              (mword_of_int 12790 : mword 21) mii n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    ...
    iApply (Fileinit.wp_fileinit_sconf F3 n vfl vfn vfc false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Hfw Hfn Hfc").
```

**The mint + `newlock`, `ProofMain.v:1955-1968`** — this is the site the ftable counted token must be minted beside:

```coq
    iIntros (mfi) "Hcg Hpc %Hcsfi Hftw Hftnm Hftc".
    iApply fupd_wp.
    iMod (ftable_res_boot ⊤ with "Hfolauth Hfents Hfdauth Hirfile") as (γf) "Hfres".
    (* A6.69: the honest creator deposit (A6.66) wants the running token;
       this proof holds the kernel bundle, so it borrows its own and puts
       it straight back ([SieCapCtx.sie_cap_gpr_own_ctx_acc]). *)
    iDestruct (sie_cap_gpr_own_ctx_acc with "Hcg") as "[Hrun Hcgb]".
    iMod (newlock ⊤ (mword_of_int KernelSyms.ftable : mword 64) "ftable"%string (ftable_res_at γf) with "Hftnm Hrun Hftw Hftc Hfres") as "[Hrun Hft0]".
    iDestruct ("Hcgb" with "Hrun") as "Hcg".
    iDestruct "Hft0" as (γft) "#Hftable".
    iModIntro.
    (* [is_ftable γft γf] is [Hftable] at [ftable_addr]'s spelling *)
    iAssert (is_ftable γft γf) as "#Hftable'".
    { rewrite /is_ftable /ftable_addr. iExact "Hftable". }
```

`γft` and `γf` are chosen **here** and nothing above constrains them; `mn_grp_fs`'s continuation returns them existentially (`ProofMain.v:1759-1762`):

```coq
        (* ...AND THE OPEN-FILE TABLE'S LOCK, which is fileinit's output plus
           the resource the carve now hands over.  The two gnames are this
           group's own choice and nothing above it constrains them. *)
        (∃ γft γf : gname, is_ftable γft γf) -∗
```

and the group discharges it at `ProofMain.v:2196-2198`: `iApply ("Hcont" $! fsc_dlock pd pav pu mui ...) ... iExists γft, γf. iExact "Hftable'".`

Note the ordering constraint you inherit: `ftable_res_boot` runs at `+0x96`'s **return**, i.e. *after* `fileinit`, and `userinit` is called at `+0x9e` — three instructions later, in the same group, with `γft`/`γf` already in hand. So a counted-ftable token minted at `ftable_res_boot` is trivially in scope at the userinit call site.

## 1b. The proc-side token mints — `/shared/xv6iris-2-tlw/iris/BootShared.v`

`BootShared.v:2095-2130` (inside `boot_shared_alloc`):

```coq
    iMod procs_avail_alloc as (Hpav) "Hprocscore".
    (* THE AUTHORITY IS KEPT NOW.  [FileInv.ftable_res] holds it -- the
       table is where the one-unit-per-reference conservation law is checked
       -- and nothing else in the tree can make it. *)
    iMod fd_slots_alloc as (Hfd) "[Hfdauth Hfdslots]".
    ...
    iMod iref_slots_alloc as (Hir) "[Hirauth Hirslots]".
    ...
    iMod bslots_alloc as (Hbs) "(Hbsauth & Hbsproc & Hbslots)".
    ...
    iMod WaitInv.children_res_alloc as (Hwch) "[Hchb Hnpend]".
    (* THE COUNTED PROC LEDGER, PAIRED UP (lane TRAP-ROWS-4, B1b): the
       authority came out of [procs_avail_alloc] above and the pid
       counter's boot-era token out of the line just above -- it lives at
       a name the [wchG] instance carries, so it can only be minted where
       that instance is.  Together they are the COUNTED regime, and the
       [true] index is what userinit's allocproc reads <init>'s pid off. *)
    iAssert (procs_avail_at (Some NPROC) true) with "[Hprocscore Hnpend]"
      as "Hprocsavail".
    { rewrite /procs_avail_at. iFrame "Hprocscore Hnpend". }
```

`boot_shared_alloc`'s postcondition row (`BootShared.v:1752-1765`):

```coq
      (* THE PROC TABLE'S COUNTED REGIME, at the whole table: every slot is
         UNUSED at boot, so allocproc cannot come back empty and a caller
         that does not test its result -- userinit -- can be proved
         ([ProcAvail.v], and [SpecUserinit.v]'s contract, which takes
         [procs_avail (Some (S k))] and hands back [Some k]).  Threaded to
         [main] through [BootChain.boot_hart_primary]; main carries it to
         the userinit call site. *)
      procs_avail_at (Some NPROC) true ∗
      (* THE CHILDREN MAP AND ITS NPROC ROWS, at the canonical name minted
         above -- see [WaitInv.children_res_alloc]. *)
      WaitInv.children_boot ∗
```

The mint itself (`/shared/xv6iris-2-tlw/iris/WaitInv.v:1878-1879`):

```coq
  Lemma children_res_alloc :
    ⊢ |==> ∃ _ : wchG Σ, children_boot ∗ SlotGen.nextpid_pend.
```

with `Xv6Cameras.npid_name` allocated at `WaitInv.v:1899-1903` (`own_alloc (Some (to_dfrac_agree (DfracOwn 1) ...) : ipidUR)`) and the instance packed at `WaitInv.v:1905`: `iExists (WchG Σ _ _ _ _ _ γ γo γsg γpr γip γnp).`

**The boot-chain relay**: `/shared/xv6iris-2-tlw/iris/BootChain.v:403-411`:

```coq
    (* the proc table's counted regime, straight through from
       [BootShared.boot_shared_alloc] to main -- see [SpecMain]'s own row *)
    procs_avail_at (Some NPROC) true -∗
    ...
    WaitInv.children_boot -∗
```

and `/shared/xv6iris-2-tlw/iris/SpecMain.v:642-654` (same two rows, same order, with the "SPENT at the userinit call" comment).

The three ftable rows in `main_globals_raw`: `/shared/xv6iris-2-tlw/iris/SpecMain.v:371-373` and `/shared/xv6iris-2-tlw/iris/BootShared.v:506,514,519`:

```coq
     ([∗ list] k ∈ seq 0 NFILE, fentry_raw k) ∗
     iref_slots NFILE ∗
     fd_slots_auth ∗
```

## 1c. How `Hpavail` rides the groups

`Hpavail` does **not** go through `mn_grp_kvm` or `mn_grp_trap` — it is bound at `wp_main_boot_sconf`'s top (`ProofMain.v:2455`) and passed straight into `mn_grp_fs`:

```coq
    iIntros "Hparks Hpst Hpavail Hchb Hfs Hmir Hirslot Hirauth #Hcert #Hseam".
```

`mn_grp_fs`'s premise (`ProofMain.v:1662-1670`):

```coq
    (* THE COUNTED PROC REGIME, carried to the userinit call site at +0x9e.
       [SpecUserinit.wp_userinit_sconf_body] -- userinit's REAL contract,
       which [ProofUserinit.v] proves -- takes [procs_avail (Some (S k))] and
       is what refutes allocproc's empty-table arm.  The WEAK contract this
       group actually applies ([SpecUserinit.USERINIT]) does not take it, so
       it is dropped at the call below; swapping the two contracts is then a
       local edit.  See claude-notes/projects/main-boot.md §G3. *)
    procs_avail_at (Some NPROC) true -∗
```

Group application, `ProofMain.v:2607-2617`:

```coq
    iApply (mn_grp_fs γp γs γv γd γw γtl m4 (K - 2)%nat p0 ps c0 free0 dk sb nib
              Pb Rspent
              Hn50 Hlen Hlive Hdevq Hnibpos Hcovpos Hnibq Hpures
              Huartq Hdiskq Hgeomok Hpkc
              with "Hcg Htext Hkdata Hdev Hwire Hbundle Hrdtok Htramp Hccaps Hu1caps Hcready Htl Hwaitlock
                    Hpenvc Hkmem Hcert Hseamc Hfolat Hoffa Hfirst
                    [Hpenv] Hpc Hfree Hcpu Hpinv Hpavail
                    Hpidlock Hkenv Hlbc Hbufl
                    Hbufn Hbhead Hbpay Hlit Hinl Hkit1 Hkit2
                    Hsbb Hlogr Hmir Hirslot Hirauth Hient
                    Hlft Hfents Hirfile Hfdauth Hldisk Hdiskptr Hdiskfree
                    Hdusedidx Hdslots Hclaim Hcmauth Hdone Hcfg Hinitproc Hipt").
```

`Hchb` (children_boot) instead goes into `mn_grp_kvm` (`ProofMain.v:2589`) after `<init>`'s pid cell is split off at `ProofMain.v:2461`:

```coq
    iDestruct (WaitInv.children_boot_split with "Hchb") as "[Hipt Hchb]".
```

## 1d. The userinit call site — `/shared/xv6iris-2-tlw/iris/ProofMain.v:2081-2192`

```coq
    (* one slot is all userinit needs, and NPROC of them is what boot minted *)
    iDestruct (procs_avail_le_at NPROC 1 true ltac:(unfold NPROC; lia)
                 with "Hpavail") as "Hpavail".
```

```coq
    iApply (Userinit.wp_userinit_sconf γp γs γft γf γw γtl pd pav pu F5 n false p0
              (avail_sub (avail_sub (Some (length ps)) K_kvmmake) 3)
              0%nat iv0 false ∅
              ltac:(lia) Hnb8 Hdevq Hnibq
              with "Hcg Hcpu Htext Hkdata Hpc Hpanic Hitl Hitinv Hesc Hireg
                    Hfirst Hpersist Hfsinit
                    Hpinv Hlpidlk Hdcaps Hwaitlk Hftable' Hcready Hwire Hbundle Hrdtok Htramp Hkenv
                    Hpavail Hinitproc Hipt").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mui) "Hcg Hpc %Hcsui Hcpu _ _ _".
```

Note `Hftable'` (`is_ftable γft γf`) is **already** a premise of userinit at this site.

---

# 2. `SpecUserinit.v` contract and `ProofUserinit.v`'s park

## 2a. The full contract — `/shared/xv6iris-2-tlw/iris/SpecUserinit.v:136-328`

```coq
Notation K_userinit := ((4 + K_namei_root_boot)%nat) (only parsing).

Definition wp_userinit_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}
    `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γp : gname) (γs : list gname)
    (* THE PARK'S NAMES: the open-file table's two gnames, the wait lock's,
       the ticks lock's, and the disk geometry's three words.  userinit
       reads none of them; they index the six persistent rows below, which
       the first process's trap-loop environment is assembled from at the
       park (SpecForkretParkPaid.v, UsertrapRes.park_env). *)
    (γft γf γw γtl : gname) (pd pav pu : mword 64)
    (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
    (on : option nat) (np : nat) (v0 : mword 64)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.userinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_userinit <= K)%nat ->
  (exists nb, on = Some nb /\ (K_allocproc < nb)%nat) ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
             icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ireg_reg fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  first_addr ↦₄ (mword_of_int 1 : mword 32) -∗
  first_boot_persist -∗
  first_fsinit -∗
  procs_inv γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at -∗
  devintr_caps_any fsc_uart fsc_disk fsc_dlock γtl γs pd pav pu -∗
  is_lock γw wait_lock_addr "wait_lock"%string (wait_res_at) -∗
  is_ftable γft γf -∗
  SpecFileread.console_ready_app -∗
  wire_inv -∗
  init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0 -∗
  ConsoleInv.cons_reader fsc_cons 0%nat -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  kalloc_env_at fsc_kalloc fsc_kpages on -∗
  procs_avail_at (Some (S np)) true -∗
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0 -∗
  SlotGen.init_pid_tok (mword_of_int 0 : mword 32) -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ mf : regfile,
      sie_cap_gpr KT1 mf K b pj -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf
        /\ mf !!! Regidx (mword_of_int 1 : mword 5)
           = (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) ⌝ -∗
      cpu_own 0%nat eb pj b lks -∗
      kalloc_env_at fsc_kalloc fsc_kpages None -∗
      procs_avail None -∗
      (∃ v : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈□ v ∗
         WaitInv.init_gen v (mword_of_int 1 : mword 32)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
```

(I elided only the interleaved comment blocks; every premise and every post conjunct is above, in order.)

Module type, `SpecUserinit.v:318-328`:

```coq
Module Type USERINIT.
  Parameter wp_userinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}
      `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γp : gname) (γs : list gname)
      (γft γf γw γtl : gname) (pd pav pu : mword 64)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
      (on : option nat) (np : nat) (v0 : mword 64)
      (b : bool) (lks : gset string),
      wp_userinit_sconf_body γp γs γft γf γw γtl pd pav pu m K eb pj on np v0 b lks.
End USERINIT.
```

Important header note at `SpecUserinit.v:64-68`:

```
   THE FTABLE'S GNAME DOES NOT APPEAR.  allocproc's post mentions it (in
   [ProcInv.proc_priv_nocwd]) and so does [FORKRET_PARK], but the block
   userinit hands over has every descriptor null, so nothing about the open
   file table is observable in this contract; the proof instantiates both
   callees at one arbitrary name.
```

(It is stale w.r.t. the binder list, which *does* carry `γft γf`; but it tells you the ftable is currently observationally inert in this contract, which is exactly what your new token changes.)

## 2b. The park — `/shared/xv6iris-2-tlw/iris/ProofUserinit.v`

Ordered sequence at the park:

| line | step |
|---|---|
| `ProofUserinit.v:503` | `iMod (SlotGen.init_pid_seal with "Hipt") as "#Hipis".` |
| `ProofUserinit.v:769` | `iMod (kalloc_env_at_seal with "Hkenv") as "#Hkenv".` |
| `ProofUserinit.v:789` | `iDestruct (kalloc_env_at_avail with "Hkenv") as "#Hkav".` |
| `ProofUserinit.v:791` | `iDestruct (first_boot_intro with "Hfirst Hpersist Hkav Hfsinit") as "Hfb".` |
| `ProofUserinit.v:817` | `iDestruct (WaitInv.init_gen_reg (proc_addr j) with "Higl") as "#Hir".` |
| `ProofUserinit.v:819` | `iMod (procs_avail_seal_spent ⊤ np with "Hir Hpav") as "#Hpav".` |
| `ProofUserinit.v:846-848` | `pose (N := MkUtNames γft γf γw γs j γl pd pav pu γtl iv1 DfracDiscarded ks pid).` |
| `ProofUserinit.v:851` | `iAssert (park_env N) as "#Henv".` |
| `ProofUserinit.v:884` | `iAssert (park_own N) with "[Hbsl]" as "Hown".` |
| `ProofUserinit.v:889` | `iPoseProof (FP.park_token_intro γs) as "#Htoken".` |
| `ProofUserinit.v:905-911` | the park itself |

The park call, verbatim `ProofUserinit.v:905-911`:

```coq
    iMod (park_token_park N rest
            (MkUstate (upd_cwi (upd_cwd V ipv) (bv_unsigned InodeInv.ROOTINO)) M) fdt0
            ∅ Hwf Hrest
            with "Hrun Htoken Htext Hwire Htramp Hmk Hstack Henv Hown Hfrag Hrow Hbundle
                  Hrdtok [Hks Hctx Hpriv Hkq Hgh Hxb Hfd Hirs]")
      as "[Hrun Hpctx]".
```

and the `park_child` construction it feeds, `ProofUserinit.v:914-923`.

## 2c. What linear resources the park puts into the parked process's payload

Three distinct channels. This is the crux of your question.

### (i) `park_child` — rows handed straight to the cap, **not** captured by any closer

`/shared/xv6iris-2-tlw/iris/ParkCap.v:284-317`:

```coq
  Definition park_child `{XI : CurCtx} (γs : list gname) (γf : gname) (pa ks : mword 64)
      (rest : list (mword 64)) (pid : mword 32) (U : ustate) (steady : bool) : iProp Σ :=
    (is_kstack pa ks ∗
     ctx_cells (p_context pa) (park_forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) ∗
     (if steady then proc_priv γf pa pid U
      else proc_priv_nocwd γf pa pid U
           ∗ cwd_ref_at (pv_cwd (us_V U)) (pv_cwi (us_V U))
           ∗ first_boot
           ∗ gen_kq (pv_gen (us_V U)) pa pid (fun _ => True)%I
           ∗ my_pay (pv_gen (us_V U)) (fun _ => True)%I
           ∗ gen_halves_priv pa pid (pv_gen (us_V U))
           ∗ (∃ xsv : mword 32, p_xstate pa ↦₄{DfracOwn (1/2)} xsv)) ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE)%I.
```

`FirstTok.first_boot` (`/shared/xv6iris-2-tlw/iris/FirstTok.v:546-548`) is the **existing precedent for carrying a linear boot resource into a parked process**:

```coq
  Definition first_boot : iProp Σ :=
    (first_addr ↦₄ (mword_of_int 1 : mword 32)
       ∗ first_boot_persist ∗ kalloc_avail fsc_kpages None ∗ first_fsinit)%I.

  Definition first_tok : iProp Σ :=
    (first_boot
     ∨ (first_addr ↦₄□ (mword_of_int 0 : mword 32) ∗ fs_ready ∗ fsabs_env))%I.
```

`first_tok` rides **inside `ProcInv.proc_priv`**, and `first_fsinit` is a wholly exclusive resource pile. But it is **consumed by forkret's boot arm**, not by a syscall.

### (ii) `park_pkg` — the package's own rows and the closer

`/shared/xv6iris-2-tlw/iris/ParkCap.v:96-283`. The BOOT mode's linear payload row (`ParkCap.v:186-190`):

```coq
     (match Wk with
      | Some _ => first_done
      | None => init_boot_bundle cw sts ∗ cons_reader fsc_cons 0%nat
      end) ∗
```

Then `▷ (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (U' : ustate), ... -∗ (URB h Xc pt' (add_vec ks (mword_of_int 4096)) U' sts cs pid ∗ match Wk with | Some _ => uslot (uvis_of U' sts gn cs pid) | None => emp end))` (`ParkCap.v:192-283`).

### (iii) `park_env` / `park_own` — the channel `park_chan` turns into the closer

`/shared/xv6iris-2-tlw/iris/UsertrapRes.v:2239-2242`:

```coq
Definition park_env `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
                      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{XI : CurCtx}
    (N : ut_names) : iProp Σ :=
  (ut_park_caps N ∗ sysc_park_extra (un_tk N))%I.
```

— **entirely persistent** (`UsertrapRes.v:2244-2249`).

`/shared/xv6iris-2-tlw/iris/UsertrapRes.v:1195-1197`:

```coq
  Definition park_own (N : ut_names) : iProp Σ :=
    (bslots 3 ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N))%I.
```

— **two rows, both trivially linear-ish**: `bslots 3` and a `DfracDiscarded` cell share. This is the only linear channel that reaches the residue via the park channel.

`ut_park_intro_body`, `/shared/xv6iris-2-tlw/iris/UsertrapRes.v:2263-2302` (the shape `park_chan` mirrors row for row):

```coq
Definition ut_park_intro_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId}
    (URB : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> gset gname -> mword 32 -> iProp Σ)
    (W : iProp Σ)
    (N : ut_names) (av : nat) : Prop :=
  ut_wf N ->
  (K_usertrap <= av)%nat ->
  ⊢ ∀ ξp : CtxId,
    park_env (XI := ξp) N -∗
    park_own (XI := ξp) N -∗
    (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (U' : ustate) (sts' : list fdstate) (cs' : gset gname),
       ⌜pv_upt (us_V U') = pt'⌝ -∗
       park_globals Xc (un_s N) (un_w N) (un_ft N) (un_f N) (un_tk N) -∗
       ut_tfk (CID := h) (add_vec (un_ks N) (mword_of_int 4096)) (us_V U') -∗
       FirstTok.first_done (XI := Xc) -∗
       W -∗
       timer_cap (CID := h) -∗
       ut_trap_parked (CID := h) (XI := Xc) (un_pj N)
         (add_vec (un_ks N) (mword_of_int 4096)) av ∅ -∗
       proc_priv_nopt (XI := Xc) (un_f N) (un_pj N) (un_pid N) (us_V U') -∗
       fd_slots FDSPARE -∗
       iref_slots IREFSPARE -∗
       fd_frags (pv_fdg (us_V U')) sts' -∗
       ch_frag (pv_chg (us_V U')) (un_pj N) cs' -∗
       URB h Xc pt' (add_vec (un_ks N) (mword_of_int 4096)) U' sts' cs'
         (un_pid N)).
```

And the target residue's exclusive half, `/shared/xv6iris-2-tlw/iris/UsertrapRes.v:802-853`:

```coq
  Definition ut_own (Rsys : gname -> mword 64 -> fclose_names -> iProp Σ)
      (N : ut_names) (U : ustate) (sts : list fdstate) (cs : gset gname) (pid : mword 32) : iProp Σ :=
    (bslots 3 ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N) ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     proc_priv (un_f N) (un_pj N) pid U ∗
     fd_frags (pv_fdg (us_V U)) sts ∗
     ch_frag (pv_chg (us_V U)) (un_pj N) cs ∗
     Rsys (un_f N) (un_pj N) (un_fn N pid))%I.
```

### Answer to "how can a linear resource owned at userinit's park reach a SYSCALL of that process later?"

**Three routes exist, and two of them are closed for a counted ftable token:**

1. **Via `Rsys` = `ProofSyscall.syscall_env`** — **CLOSED.** `syscall_env` is fully persistent. `/shared/xv6iris-2-tlw/iris/ProofSyscall.v:267`: "``syscall_env` is FULLY PERSISTENT (every conjunct is)`"; `ProofSyscall.v:1038`: "`[syscall_env] is entirely persistent, so a second process's copy costs nothing`". Confirmed by the definition (`ProofSyscall.v:915-940`, all six conjuncts persistent). A counted (linear) token cannot live there.

2. **Via `park_own` → `ut_own`'s explicit rows** — **OPEN, and it is the precedent.** `park_own N = bslots 3 ∗ initproc-share` (`UsertrapRes.v:1195-1197`) is exactly "a linear resource the parker owns, handed through the park channel, landing in `ut_own` (`UsertrapRes.v:804-805`) and threaded into `wp_syscall_sconf_body`'s premise list as `bslots 3` (`SpecSyscall.v:766`) and back out (`SpecSyscall.v:1010`)". A counted ftable token added as a row of `park_own`/`ut_own` reaches the dispatcher the same way `bslots 3` does, and the open arm forwards it exactly as it forwards `Hbs` (`ProofSyscall.v:7397`, `ProofSyscall.v:7405`).

3. **Via `proc_priv`'s `FirstTok.first_tok`** — **OPEN but wrong-shaped.** `first_boot` carries linear rows into the parked block, but its consumer is forkret's `if (first)` arm, which converts the whole token into the persistent `first_done` arm. Anything left in `first_boot` after forkret runs is gone.

So: **the counted-ftable token should ride `park_own` / `ut_own` (and hence `wp_syscall_sconf_body`'s premise list) — not `syscall_env`, not `first_tok`.** Alternatively it can ride the `park_pkg` BOOT-mode row beside `init_boot_bundle` (`ParkCap.v:186-190`) if forkret is to spend it, but the two `open` calls happen from *user mode after forkret returns*, so the residue is the right home.

## 2d. Where the U-tier program's own frame lives

**It is completely invisible to the kernel.** There is no separate user WP: both tiers are `WP (Loop : expr riscv_lang)`. A user-tier leaf's continuation is a plain wand into that WP, so everything the program holds is framed by the Iris frame rule across the ecall and never appears in any kernel contract.

`/shared/xv6iris-2-tlw/iris/UkRun.v:896-970` — `urun` is the program's between-instruction bundle (existentially hiding `xi C pt Rfd Rut sz M pm fdv cw gn cs pidv`), carrying `uheap`, `ustack`, `ufd_auth`, `ucwd_auth`, `urun_ids`, `my_pay`, `udep`, `uvb`.

`/shared/xv6iris-2-tlw/iris/UkRun.v:334-338`:

```coq
  Definition udep : iProp Σ :=
    (□ Dsup ∗
     ⌜ forall (n : Z) (W : uvis) (Q : Z -> iProp Σ),
         psok n -> n <> USYS_exec ->
         ⊢ □ Dsup ==∗ sbundle_pay uslot n Q W ⌝)%I.
```

— persistent, so `udep` is not a frame-crossing linear resource.

The open ecall leaf, `/shared/xv6iris-2-tlw/iris/UkRunSys.v:831-851`:

```coq
  Lemma wp_uk_ecall_open (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_open -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat⌝ ∗
           ualloc (ukn_fd N) l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l)) -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
```

Anything the program holds beyond `urun`/`udepw`/`ustd` sits in the caller's frame across this wand and is invisible to everything on the kernel side. What *does* cross explicitly is the **deposit**, `sbundle_at uslot n f (uvis_of U sts gn cs pid)` — minted by `udepw_mint` (`UkRunSys.v:857`) and read by the kernel as `SpecSyscall.sysc_sys_in` / `SpecUsertrap.ut_sys_in`.

Note that the open leaf's two arms are `fd` (with `fd < NOFILE`) or `-1`. **A U-tier program cannot refute `-1` today** — the kernel's `filealloc` "table full" arm is what produces it (`/shared/xv6iris-2-tlw/iris/SpecFilealloc.v:70-72`):

```coq
  Definition filealloc_post `{XI : CurCtx} (γf : gname) (r : mword 64) : iProp Σ :=
    (⌜r = (zero_reg : mword 64)⌝ ∗ fd_slot
     ∨ ∃ k : nat,
         ⌜(k < NFILE)%nat /\ r = fnode k⌝ ∗ file_ref γf k 1 FdClosed)%I.
```

This is the `ProcAvail`-analogue: the counted-ftable regime you are building would refute the left disjunct exactly as `procs_avail (Some (S k))` refutes `allocproc`'s empty-table arm.

---

# 3. Syscall dispatcher rows and the open arm

## 3a. `sysc_init_id` — `/shared/xv6iris-2-tlw/iris/SpecSyscall.v:212-215`

```coq
Definition sysc_init_id `{!riscvGS Σ, !xv6G Σ, !wchG Σ} `{GEN : GenId} `{XI : CurCtx}
    (dqi : dfrac) (ip : mword 64) : iProp Σ :=
  ((mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip ∗
   WaitInv.init_ident ip)%I.
```

## 3b. `ut_caps` / `ut_park_caps` / `park_world`

`ut_caps`, `/shared/xv6iris-2-tlw/iris/UsertrapRes.v:658-705` — 19 conjuncts + one pure, all persistent:

```coq
  Definition ut_caps (N : ut_names) : iProp Σ :=
    (procs_inv (un_s N) ∗
     kernel_data ∗
     is_kstack (un_pj N) (un_ks N) ∗
     devintr_caps_any (fsc_uart) (fsc_disk) (fsc_dlock) (un_tk N) (un_s N)
       (un_pd N) (un_pav N) (un_pu N) ∗
     printk_env (fsc_printk) (fsc_uart) (fsc_disk) ∗
     is_lock (un_w N) wait_lock_addr "wait_lock"%string (wait_res_at) ∗
     is_ftable (un_ft N) (un_f N) ∗
     is_lock (fsc_kalloc) (mword_of_int KernelSyms.kmem) "kmem"%string
       (λ ξ : CtxId, kmem_res (XIk := ξ) (fsc_kpages) (mword_of_int (KernelSyms.kmem + 24))) ∗
     is_lock (fsc_dlock) d_lock "virtio_disk"%string
       (disk_res_at (fsc_disk) (un_pd N) (un_pav N) (un_pu N)) ∗
     bio_ctx (fsc_bio) (fs_view fsc_fs (fsc_disk) icfg_dev fsc_cov) ∗
     log_ctx icfg_log (fsc_bio) fsc_fs fsc_cov fsc_logst icfg_dev ∗
     fs_crash_seam fsc_cov fsc_logst ∗
     gen_cert ∗
     dev_inv (fsc_uart) (fsc_disk) ∗
     disk_geom (fsc_disk) (un_pd N) (un_pav N) (un_pu N) ∗
     kalloc_avail (fsc_kpages) None ∗
     FsReady.fs_ready ∗
     park_world (un_s N) ∗
     WaitInv.init_gen (un_ip N) (mword_of_int 1 : mword 32) ∗
     ⌜un_dqi N = DfracDiscarded⌝)%I.
```

`ut_park_caps`, `/shared/xv6iris-2-tlw/iris/UsertrapRes.v:746-768`:

```coq
  Definition ut_park_caps (N : ut_names) : iProp Σ :=
    (⌜un_dqi N = DfracDiscarded⌝ ∗
     procs_inv (un_s N) ∗
     is_kstack (un_pj N) (un_ks N) ∗
     devintr_caps_any (fsc_uart) (fsc_disk) (fsc_dlock) (un_tk N) (un_s N)
       (un_pd N) (un_pav N) (un_pu N) ∗
     is_lock (un_w N) wait_lock_addr "wait_lock"%string (wait_res_at) ∗
     is_ftable (un_ft N) (un_f N) ∗
     disk_geom (fsc_disk) (un_pd N) (un_pav N) (un_pu N) ∗
     park_world (un_s N) ∗
     WaitInv.init_gen (un_ip N) (mword_of_int 1 : mword 32))%I.
```

`park_world`, `/shared/xv6iris-2-tlw/iris/SyscParkEnv.v:115-164` — note `procs_avail None` sits *inside* it (line 127), i.e. the sealed proc ledger is what the trap loop carries, and `sysc_park_extra` (`SyscParkEnv.v:80-91`) carries the same row at line 82:

```coq
  Definition sysc_park_extra (γtk : gname) : iProp Σ :=
    ((∃ γp : gname, is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at) ∗
     procs_avail None ∗
     is_tickslock γtk ∗
     console_ready_app)%I.
```

`ut_names`, `/shared/xv6iris-2-tlw/iris/UsertrapRes.v:479-511` — fields `un_ft` (ftable.lock gname), `un_f` (the open-file table gname), `un_w`, `un_s`, `un_j`, `un_l`, `un_pd`, `un_pav`, `un_pu`, `un_tk`, `un_ip`, `un_dqi`, `un_ks`, `un_pid`. **There is no free/unused gname field.**

`park_globals`, `/shared/xv6iris-2-tlw/iris/UsertrapRes.v:2043-2060` — eight persistent rows including `is_ftable (XI := ξ) γft γf`.

## 3c. The family record `f : sfam`

`sfam` is a **field of the `uexecSG Σ` class**, `/shared/xv6iris-2-tlw/iris/UexecSG.v:268-272`:

```coq
Class uexecSG (Σ : gFunctors) {sg_ctok : ctokG Σ} := {
  sfam : Type;
  sfam_pt : sfam;
  sfork_pay : sfam -> Z -> iProp Σ;
  sfork_lend : sfam -> iProp Σ;
  sfam_pay : (Z -> iProp Σ) -> iProp Σ -> sfam;
  ...
```

The concrete instantiation is the record `xfam`, `/shared/xv6iris-2-tlw/iris/UexecExecInst.v:219-...`; the open fields are `UexecExecInst.v:232-239`:

```coq
    of_P     : nat -> Z -> iProp Σ;
    of_Pmiss : nat -> Z -> iProp Σ;
    of_Farm  : pfam Σ (aview -> Z -> iProp Σ);
    of_Fun   : pfam Σ (aview -> Z -> iProp Σ);
    of_Fok   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    of_Fex   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    of_Fo    : pfam Σ (aview -> Z -> anode -> iProp Σ);
    of_Ft    : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ);
```

The deposit / post rows, `/shared/xv6iris-2-tlw/iris/SpecSyscall.v:378-383` and `412-422`:

```coq
  Definition sysc_sys_in (U : ustate) (sts : list fdstate) (gn : gname)
      (cs : gset gname) (pid : mword 32) (f : sfam)
      : iProp Σ :=
    (∀ n : Z,
       ⌜sysc_num (us_V U) = n /\ n <> USYS_exit /\ n <> USYS_fork⌝ -∗
       sbundle_at uslot n f (uvis_of U sts gn cs pid))%I.
```

```coq
  Definition sysc_sys_out (U : ustate) (sts : list fdstate) (gn : gname)
      (cs : gset gname) (pid : mword 32) (f : sfam)
      (r : mword 64) (M' : gmap Z (bv 8)) (sts' : list fdstate) (cw' : Z)
      (cs' : gset gname)
      : iProp Σ :=
    (∀ n : Z,
       ⌜sysc_num (us_V U) = n /\ n <> USYS_exit /\ n <> USYS_fork⌝ -∗
       spost_at uslot n f (uvis_of U sts gn cs pid) r M' sts' cw' cs')%I.
```

Trap-loop-side twins: `/shared/xv6iris-2-tlw/iris/SpecUsertrap.v:485-499` (`ut_sys_in`) and `SpecUsertrap.v:517-530` (`ut_sys_out`).

## 3d. The dispatcher's per-process rows — `sysc_arm_pre`

`/shared/xv6iris-2-tlw/iris/ProofSyscall.v:1627-1670`:

```coq
  Definition sysc_arm_pre `{CIDh : CpuId} (γf : gname) (γw : gname)
      (pj : mword 64) (γs : list gname)
      (fn : fclose_names) (dqi : dfrac) (ip : mword 64) (pid : mword 32)
      (U : ustate) (sts : list fdstate) (cs : gset gname)
      (lks : gset string) (av : nat) (M : regfile)
      (tgt : mword 64) :=
    (pc_is tgt ∗
     sie_cap_gpr KT1 M av true pj ∗
     cpu_own 0%nat true pj true lks ∗
     kernel_text ∗
     procs_inv γs ∗
     syscall_env γf pj fn ∗
     bslots 3 ∗
     sysc_init_id dqi ip ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     proc_priv γf pj pid U ∗
     fd_frags (pv_fdg (us_V U)) sts ∗
     ch_frag (pv_chg (us_V U)) pj cs ∗
     is_lock γw wait_lock_addr "wait_lock"%string (wait_res_at))%I.
```

`syscall_env`, `/shared/xv6iris-2-tlw/iris/ProofSyscall.v:915-940`:

```coq
  Definition syscall_env
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId}
      (γf : gname) (pj : mword 64) (fn : fclose_names)
      : iProp Σ :=
    (sysc_proc_env γf ∗ SpecFileread.console_ready_app ∗ sysc_fs_env pj fn ∗
     FirstTok.first_done ∗
     park_world (fcn_procs fn) ∗
     park_token (fcn_procs fn))%I.
```

`sysc_proc_env`, `ProofSyscall.v:904-913`:

```coq
  Definition sysc_proc_env
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId}
      (γf : gname) : iProp Σ :=
    (∃ (γp γw γft γtk : gname),
       is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at ∗
       procs_avail None ∗
       is_lock γw wait_lock_addr "wait_lock"%string (wait_res_at) ∗
       is_ftable γft γf ∗
       is_tickslock γtk)%I.
```

Its producer `syscall_env_park` is `ProofSyscall.v:1002-1011` — note it asks for no linear row at all.

`sysc_fs_env`, `ProofSyscall.v:637-666`.

## 3e. The open arm: what it hands `wp_sys_open`

`sysc_arm_open` is `/shared/xv6iris-2-tlw/iris/ProofSyscall.v:7296-7302`; the call is `ProofSyscall.v:7391-7410`:

```coq
      iApply (SysOpen.wp_sys_open γft γf γs j γl
                (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) IREFSPARE
                DfracDiscarded DfracDiscarded DfracDiscarded DfracDiscarded
                v0 v1 pid U sts M (av - 4)%nat true true ∅
                (of_P fdep) (of_Pmiss fdep)
                (* create's child legs, at the process's families too
                   (round E2, lane E2-C) *)
                (of_Farm fdep) (of_Fun fdep)
                (of_Fok fdep) (of_Fex fdep)
                (of_Fo fdep) (of_Ft fdep)
                ltac:(lia) Hroot Hnib0 Hlg Hsize Hbm0 Hbmc
                Hbml Hist0 Hcb Hbmgeo Hib Hn1 Hn2 Hn3 Hn4 Hprg
                ltac:(compute; lia) Hj Hgamma eq_refl Hv0 Hv1
                with "Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hftable Hbio Hlog
                      Hseam Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2
                      Hireg Hropen Hsbn Hisp Hsbs Hbmp Hbmr Hkalloc Hprocs Hir
                      Hfd0 Hpriv Hufrag [Hxin]").
      { iApply (sysc_dep_open U sts gn cs pid fdep v0 v1
                  ltac:(rewrite Hnum; reflexivity) Hv0 Hv1 with "Hxin"). }
```

**Arguments, in order:**

| position | value | meaning |
|---|---|---|
| `γfl γf` | `γft γf` | ftable lock gname, ftable ghost — **taken off `syscall_env_all` at `ProofSyscall.v:7321-7322`** |
| `gs j gl` | `γs j γl` | proc array, running slot index, that slot's lock |
| `pd pav pu` | `(fcn_pd fn) (fcn_pav fn) (fcn_pu fn)` | virtio ring pages |
| `ns` | `IREFSPARE` | iref ledger |
| `dqb dqs dqbs dqn` | 4× `DfracDiscarded` | the four superblock cells' shares |
| `v vom` | `v0 v1` | syscall args 0 and 1 (path, omode) — read off `pv_tf` at `ProofSyscall.v:7318-7321` |
| `pid U sts` | | block index, entry record, entry descriptor states |
| `m K eb` | `M (av - 4)%nat true` | |
| `b lks` | `true ∅` | |
| `P Pmiss Farm Fun Fok Fex Fo Ft` | `of_P fdep` … `of_Ft fdep` | **the process's own deposited families** |

**Resources, in order** (`Hcg Hcpu Htcx Hccx Htext Hdata Hpc Hpr Hftable Hbio Hlog Hseam Hgen Hdevi Hgeom Hdlock Hbs Hit Hitinv Hesc Hsl2 Hireg Hropen Hsbn Hisp Hsbs Hbmp Hbmr Hkalloc Hprocs Hir Hfd0 Hpriv Hufrag [Hxin]`) matching `wp_sys_open_frame`'s premise list at `/shared/xv6iris-2-tlw/iris/SpecSysOpen.v:1484-1519`:

```coq
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  is_ftable γfl γf -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  ireg_open -∗
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv gs -∗
  iref_slots ns -∗
  fd_slot -∗
  proc_priv γf pj pid U -∗
  fd_frags (pv_fdg (us_V U)) sts -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
```

`fd_slot` is split out of `FDSPARE` at `ProofSyscall.v:7337`: `iDestruct (fd_slots_split 1 3 with "Hfd") as "[Hfd0 Hfd]".` — **this is the natural place a counted ftable token would be split/threaded too.**

`wp_sys_open_frame`'s return (`SpecSysOpen.v:1520-1544`): binds `(mf, ns', P')`, gives back `bslots 3`, the four sb cells, `⌜ns' = ns⌝`, `iref_slots ns'`, and `ARMS (us_upt U P') (mf !!! Regidx (mword_of_int 10 : mword 5))`.

The intermediate assertion the dispatcher builds around it (`ProofSyscall.v:7346-7386`) lists the arms split by `open_arms_split`:

```coq
        (∃ (UW' : ustate) (sts' : list fdstate),
           ⌜(mf !!! Regidx (mword_of_int 10 : mword 5)
               = (mword_of_int (-1) : mword 64)
             /\ UW' = us_upt U P' /\ sts' = sts)
            \/ (exists (fd : nat) (l : list nat) (k : nat) (rb wb : bool)
                       (t : fdtype),
                  mf !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int (Z.of_nat fd) : mword 64)
                  /\ fd_frees (pv_ofile (us_V (us_upt U P'))) = fd :: l
                  /\ UW' = us_ofile (us_upt U P') fd (fnode k)
                  /\ sts !! fd = Some FdClosed
                  /\ sts' = <[fd := FdOpen rb wb t]> sts)⌝
           ∗ proc_priv γf (proc_addr j) pid UW'
           ∗ fd_frags (pv_fdg (us_V (us_upt U P'))) sts'
           ∗ fd_slot
           ∗ open_receipt (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U))
               (us_M U) v0 v1
               (of_P fdep) (of_Pmiss fdep) (of_Farm fdep) (of_Fun fdep)
               (of_Fok fdep) (of_Fex fdep) (of_Fo fdep) (of_Ft fdep) sts
               (mf !!! Regidx (mword_of_int 10 : mword 5)) sts') -∗
```

**Left disjunct is `-1`.** This is the arm a counted ftable regime must be able to refute.

## 3f. What the syscall returns to the trap loop

`/shared/xv6iris-2-tlw/iris/SpecSyscall.v:708-1037` — `wp_syscall_sconf_body`. Premises (spatial), in order: `is_lock γw …` , `sie_cap_gpr`, `cpu_own`, `kernel_text`, `kernel_data`, `pc_is pcE`, `procs_inv γs`, `bslots 3`, `sysc_init_id dqi ip`, `fd_slots FDSPARE`, `iref_slots IREFSPARE`, `R γf pj fn`, `proc_priv γf pj pid U`, `fd_frags (pv_fdg (us_V U)) sts`, `ch_frag (pv_chg (us_V U)) pj cs`, `sysc_sys_in U sts gn cs pid f`, `sysc_fork_in f U sts`, `sysc_pay_in f U`.

Conclusion (`SpecSyscall.v:832-1037`) is an **additive conjunction**:

```coq
  (wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (U' : ustate) (sts' : list fdstate) (cs' : gset gname),
      ⌜ callee_saved m mf ⌝ -∗
      ⌜ sysc_mem_ok (us_V U) (us_V U') (us_M U) (us_M U') ⌝ -∗
      ⌜ sysc_fd_ok (us_V U) (pv_tf (us_V U') !!! tf_arg_idx 0) sts sts' ⌝ -∗
      ⌜ sysc_pipe_ok (us_V U) (us_M U) (us_M U') (pv_tf (us_V U') !!! tf_arg_idx 0) sts sts' ⌝ -∗
      ⌜ sysc_ch_ok (us_V U) cs cs' ⌝ -∗
      ⌜ sysc_num (us_V U) <> 2 ⌝ -∗
      ⌜ sysc_num (us_V U) = 7 \/ exists w : mword 64,
          pv_tf (us_V U') = <[tf_arg_idx 0 := w]> (pv_tf (us_V U)) ⌝ -∗
      ⌜ sysc_num (us_V U) = 7 \/ sysc_num (us_V U) = 12 \/
          ProcPtOwn.uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) (pv_upt (us_V U')) ⌝ -∗
      ⌜ sysc_num (us_V U) = 7 \/ sysc_num (us_V U) = 12 \/
          pv_sz (us_V U') = pv_sz (us_V U) ⌝ -∗
      ⌜ sysc_num (us_V U) = 7 \/ sysc_num (us_V U) = 12 \/
          pv_lazy (us_V U') = pv_lazy (us_V U) ⌝ -∗
      ⌜ ud_tfp (pv_upt (us_V U')) = ud_tfp (pv_upt (us_V U)) ⌝ -∗
      ⌜ pv_fdg (us_V U') = pv_fdg (us_V U) ⌝ -∗
      ⌜ pv_chg (us_V U') = pv_chg (us_V U) ⌝ -∗
      ⌜ pv_gen (us_V U') = pv_gen (us_V U) ⌝ -∗
      ⌜ (sysc_num (us_V U) = 9 /\ uint (pv_tf (us_V U') !!! tf_arg_idx 0) = 0)
        \/ pv_cwi (us_V U') = pv_cwi (us_V U) ⌝ -∗
      ⌜ sysc_num (us_V U) <> 12 \/ ... sbrk row ... ⌝ -∗
      ⌜ sysc_num (us_V U) <> UsysMemOk.USYS_fork \/ ... fork row ... ⌝ -∗
      ⌜ sysc_ret_pid (us_V U) (pv_tf (us_V U') !!! tf_arg_idx 0) pid ⌝ -∗
      sie_cap_gpr KT1 mf av true pj -∗
      cpu_own 0%nat true pj true lks -∗
      bslots 3 -∗
      sysc_init_id dqi ip -∗
      fd_slots FDSPARE -∗
      iref_slots IREFSPARE -∗
      R γf pj fn -∗
      proc_priv γf pj pid U' -∗
      fd_frags (pv_fdg (us_V U)) sts' -∗
      ch_frag (pv_chg (us_V U)) pj cs' -∗
      pc_is ret_tgt -∗
      sysc_exec_out f U U' sts sts' gn cs pid -∗
      sysc_sys_out U sts gn cs pid f (pv_tf (us_V U') !!! tf_arg_idx 0)
        (us_M U') sts' (pv_cwi (us_V U')) cs' -∗
      sysc_fork_out f U (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' -∗
      sysc_wait_out U (pv_tf (us_V U') !!! tf_arg_idx 0) cs cs' pid -∗
      WP (Loop : expr riscv_lang))
   ∧ kstack_closer pj (m !!! Regidx csp_rs1) (trap_res true + av)) -∗
  WP (Loop : expr riscv_lang).
```

(Again I elided only the interleaved comment blocks and the two long pure disjunctions' bodies — see `SpecSyscall.v:970-1000` for their verbatim text.)

**Note the exact shape of the "in and out" channel** for the exclusive ghost rows — `bslots 3`, `sysc_init_id dqi ip`, `fd_slots FDSPARE`, `iref_slots IREFSPARE` appear identically in the premise list (`SpecSyscall.v:765-768`) and in the post (`SpecSyscall.v:1010-1013`). A counted-ftable token would add exactly one such row on both sides.

---

# 4. `SpecFileinit.v` / `ProofFileinit.v`

## Full contract — `/shared/xv6iris-2-tlw/iris/SpecFileinit.v:27-66`

```coq
Definition ftable_name_str : Z := 0x80007580%Z.

Definition wp_fileinit_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let lk : mword 64 := mword_of_int KernelSyms.ftable in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (4 <= K)%nat ->
  sie_cap_gpr KT1 m K b p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name lk "ftable"%string -∗
    WpLock.lk_cpu_ready lk -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEINIT.
  Parameter wp_fileinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64),
      wp_fileinit_sconf_body m K vlock vname vcpu b p.
End FILEINIT.
```

Key header note (`SpecFileinit.v:31-37`): *"Whether the lock then becomes an [is_lock] over the open-file table is the caller's ghost step, not fileinit's -- it need only add the invariant ([is_lock_intro])."*

## `ProofFileinit.v` — **no `newlock` here**

`/shared/xv6iris-2-tlw/iris/ProofFileinit.v` is only 102 lines: `fii_code` (`ProofFileinit.v:39-58`) and `wp_fileinit_sconf` (`ProofFileinit.v:70-101`), which delegates entirely to `ILW.wp_initlock_wrapper_sconf`. **The lock is created in `ProofMain.v:1962`**, with payload `ftable_res_at γf`.

## The payload — `/shared/xv6iris-2-tlw/iris/FileInv.v`

`FileInv.v:47-52`:

```coq
  Definition ftable_res (γ : gname) : iProp Σ :=
    (∃ M : gmap nat (Qp * positive),
       ftable_auth γ M ∗
       fd_slots_auth ∗
       ⌜∀ k, is_Some (M !! k) -> (k < NFILE)%nat⌝ ∗
       [∗ list] k ∈ seq 0 NFILE, fslot γ M k)%I.
```

`FileInv.v:624-626`:

```coq
Definition ftable_res_at `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}
    (γ : gname) (ξ : CtxId) : iProp Σ :=
  ftable_res (XI := ξ) γ.
```

`FileInv.v:648-652`:

```coq
  Definition is_ftable (γl γ : gname) : iProp Σ :=
    is_lock γl ftable_addr "ftable"%string (ftable_res_at γ).

  Global Instance is_ftable_persistent γl γ : Persistent (is_ftable γl γ).
  Proof. apply _. Qed.
```

`FileInv.v:780-785`:

```coq
  Lemma ftable_res_boot (E : coPset) :
    flive_own (● (∅ : gmap nat positive)) -∗
    ([∗ list] k ∈ seq 0 NFILE, fentry_raw k) -∗
    fd_slots_auth -∗
    iref_slots NFILE ={E}=∗
    ∃ γ : gname, ftable_res γ.
```

Note `ftable_res_at_morph` (`FileInv.v:631-640`) is a `Global Instance` — if you change `ftable_res` you must keep the `CtxMorph` proof working (reviewer 1's pitfall 6 is called out at `FileInv.v:628-630`).

---

# 5. The camera pattern to copy

## 5a. `ipidUR` and the `wchG` class — `/shared/xv6iris-2-tlw/iris/Xv6Cameras.v`

`Xv6Cameras.v:1143-1145`:

```coq
Definition ipidUR : ucmra :=
  optionUR (dfrac_agreeR (leibnizO (SailStdpp.Values.mword 32))).
```

`Xv6Cameras.v:1146-1183`:

```coq
Class wchGpreS (Σ : gFunctors) :=
  { wch_pre_inG :: ghost_mapG Σ gname (SailStdpp.Values.mword 64 * gset gname);
    worph_pre_inG :: ghost_varG Σ orph_map;
    wsg_pre_inG :: inG Σ sgenUR;
    wpr_pre_inG :: ghost_mapG Σ Z gname;
    wip_pre_inG :: inG Σ ipidUR }.
Class wchG (Σ : gFunctors) :=
  WchG { wch_inG :: ghost_mapG Σ gname (SailStdpp.Values.mword 64 * gset gname);
         worph_inG :: ghost_varG Σ orph_map;
         wsg_inG :: inG Σ sgenUR;
         wpr_inG :: ghost_mapG Σ Z gname;
         wip_inG :: inG Σ ipidUR;
         wch_name : gname;
         worph_name : gname;
         wsg_name : gname;
         wpr_name : gname;
         wip_name : gname;
         (* THE PID COUNTER'S BOOT-ERA TOKEN (lane TRAP-ROWS-4, B1b).  A
            SECOND NAME AT [ipidUR] and no new functor: ... *)
         npid_name : gname }.
Global Instance wchG_preS `{!wchG Σ} : wchGpreS Σ :=
  {| wch_pre_inG := wch_inG; worph_pre_inG := worph_inG;
     wsg_pre_inG := wsg_inG; wpr_pre_inG := wpr_inG;
     wip_pre_inG := wip_inG |}.
Definition wchΣ : gFunctors :=
  #[ ghost_mapΣ gname (SailStdpp.Values.mword 64 * gset gname);
     ghost_varΣ orph_map;
     GFunctor sgenUR;
     ghost_mapΣ Z gname;
     GFunctor ipidUR ].
Global Instance subG_wchΣ {Σ} : subG wchΣ Σ -> wchGpreS Σ.
Proof. solve_inG. Qed.
```

**The key trick**: `npid_name` is a *second gname at an existing functor* (`ipidUR`), so `wchΣ` did **not** grow a row. `Xv6Cameras.v:1160-1171` spells that out explicitly.

## 5b. `SlotGen.nextpid_*` — `/shared/xv6iris-2-tlw/iris/SlotGen.v:601-637`, verbatim

```coq
  Definition nextpid_pend : iProp Σ :=
    own npid_name (Some (to_dfrac_agree (DfracOwn 1)
                           ((mword_of_int 0 : mword 32) : leibnizO (mword 32)))
                   : ipidUR).

  Definition nextpid_shot : iProp Σ :=
    own npid_name (Some (to_dfrac_agree DfracDiscarded
                           ((mword_of_int 0 : mword 32) : leibnizO (mword 32)))
                   : ipidUR).

  Global Instance nextpid_shot_persistent : Persistent nextpid_shot.
  Proof. rewrite /nextpid_shot. apply _. Qed.
  Global Instance nextpid_shot_timeless : Timeless nextpid_shot.
  Proof. rewrite /nextpid_shot. apply _. Qed.
  Global Instance nextpid_pend_timeless : Timeless nextpid_pend.
  Proof. rewrite /nextpid_pend. apply _. Qed.

  (* THE EXCLUSION, which is what the counted caller reads the counter's
     value with: a pending token and a shot cannot both exist. *)
  Lemma nextpid_pend_shot : nextpid_pend -∗ nextpid_shot -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    destruct Hv as [Hd _].
    apply dfrac_valid_own_discarded in Hd.
    iPureIntro. apply (proj1 (Qp.lt_nge _ _) Hd). done.
  Qed.

  (* ...and the one-way step allocproc takes at its store to <nextpid> *)
  Lemma nextpid_shoot : nextpid_pend ==∗ nextpid_shot.
  Proof.
    rewrite /nextpid_pend /nextpid_shot. iApply own_update.
    apply option_update. apply dfrac_agree_persist.
  Qed.
```

The design rationale is `SlotGen.v:575-601` (one-shot rather than exact-value mirror, because "updating a two-half value ghost needs BOTH halves"; "THE VALUE IS JUNK. Only the dfrac carries information; the token is reused from `[ipidUR]` at a second name (`[Xv6Cameras.npid_name]`) so that no new functor joins the bundle").

Its consumer/reader side: `PidLock.nextpid_res_at`, `/shared/xv6iris-2-tlw/iris/PidLock.v:146-156`:

```coq
  Definition nextpid_res_at (ξ : TsoCtx.CtxId) : iProp Σ :=
    ((∃ v : mword 32, TsoCtx.ctx_word4_pointsto ξ alp_nextpid (DfracOwn 1) v ∗
                      ⌜1 <= bv_unsigned v <= PIDMAX⌝ ∗
                      (⌜bv_unsigned v = 1⌝ ∨ SlotGen.nextpid_shot)) ∗
     (∃ (pids : list (mword 32)) (R : gmap Z gname),
        ⌜length pids = NPROC /\ pid_reg_dom R pids⌝ ∗
        ([∗ list] j ↦ p ∈ pids, pid_lock_share_at ξ (proc_addr j) p) ∗
        pid_reg_auth R ∗
        (⌜Forall (fun q : mword 32 => bv_unsigned q <> 1) pids⌝
         ∨ SlotGen.nextpid_shot)))%I.
```

Shooting site in `allocproc`: `/shared/xv6iris-2-tlw/iris/ProofAllocproc.v:815-825`; the regime index it takes is `ProofAllocproc.v:743-744`:

```coq
    (if tk then SlotGen.nextpid_pend
           else SlotGen.nextpid_shot ∗ SlotGen.init_reg) -∗
```

## 5c. The counted regime it rides — `/shared/xv6iris-2-tlw/iris/ProcAvail.v`

`ProcAvail.v:96-107`:

```coq
Definition pavUR : ucmra := authUR (gsetUR nat).

Class pavGpreS (Σ : gFunctors) := {
  pav_pre_inG :: inG Σ pavUR;
}.
Definition pavΣ : gFunctors := #[GFunctor pavUR].
Global Instance subG_pavΣ {Σ} : subG pavΣ Σ -> pavGpreS Σ.
Proof. solve_inG. Qed.

Class pavG (Σ : gFunctors) := PavG {
  pavG_pre :: pavGpreS Σ;
  pav_name : gname;
}.

Definition pavN : namespace := nroot .@ "procavail".
```

`ProcAvail.v:190-232` — the regime:

```coq
  Definition pav_core (on : option nat) : iProp Σ :=
    match on with
    | Some n => ∃ U : gset nat, own pav_name (● U) ∗ ⌜(n <= pav_free U)%nat⌝
    | None   => inv pavN (∃ U : gset nat, own pav_name (● U))
    end%I.

  Definition npid_done : iProp Σ := (nextpid_shot ∗ init_reg)%I.

  Definition procs_avail_at (on : option nat) (t : bool) : iProp Σ :=
    (pav_core on ∗
     match on with
     | Some _ => if t then nextpid_pend else npid_done
     | None   => npid_done
     end)%I.
```

`ProcAvail.v:244-245`, `257-258`, `312-332`:

```coq
  Definition pav_spent (on : option nat) : iProp Σ :=
    (pav_core on ∗ nextpid_shot)%I.

  Definition procs_avail (on : option nat) : iProp Σ :=
    (∃ t : bool, procs_avail_at on t)%I.

  Lemma procs_avail_seal_spent (E : coPset) (n : nat) :
    init_reg -∗ pav_spent (Some n) ={E}=∗ procs_avail None.

  Lemma procs_avail_le_at (n m : nat) (t : bool) :
    (m <= n)%nat -> procs_avail_at (Some n) t -∗ procs_avail_at (Some m) t.
```

`ProcAvail.v:499-506` — the boot mint, **over the functor half only**:

```coq
Lemma procs_avail_alloc `{!riscvGS Σ, !pavGpreS Σ} :
  ⊢ |==> ∃ _ : pavG Σ, pav_core (Some NPROC).
Proof.
  iMod (own_alloc (● (∅ : gset nat))) as (γ) "Ha".
  { by apply auth_auth_valid. }
  iModIntro. iExists (PavG Σ _ γ). iExists ∅. iFrame "Ha".
  iPureIntro. rewrite pav_free_empty. lia.
Qed.
```

## 5d. `Xv6G.v` bundle membership — and what you can/cannot reuse

`/shared/xv6iris-2-tlw/iris/Xv6G.v:64-128` (full class quoted in section-1 research above; 21 fields, every one pure capacity, none carrying a gname).

**The membership rule** (`Xv6G.v:1-7, 20-22`): *"Every field below is an `[inG]`/`[ghost_varG]`/`[ghost_mapG]` … None of them carries a `[gname]`. That is the whole criterion for membership"* and *"a file at or above this one binds `[xv6G]` and does NOT bind any of its members."*

**Adding a member takes three things** (`Xv6G.v:55-59`): the class in `Xv6Cameras.v` with its own `subG` instance, a field in `xv6G`, and a row in `xv6GΣ` (`Xv6G.v:148-152`).

**Answers to your three specific questions:**

- **Is there a `ghost_varG Σ nat` on the bundle?** Yes, four times: `kallocG.kalloc_count_inG` (`Xv6Cameras.v:152`), `diskGhostG.disk_np_inG` (`Xv6Cameras.v:297`), `consG.cons_ghost_rdG` (`Xv6Cameras.v:376`), `boxG.box_cntG` (`Xv6Cameras.v:1262`). **But there is a standing warning against a second field for an already-present class** — `Xv6G.v:130-140` documents the "duplicate-class trap" (measured twice in one day: a 400 GB / 703 GB search-cycle bomb, and an `iFrame` failing on terms that print identically). `Xv6Cameras.v:1347-1350` records the same for `ghost_varG Σ Z`. So do **not** add a duplicate class; either read the capacity off an existing member (the `TxPin` / off-ledger pattern, `Xv6G.v:138-140`) or add a *new* second name at an *existing* functor.

- **Is there a `ghost_varG Σ Z`?** Yes: `uioG.uio_brkG` (`Xv6Cameras.v:984`) and `offboxG.offbox_offG` (`Xv6Cameras.v:1356`).

- **Is there an unused gname field anywhere?** No. `wchG` has six named gnames, all in use (`wch_name`, `worph_name`, `wsg_name`, `wpr_name`, `wip_name`, `npid_name`). `pavG` has `pav_name`; `fdslotG` has `fdslot_name` (`/shared/xv6iris-2-tlw/iris/FdSlots.v:237-241`); `irefslotG` has `irefslot_name` (`/shared/xv6iris-2-tlw/iris/IrefSlots.v:125-128`). `fscfg` (`/shared/xv6iris-2-tlw/iris/FsCfg.v:79-171`) has no ftable field at all — the two ftable gnames (`γft`, `γf`) are threaded, not ambient.

### Cheapest sibling shape for the file table

Copying the `npid_name` trick exactly: **add one gname field to the class that already holds the ftable's *other* counted supply's name**. The natural candidates are:

- `fdslotG` (`FdSlots.v:237-241`) — it already has `fdslotUR := authUR natUR` (`FdSlots.v:70`), it is minted at `BootShared.v:2099` (`fd_slots_alloc`, `FdSlots.v:905-906`), and its authority **already lives inside `ftable_res`** (`FileInv.v:50`). A second gname at the *existing* `inG Σ fdslotUR` (or at a one-shot reusing a functor already in `fdslotΣ`) costs no new functor row and no new binder anywhere: `!fdslotG Σ` is already in every relevant signature (`SpecUserinit.v:139`, `SpecSyscall.v:710`, `ParkCap.v:77`, `UsertrapRes.v:2239`, `ProofSyscall.v:915`, `FileInv.v:624`).
- Failing that, `irefslotG` (`IrefSlots.v:125-128`) on the same reasoning.

Either way, the boot mint would run in `/shared/xv6iris-2-tlw/iris/BootShared.v` beside `iMod fd_slots_alloc as (Hfd) "[Hfdauth Hfdslots]"` (line 2099) and the token would be paired to the ftable at `/shared/xv6iris-2-tlw/iris/ProofMain.v:1957` (`ftable_res_boot`) rather than at `BootShared.v:2127`, because the `γf` it must be indexed by does not exist until then.

---

# Summary: the shape of the lane you are building

| step | site |
|---|---|
| camera + class field (new gname at existing functor) | `/shared/xv6iris-2-tlw/iris/Xv6Cameras.v` (`fdslotG` at `FdSlots.v:237-241`, or `wchG` at `Xv6Cameras.v:1152-1172` as the verbatim model) |
| one-shot pend/shot pair | new sibling of `SlotGen.v:601-637` |
| counted regime `ftable_avail_at on t` | new sibling of `ProcAvail.v:190-232`, with the `pav_core`/`npid_done`/`_at`/`_seal_spent`/`_le_at` set |
| the payload reading (what the token refutes) | `FileInv.ftable_res` (`FileInv.v:47-52`) — the analogue of `PidLock.nextpid_res_at` (`PidLock.v:146-156`) |
| the failure arm it refutes | `SpecFilealloc.filealloc_post`'s left disjunct (`SpecFilealloc.v:70-72`), propagating to `sys_open`'s `-1` arm (`ProofSyscall.v:7365-7368`) and to the U-tier's `wp_uk_ecall_open` `-1` arm (`UkRunSys.v:846`) |
| boot mint | `/shared/xv6iris-2-tlw/iris/BootShared.v:2099` (beside `fd_slots_alloc`) |
| pairing to `γf` | `/shared/xv6iris-2-tlw/iris/ProofMain.v:1957` (beside `ftable_res_boot`) |
| ride to userinit | new row on `mn_grp_fs` (beside `ProofMain.v:1670`'s `procs_avail_at (Some NPROC) true`) — **or nothing at all, since it is minted inside the group at line 1957** |
| new premise on userinit | `/shared/xv6iris-2-tlw/iris/SpecUserinit.v:259` (`procs_avail_at (Some (S np)) true`)'s neighbour |
| spend at the park | new row of `ParkCap.park_own` (`UsertrapRes.v:1195-1197`) → `ut_own` (`UsertrapRes.v:804`) → `ut_park_intro_body` (`UsertrapRes.v:2263-2302`) → `ParkCap.park_chan` (`ParkCap.v:372-404`) |
| reach the syscall | `wp_syscall_sconf_body` premise + post (`SpecSyscall.v:765-768` / `SpecSyscall.v:1010-1013`, the `bslots 3` route) → `sysc_arm_pre` (`ProofSyscall.v:1633-1670`) → the open arm's `SysOpen.wp_sys_open` call (`ProofSyscall.v:7391-7410`) |

**Do NOT** put it in `ProofSyscall.syscall_env` (`ProofSyscall.v:915-940`) — that bundle is fully persistent by contract (`ProofSyscall.v:267`, `ProofSyscall.v:1038`), and a linear token there would be duplicable from inside every trap round, which is exactly the objection recorded in `SyscParkEnv.v:130-141` against putting the user WP in `park_world`.