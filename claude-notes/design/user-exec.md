# Design: the generic exec-success spec (spec-cleanup, EX-0)

Status: DESIGN OF RECORD, 2026-09-18 (Fable), on the owner's word
("exec is something we could tackle; come up with an exec-success
spec").  Companion pages: `user-read.md` (the pattern: one rule, the
arm by the caller's own knowledge, the application as an INSTANCE),
`applications.md` (the pinned bundle's home), `fs-syscall-specs.md`
(the AU forms and the abstract view `aview`).

## 0. The finding that sets the scope: the kernel side is already general

Every exec-success obligation at the kernel boundary is stated over an
ARBITRARY file, checked in the tree rather than assumed:

- `SpecKexec.exec_slot_pre`'s arm (a) is `∀ av i f nl W', … Φo av i
  (File f) -∗ ⌜kexec_loadable f⌝ -∗ ⌜kexec_image_ok f na alen afun sts W'⌝
  -∗ ⌜cwd/lazy/ch/pid rows⌝ -∗ my_pay -∗ S W'` — `f : elf_bytes` is a
  binder, not a constant.
- `kexec_image_ok f na alen afun sts W'` is NEAR-FUNCTIONAL in
  `(f, args, sts)`: entry pc = `elf_entry f`, size = `kexec_sz f`, sp and
  a0/a1 by formula, the loaded segments a sub-image (`uimg_sub (elf_image
  f)`), the args and stack at their computed places, the permission map
  `kxb_perm_ok f` and nothing past the break, the fd table = the caller's
  `sts`, cwd/children/pid = the caller's.  A program's entry proof needs
  nothing else about its key.
- `kexec_loadable f` is DECIDABLE (`ElfLoadable.kexec_loadable_b`).
- The argument vector is ANY vector already (`exec_args_of`, upstream's
  word-list generalization); the path is read off the caller's own image
  (`exec_path_of`, a function of `(M, pv)`).
- An UNVERIFIED target is already served: the taint arm sends the new
  image to the generic family (`UkRun.uxsup`, `udepw_of_uxsup`) — exec
  of an arbitrary binary with NO promise about it works today.

So "exec is pinned to init/sh/echo" means precisely: the U-TIER
ASSEMBLY that turns a program's knowledge into the kernel's three-conjunct
bundle (`SpecSysExec.sys_exec_au_pre` = the walk, the observation, the
slot) exists only in `PinnedExec.pinned_exec_bundle`, whose inputs are a
PIN on the abstract view read out of the application's invariant
(`AppInv.app_inv`) and a loadability fact proved per image.  Nothing
kernel-side is owed.  Everything below is U-tier and ours.

## 1. The three obligations the pinned bundle fuses

`pinned_exec_bundle` takes `pin_resolves Pin cw pl hops ino f nl`,
`kexec_loadable f`, `exec_path_of M pv pl`, the app_inv claim law, and a
□-constructor.  Read as three separable obligations:

**(W) THE RESOLUTION** — "from cwd `c`, path `pl` walks `hops` to inode
`i`, whose node is `File f`."  Kernel-side this is the cursor-family walk
`FsAbsEra.ex_start γfs c P Pmiss pl` + the terminal observation
`aopen_commit_at`'s `Φo av i (File f)`; the family `P k d` is WHAT THE
CALLER WANTS TO LEARN at hop `k` — the same role as read's `Φ`.  Three
suppliers:
  - TRIVIAL (`ax_hops_triv`, `P := λ _ _, True`): the generic tier's;
    learns nothing, so only the taint arm is reachable.  Exists.
  - PIN (`PinnedObs.pobs_walk` from `pin_resolves_at`, read off
    `app_inv`): the application asserts the fs shape as an invariant.
    Exists; echo's route.
  - FRAGMENTS (NEW): the caller OWNS shares of the abstract view —
    `FsAbs.nview Γ q d (Dir …)` at each hop and `nview Γ q i (File f)` at
    the terminal — and the walk's cursor family is paid hop by hop from
    them.  This is the pin-free route: a program that opened/read a file
    and kept a share, or was handed one, can exec it without any
    application-level fs invariant.  FEASIBILITY NOTE: exec's namei and
    `readi` are READS; RD-6 established that a WRITE's mover needs the
    whole γtop element (`ic_loaded` exclusivity), but `ic_rd_arm` leaves
    a 3/4 share on purpose — so held shares should survive the walk.
    Verify at EX-2, it is the lane's first check.

**(L) LOADABILITY** — `kexec_loadable f`.  For a known `f`: by
computation (`kexec_loadable_b f = true`, `vm_compute`).  Today proved
per image ("the two user images are loadable"); the general form is the
one-line decision, stated once.  It is what REFUTES arm (b) (the not-
loadable arm), exactly as the pinned bundle does.

**(E) THE ENTRY** — the exec'd program's own promise at its key:

    image_entry f Q Pay X :=
      □ ∀ na alen afun sts cs pidv c W',
          ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
          ⌜uvis_cwd W' = c⌝ -∗ ⌜uvis_lazy W' = false⌝ -∗
          ⌜uvis_ch W' = cs⌝ -∗ ⌜uvis_pid W' = pidv⌝ -∗
          my_pay (uvis_gen W') Q -∗ Pay -∗ X W'

This IS the □-constructor premise `pex_slot`/`pinned_exec_bundle`
already take — the design names it and makes it the seam.  ONE LEMMA
PER VERIFIED PROGRAM, proved from that program's own code proof, in
place of today's hand-shaped pair (`UShKernel.sh_slot_of_kexec` for sh,
`UEchoKernel.echo_uexec_slot` bridged from `kexec_image_ok` for echo).
`Pay` is the linear resource the new image must OWN from birth (sh's
console lease); for most programs it is `emp`.  And the generic entry
`image_entry_taint T` (X := the generic slot, from `T`) is the taint arm,
already there.

## 2. The general assembly and the U-tier rule

    exec_bundle_of :  (W) -∗ ⌜(L)⌝ -∗ (E) -∗ (taint arm) -∗ Pay -∗
                      ∃ P Pmiss Fo, sys_exec_au_pre (MkPfam X Pay) … c Q P Pmiss Fo M pv av sts cs pidv

`pinned_exec_bundle` becomes `exec_bundle_of` at the PIN supplier of (W)
and the per-image (L); init's and sh's bundles re-derive as instances
at their exact statements.

THE U-TIER RULE `wp_uk_ecall_exec_run`, in `user.tex`'s `urun` style
(§7 "Processes", beside fork):

    m[a7] = SYS_exec → m[a0] = pv → m[a1] = av →
    path_at M pv pl → args_at M av (na, alen, afun) →        (pure, off the caller's own read-only runs)
    uinstr γ pc ECALL -∗ urun γ h m pc k -∗ ucwd γ c -∗
    resolves γfs c pl i f -∗                                  (W: the caller's knowledge, as a resource or a pin)
    ⌜loadable f⌝ -∗                                           (L: by computation)
    image_entry f Q Pay X -∗ Pay -∗                           (E: the exec'd program's own theorem, and what it must own)
    ( ∀ h'.  Pay -∗ ukn_pay (−1) -∗                           (the FAILURE arm: refund — args did not fit, or no page)
             urun γ h' m[a0 := −1] (pc+4) k -∗ wpcycle ) -∗
    wpcycle

There is no success continuation IN the rule: on success the process
never returns here — it continues as `X` at the loaded key, which is
what `image_entry` promised.  That asymmetry is the honest shape of
exec, and it is why the entry is a separate theorem rather than a
postcondition.

Two derived readings the TR should say in prose: (i) exec'ing an
UNVERIFIED binary is the same rule at `image_entry_taint` — the program
learns nothing about what runs next, and the system stays safe; (ii)
with the FRAGMENT supplier a program needs no application-level
invariant to exec a file it holds a share of — "I know what this file
is" is a resource, not a global claim.

## 3. What each existing program becomes

- init execs /sh: `exec_bundle_of` at the PIN supplier (era-0 pins,
  unchanged) with `image_entry sh_elf` := the lemma extracted from
  `sh_slot_of_kexec`.  `UInitSh`'s bundle at its exact statement.
- sh execs /echo: same at `FsEchoPin.era0_echo_pins`, `image_entry
  echo_elf` := the bridge from `echo_uexec_slot`.  `UShEcho`'s bundle at
  its exact statement; `echo_node_img` (sh's malloc'd-argv reading)
  becomes an instance of the general argv reading (§4, EX-3).
- A NEW program: its author proves `image_entry f_P …` from its code
  proof and chooses a (W) supplier; nothing else.

## 4. Lanes

- [ ] **EX-1 ENTRY + ASSEMBLY** (U tier; mechanical): name
  `image_entry`, cut `exec_bundle_of` out of `pinned_exec_bundle` with
  (W)/(L)/(E) as premises, re-derive `pinned_exec_bundle`, init's and
  sh's bundles as instances at their exact statements; (L) as the
  decision lemma.  Zero semantic change; echo audit at 14.
- [ ] **EX-2 FRAGMENT WALK** (U tier + fs seam; the feasibility lane):
  `ex_start` paid from owned `nview` shares along the hops + the
  terminal share as `Φo`'s receipt.  First check: the read-side share
  survives exec's namei/readi (`ic_rd_arm`'s 3/4).  If it does not,
  STOP with the wall written here — that would be a kernel-side ask
  (the read path's share discipline), the only thing that could make
  exec need upstream.
- [ ] **EX-3 ARGV READING** (U tier): one lemma reading
  `exec_path_of`/`exec_args_of` off owned `ubytesq`/`uwordq` runs at
  any layout; `init_args_det` and `echo_node_img` as instances.
- [ ] **EX-4 THE RULE + THE TEST + THE TR**: `wp_uk_ecall_exec_run`
  over the general bundle; a consumer test (a program holding fragments
  for a file execs it and lands at `X`); `user.tex` §7's fork figure
  gains its exec sibling from §2.

Nothing in this plan is relay-shaped: the kernel already promised
everything the general rule consumes.
