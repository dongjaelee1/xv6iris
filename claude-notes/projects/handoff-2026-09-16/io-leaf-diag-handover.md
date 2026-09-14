# lane IO-LEAF M4b(1) -- handover (the shell's diagnostic tower carries
# the per-call write obligation)

Checkout `/shared/xv6iris-2-sup`, branch `lane/io-leaf-diag` on
`origin/main` = `0a2a4befe`.  NOT pushed.  ONE file touched:
`iris/UkShDiag.v`.  Build logs `dg1` (baseline), `dg2` (post-rebase),
`dg3` (the milestone); **next free `dg4`.**
Edit loop: scratchpad `wmsup.sh <File.v>` (rocq-warm on the -sup VM tree);
real builds `./gcp-rocq/vmbuild.sh xv6iris-2-sup <log>` from the repo root.

## WHAT LANDED

`UkSh.ksh_w` is the per-CALL obligation (descriptor, buffer, count).
ulib's `putc` writes ONE byte out of ITS OWN FRAME, at an address no
caller of the printf cone can name, so the cone carries

    Definition ksh_w1 (fdv : mword 64) (b : bv 8) (Ci Co : iProp Σ) : iProp Σ :=
      (∀ ua : mword 64,
         UkSh.ksh_w N fdv ua 1%nat
           (ubyte γd (uint ua) b ∗ Ci) (ubyte γd (uint ua) b ∗ Co))%I.

(new section `UkShDiagW`, beside `shd_nth_byte0_moi`, `ksh_w1_of_law`
(`UkSh.sh_deps -∗ ksh_w1 fdv b emp emp`) and `ksh_w1_mono`).  It is
`UkInit.kinit_w1` at sh.

FIFTEEN lemmas gained a `_chain` form carrying the family; EVERY ONE of
the fifteen OLD statements is kept VERBATIM as a corollary at
`ksh_w1_of_law` / `(fun _ => emp)`:

  putc, vprintf_step, vprintf_loop, vprintf, vprintf_seg, vprintf_sstep,
  vprintf_sloop, vprintf_pcs3, vprintf_pcs2, vprintf_pcs, vprintf_s,
  fprintf, fprintf_s, die, panic.

Shapes:
* the plain runs (`_loop_chain`, `_seg_chain`) take
  `□ (∀ j, ⌜lo <= j < hi⌝ -∗ ksh_w1 N fd (f j) (Ch j) (Ch (S j)))`
  with `Ch i` in and `Ch (end)` out; `lo`/`hi` are FIXED outside the
  induction so the box never has to be re-boxed.
* `_sloop_chain` takes the FIRST round's obligation LINEARLY (`b0` is the
  byte a1 already holds, which only the caller's own `lbu` can name) and
  the rest as the box over `[lo, slen)`.
* `_s_chain` / `_fprintf_s_chain` / `_die_chain` / `_panic_chain` take
  THREE families `C1 C2 C3` (format prefix / argument / format tail) and
  the two Coq equations `C1 q = C2 0` and `C2 slen = C3 (S (S q))` that
  say they are ONE family re-indexed.  At `C1 := Cg`,
  `C2 := fun p => Cg (p + q)`, `C3 := fun j => Cg (j - S (S q) + (slen + q))`
  both are `f_equal; lia`.
* `_die_chain` / `_panic_chain` are at the CONCRETE descriptor
  `mword_of_int 2` (the block is `c.li a0,2`), and the exit payload is a
  WAND `C3 flen -∗ ukn_pay N (-1)` -- that is the slot M4b(2)'s payment
  plugs into.

TWO internal helper statements grew an output fact (both are in-file only;
they are the CHANGED entries in lemma_diff):
* `wp_kshd_vprintf_pro` : `⌜ fd = m !!! Regidx a0_idx ⌝` (which descriptor
  the prologue parked in s6 -- it already said which va_list it parked in
  s7).  Without it the family's descriptor cannot be connected to the
  caller's a0.
* `wp_kshd_fprintf_gen` : `⌜ m' !!! Regidx a0_idx = m !!! Regidx a0_idx ⌝`
  (fprintf spills a2..a7 and a0 is neither).

NO other file moved.  `Hsh_owed` untouched.  No `sh_deps` premise was
renamed anywhere, so UkShRun / UkShFork / UkShMain / UkShCd / UkShEcho are
BYTE-IDENTICAL to origin/main (the other IO-LEAF agent owns four of them).

## WHAT M4b(2) RECEIVES, AND WHAT IT STILL HAS TO MOVE

The three remaining `sh_deps` sites in UkShDiag are ABOVE the chain forms
and cannot move without a consumer moving too:

* `ush_diag_leaf_holds` -- it is written at `UkShRun.ush_diag_leaf`'s
  shape (a Coq-level statement `wp_kshr_runcmd` / `wp_kshr_fork1` take as
  an argument).  To carry the obligation, THAT shape must change in
  `UkShRun.v`, and with it `wp_kshr_runcmd_final` / `wp_kshr_fork1_final`.
* The leaf's three arms print three different strings:
  - panic  : the .rodata literal (`shd_lit 0x1298 / 0x12a0 / 0x12c8`) at
    format `shd_lit 0x1290`, len 3, directive at 0 -- fully pinned, the
    family can be written down today;
  - 0xda "exec %s failed\n" and 0x10e "open %s failed\n" : the argument is
    `∃ x : uarg, ush_ptr .. ∗ ush_str (ukn_d N) x` out of
    `UkShRun.ush_diag_res`, so the argument's byte function is
    EXISTENTIAL at the leaf.  The chain leaf must therefore read
    `∀ (slen : nat) (sf : nat -> bv 8), ... C2/C3 ...` under that
    existential, or the leaf must be re-stated to expose `x` to its
    caller.  Whether `sf` is pinned to "echo" is M3/M4b(2)'s question --
    the parser's proof pins the LINE (`UkSh.ush_line_is`), not yet the
    `%s` token handed to the diagnostic.
* The payment itself (`EchoLinks`' write link at each site's stage) needs
  the turn at that stage, which is M3b core's / M6's.  Nothing here pays
  with the era's link; every chain form is discharged today from
  `sh_deps` through `ksh_w1_of_law`.
