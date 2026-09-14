# PROLOGUE-ALTS handover -- three commits green on `lane/prologue-alts`

Checkout /shared/xv6iris-2-sup, branch `lane/prologue-alts`, HEAD `833300de0`,
rebased onto origin/main `1bb1702af` (still current).  Three commits:
  f5d63cbfa  items 1-2   EchoDisc.v + EchoOutPure.v
  d1b189277  item 3 (part)  EchoOut.v's stage carries the prologue resolution
  833300de0  the open-round lemmas (EchoDisc.v)

## GATE (all green, on the whole tree)
zero Error; EXIT=0 (660 files, build `pa3`; `pa4` confirms after `833300de0`);
`make -f CoqMakefile -n` prints 0 `ROCQ compile`;
`make audit-only | md5sum` = 57f7327206c4b276d05035342fea8ecf (the thirteen);
`lemma_diff --ref origin/main` CLEAN (3 files, nothing dropped/admitted, no new
assumption); no `Admitted` in any of the three files; `--check-dumps` clean.

## STILL OWED (the ONE thing item 3 does not have)
`eout_step_write_pro` / `echo_write_link_pro` -- the write link at a prologue
round's CHOICE byte.  `echo_write_link_taint` IS landed; the ordinary and
block-first links carry `ps_lb`; `read_ret` carries `ps_lb`.  Nothing in the
tree consumes the missing link yet (IO-LEAF is its only consumer), which is
why the tree is green without it.

### WHY IT DID NOT LAND, precisely -- a design finding for the coordinator
The step must derive, from the writer's credential, that the CLAIM's current
round is still open (so that filing `a` is what extends it).  The turn gives
`P = pcount`, hence `length (o_w so) = length (pending_n ps0 cs0 n0)` and
therefore `o_w so = pending_n ps0 cs0 n0` (both are prefixes of the claim's
pending).  That is NOT enough: a claim whose round is ALREADY settled has a
strictly longer `pending_n`, and `o_w so` being a proper prefix of it is a
perfectly consistent state as far as `eout_pure` says.  Nothing rules it out
because the stage has no bookkeeping law for `ps` -- `pro_pin` settles only
the rounds STRICTLY BELOW the stage and says nothing about the current one.

The fix is the exact twin of what `cs_len_ok` does for `cs`: a `ps_len_ok`
conjunct in `eout_pure` saying the current round is settled EXACTLY when the
writer has written past the block's banner, i.e.

  ps_len_ok so :=
    pro_done (pro_from (pro_idx (o_cs so) (length (o_E so) `div` 17)) (o_ps so))
    <-> (length (pending_n (o_ps so) (o_cs so) (length (o_E so)))
         < length (o_w so) + 1)   -- or, equivalently, the writer has passed
                                     the open round's [pro_of]

with its three moves (echo / ordinary write / choice write) proved as
`cs_len_ok_echo` / `_write` / `_blk` are.  I did not improvise it at the end
of a long session; phase 1b did not foresee it and it is worth a ruling.
Everything else the step needs is already proved and committed:
`pro_of_snoc_head`, `pro_tail_snoc`, `pro_from_snoc_le` (833300de0),
`pending_n_ps_mono`, `pending_n_cs_ext`, `proc_upto_prefix_S`,
`pro_of_prefix_free`, `pro_idx_app_le`.

A PURE helper the step will also want (about 20 lines, not yet written):
  Lemma pending_n_round_det (ps ps' cs : list nat) (n : nat) :
    (n `mod` length echo_line)%nat = 0%nat ->
    (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
    pending_n ps cs n = pending_n ps' cs n ->
    pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps)
    = pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps').
(n = 0 is the boot prologue; the 3-block case is `app_inv_head` on `alt_cont`
plus `pro_idx_S3`.)  Note the "this block opens a round" disjunct: it must be
a PREMISE of `echo_write_link_pro` too -- a block whose alternative is not 3
opens no round and the link must not fire there.

### ALSO OWED: the arbitrary-round BANNER LEMMA (the coordinator's (1))
For init's loop at a round entered through `line_alts !!! 3`.  Build it on
`pro_of_replicate_banner`'s shape but at `pro_from r ps` and with the offset
`length (proc_upto ps0 cs0 n0) + length (line_alts !!! 3)`; `lookup_app_shift`
is the tool.  Nothing depends on it yet.

## WHAT IO-LEAF RECEIVES TODAY (verbatim)
  echo_write_link      : (n0/17 <= length cs0) -> pro_pin ps0 cs0 n0 ->
                         proc_upto ps0 cs0 (S n0) !! P = Some b ->
                         era_pin k v -* turn v P -* ps_lb v ps0 -* cs_lb v cs0
                         -* E_lb v n0 -*
                         (((turn v (S P) * ps_lb v ps0 * cs_lb v cs0
                            * E_lb v n0) \/ T) -* Phi) -* out_link Uart0 k b Phi
  echo_write_link_blk  : + 0 < n0, n0 mod 17 = 0, n0/17 <= S (length cs0),
                         pro_pin ps0 cs0 n0, P = length (proc_upto ps0 cs0 n0),
                         a < length line_alts, line_alts !!! a !! 0 = Some b;
                         returns cs_lb v (cs0 ++ [a])
  echo_write_link_taint: T -* (T -* Phi) -* out_link Uart0 k b Phi
  read_ret's non-empty arm: cs_lb v cs0 * ps_lb v ps0 * E_lb v (n + |ws|)
  eturn k              : era_pin * turn v 0 * dl_cnt v (1/2) 0
                         * cs_lb v [] * ps_lb v [] * E_lb v 0

## Process notes
- Edit loop `scratchpad/warm.sh <File.v>`; rocq-warm writes no `.vo`, so after
  editing EchoDisc run `make -f CoqMakefile EchoDisc.vo` on the VM before
  warming EchoOutPure/EchoOut.
- Full build `./gcp-rocq/vmbuild.sh xv6iris-2-sup pa5` (pa1..pa4 used).
- Gotchas: `decide (1 = 1)` / `decide (0 = 1)` REDUCE (hence `pro_more` as a
  named definition with `pro_more_1`/`pro_more_ne`); `rewrite !length_app` and
  `rewrite -!app_assoc` UNFOLD `u_banner` / `alt_cont`, so pass explicit
  arguments (`rewrite (length_app u_banner ...)`, `rewrite -(app_assoc A B C)`)
  wherever a folded hypothesis must still match; `apply Forall_imap_pair` on a
  conjunctive predicate needs the explicit-P `Forall_imap_pair_intro`.
