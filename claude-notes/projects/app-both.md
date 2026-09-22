# Worklist: app-both — ONE application by abstraction (Route B), then the union

Design of record: [`../design/app-both.md`](../design/app-both.md) (RULED
2026-09-22: Route B; the union replaces the file and pipe applications).
Opened 2026-09-22.  Nothing built yet.

## 0. The abstraction, read off the three instances

`LinkRec` (`iris/LinkRec.v`) is the era's console-output record: ~20 data
fields (the era's taint/pins/links, the per-line pure hooks `lk_ab`/
`lk_apr`/`lk_pan`/`lk_exf`/`lk_exfb`/`lk_noc`, twelve credential families
indexed by era, pins, input and position, the read receipt, the reader's
residue, the turn) and ~60 laws.  Its three instances (`EchoLinkInst`,
`FileLinkInst.file_link_inst_at s0`, `PipeLinkInst.pipe_link_inst_at`) are
built by hand, ~5k lines each, and every family in all three has ONE
shape:

    (∃ ps cs P, ⌜wr_X ps cs [s0] I P⌝ ∗ cursor v ps cs I P [∗ state witness]) ∨ [head arm] ∨ T

where `wr_X` is a PURE predicate on the app's session model (`sess`,
`sessf`, `sessp`: prologue ++ per-line blocks ++ partial line, the block
being the echoed line ++ the alternative's continuation), the cursor is the
era's ghost (`turn ∗ ps_lb ∗ cs_lb ∗ inp_lb`) and the state witness is the
file's boot-ledger entry (`f0w s0`; absent at echo/pipe, whose state is
`unit`).  The per-app differences are exactly:

1. **the LINE MODEL**: the line grammar, the alternatives per shape, their
   continuation bytes, and the STATE they thread (`FileDisc.fsm`; the
   identity at echo/pipe) — a pure record;
2. **the BLOCK ARM of one shape**: how the console family looks while that
   shape's continuation is being written — one writer (echo, file), or the
   pipe's TWO writers with the per-round ledger and terminal flag
   (`PipeBoth.pwc_blk2`, `pwc_line2`'s third arm) and the loop's widened
   credential (`UkShPipeFork.pterm_wc`);
3. **the CHILD LAW of one shape** (`UkShFork.ushf_child_law_at` at the
   shape's line predicate: echo's, `UkShRedirBody.sh_redir_child_law`,
   `UShRound.Hchild_cat`, `UShPipeLaw`'s);
4. **the per-cycle console claim's STAGE** (`FileOut.fostage` with `f0`;
   `PipeOut.postage` with the two-writer cursor), where the write/read
   steps are proved.

So a SHAPE MODULE is (2)+(3) plus its contribution to (1) and (4), and an
application is a line model assembled from modules, a claim stage
assembled from their extensions, and the generic families/laws/round/init
proved ONCE over that.

## 1. Milestones

- **M1 — the line model, pure.**  `LineModel.v`: a record `lmodel` (state
  type, line type with parse/print, alternatives with encoding/`ok`/
  panic/exec/silent classification, continuation at a state, the state
  step) and, over it, the session (`sess`), the `wr_*` predicates, the
  round pointer, and the DETERMINACY theorem (`sess_prefix_det`) proved
  once from the byte facts every instance already proves (`$`-free runs
  and prompts; the pipe's interleavings are a module's alternatives).
  `EchoDisc`/`FileDisc`/`PipeDisc`'s sessions as instances, with the
  landed definitions recovered BY CONVERSION (the `LinkRec` rule: consumers
  name families partially applied, so an instance must be definitionally
  the landed thing, not merely equivalent).  Anti-vacuity demos.
  Exit: the three `*_prefix_det` theorems are corollaries; nothing
  downstream moves.  **DONE 2026-09-23** (the file's and the pipe's are
  corollaries; echo's stays its own, see RESUME HERE; the demos are the
  models' own, unchanged).
- **M2 — the generic families.**  `GenLinksLine.v`: the twelve families,
  the read residue, the turn and the ~60 laws over an `lmodel`, a cursor
  and a state-witness family (`f0w` at the file, `emp` elsewhere), with
  a per-shape BLOCK ARM hook; the echo and file instances by conversion;
  the pipe's two-writer arm as the first non-trivial block module (this
  is where RULINGS §4.3f–p live; they are not re-argued, they are
  re-housed).  Exit: `EchoLinkInst`/`FileLinkInst`/`PipeLinkInst` are
  applications of the generic record; the three tiers' link files
  deleted.
- **M3 — the generic console claim.**  `GenOut.v`: the stage as the
  model's stage + a per-shape extension; the write/read/drain steps once;
  `EchoOut`/`FileOut`/`PipeOut` as instances.
- **M4 — the child laws as modules.**  Each child law re-stated at the
  generic families (its proof is line-shape-local, so this is renaming),
  and the generic round `UShGenRound` dispatching over the module list;
  `UShRound`/`UShPipeRound` deleted.
- **M5 — the union.**  The four-module application: `BothDisc` is the
  model at the four shapes (a listing), the claim `file_pred`, /init by the
  generic mould, `UBothBootAdequacy`, `BothAssumptions`; `file_phi` and
  `pipe_phi` as corollaries; `UFileBootAdequacy`/`UPipeBootAdequacy` and
  their audits retired.

## 2. Rules for the campaign

- Every milestone lands with the three existing theorems still closed and
  the four audits unmoved (system 13, tree 13, file 14, pipe 14); a
  milestone that cannot keep a landed statement recovers it by conversion
  or by a one-line corollary, never by a restatement.
- The whole-tree gate before every landing (durable-notes); no
  section-level instance binder goes into a shared file unmeasured.
- Cleanups owed to this campaign from before it: SLOT-WS (the fork
  interface at the parsed line — M4 is where it is paid), NAME-PATTERN.

## 3. M2: the family-shape table (read off the three link tiers, 2026-09-23)

Every console family in `EchoLinks`/`EchoLinksLine` (E), `FileLinksLine`
(F) and `PipeLinksLine` (P) has the shape

    (∃ ps cs [s0] P, ⌜wr_X ps cs [s0] I P⌝ ∗ CUR) ∨ [HEAD] ∨ T

with `CUR := turn v P' ∗ ps_lb v ps ∗ cs_lb v cs' ∗ inp_lb v I ∗ [W k s0]`.
What differs per tier, field by field of `LinkRec`:

| field | E | F | P | generic |
|---|---|---|---|---|
| `lk_T` | `T` (param) | `file_taint` | `echo_taint γ` | param `T` |
| state witness in CUR | — | `f0w k s0` (writer), `f0bw` (reader) | — | params `W`, `Wb : nat → lm_st → iProp` (`emp` at E/P) |
| head arm | — | `fhead k v I` (I=[], cursor 0, `f0pre`) | — | param `H k v I` (`False` at E/P); `_at s0` twin `H_at` |
| `lk_ab I a` | `line_alts_of (last_ws I) !!! a` | guarded `cont None (fline I) (ralt_dec a)`, guard = ok ∧ state-free | guarded `pcont (pline_at I) (palt_of a)`, guard = ok ∧ ¬forkS | `lm_ab := if decide (ok ∧ free) then lm_cont st0 (line_at I) (dec a) else []`; hooks `lmh_free`, `lmh_st0` |
| `lk_apr I a` | `a < 3` | ok ∧ free ∧ ¬panic | ok ∧ ¬panic ∧ ¬forkS | `lm_apr := ok ∧ free ∧ ¬panic` (free ⇒ ¬term) |
| post index | `length (ab I a) - 2` | INSIDE, `length (fabs s0 cs I a) - 2` at the round's state | `length (pab I a) - 2` | F's (state-computed `lm_abs`); E/P's is it at a state-free alt |
| `lk_pan/exf/exfb/noc` | 3 / 1 / `alt_execfail` / 2 | `fpan_of/fexf_of/fexfb/fnoc_of (fline I)` | 3 / `pexf_of/pexfb/pnoc_of (pline_at I)` / 2 | hooks `lmh_pan/exf/exfb/noc : lm_line → _` + laws |
| `lk_line` | `pro ∨ ∃ a<3, post` | `pro ∨ ∃ a, faprs ∗ post` | `pwc_line2`: F's two arms ∨ the TWO-WRITER arm | generic two-arm `gwc_line`; the pipe MODULE wraps it (`pwc_line2 := gwc_line ∨ blk2`, as today) |
| `lk_lpr` | match | match | `pwc_lpr2` (line2 at 0) | match; the module's twin at 0 |
| `lk_rres` | `∃ ps0 cs0, rd_stage ∗ turn_lb (len proc_before) ∗ ps_lb ∗ cs_lb` | + `s0`, `alts_pre I cs0`, `f0bw`; `rresw = rres ∗ flw` | E's with `alts_pre_p` | `lm_rd_stage` (pointwise `lm_alts_pre`); `Wb` in the residue; `flw` is the file MODULE's extra conjunct |
| `lk_rr`, `lk_turn` | `read_ret`, `eturn` | `fread_ret`, `fturn_pre` | `pread_ret`, `pturn_pre` | stage-side (M3) |
| `lk_pban/pdiag` | `ewc_pro/ewc_pdg` | `∃ s0, fwc_pban_at` | `pwc_pban/pwc_pdg` | generic over `lm_wr_pban/pdiag` |
| the write laws (`lk_ban_step`, `lk_blk_step`, prompt steps) | from `echo_links` | from `file_links` (at `proc_stream_f`, `f0_lb`) | from `pipe_links` | a generic LINKS interface `glinks M W` (the six □ laws at `lm_proc_stream`); each stage proves its links ⊢ it (M3) |

The pure lemma inventories are the SAME list three times (F: 75, P: 70,
E: 28+28+11): `ab_ok/is/at/len_ge2/dollar/space`, `pan/exf/noc` at the
hooks, `wr_blk_{nonnil,lines,started,t_stage,pin_snoc,low,pending,byte}`,
`pro_idx_snoc_{ne,pan}`, `wr_tail_snoc`, `pending_at_round_snoc`,
`wr_ban_{pro,low,filed,byte,done,round0}`, `proc_before_from_gap`,
`proc_before_line`, `wr_pro_dollar`, `wr_blk_dollar`, `wr_sp_open`,
`wr_open_read`, `wr_blk_{open,sp}`, `wr_sp_open_t`, `wr_open_read_t`,
`wr_pro_tail`, `wr_pro_dollar_t`, `wr_blk_pending_pan`, `wr_blk_ban`,
`pending_at_nonnil_at`, `wr_owed_read_refute`, `wr_pban_of_ban`,
`wr_pdiag_{byte,1_of_pro,S,done_1}`.  Some at F/P need the state
(`_fs` variants at `fabs`); E's are the originals.

### M2 plan

- **M2a `LineModelLinks.v`** (pure; after `LineModel.v`): the hooks
  record `lm_hooks M` (data `lmh_free`, `lmh_st0`, `lmh_pan/exf/noc`,
  `lmh_exfb`; laws: the hook alternatives are admissible / free / their
  panic bits / their continuations; state-freedom
  `lmh_free_cont : lmh_free a = true → lm_cont s l a = lm_cont s' l a`;
  `lmh_free_term`; `lmh_cont_prompt` WITHOUT line/state premises, as the
  writer holds none), `lm_line_at`, `lm_ab`, `lm_apr`, `lm_abs`, `lm_aprs`,
  `lm_alts_pre`, `lm_rd_stage`, `lm_wr_pban`, `lm_wr_pdiag`, and the pure
  lemma list above ONCE over `lm_wr_*`/`lm_proc_stream` (mould:
  `FileLinksLine` S0–S7, the richest).  Then `LineModelWr.v`'s equations
  move INTO `FileLinksLine` S1 / `PipeLinksLine` S1 (they need only the
  stage's pure file), `LineModelWr.v` is deleted, and the two tiers'
  pure sections become corollaries through the equations (as M1 did for
  determinacy).  Exit: F/P pure sections are corollaries; E untouched.
- **M2b, THE INTERFACE (read off `FileLinks`/`PipeLinks` and the S8
  proofs, 2026-09-23).**  Section parameters: `M`, `L`, `K`; the taint
  `T`; the pin `PIN : nat → era_pins → iProp`; the writer's state witness
  `W : nat → lm_st M → iProp` (persistent, timeless; the file's `f0w g`
  minus nothing, `emp` at the pipe); the reader's `Wb` (`f0bw g`; `emp`)
  with `W ⊢ Wb` and the two agreement laws; the head arm `H : nat →
  era_pins → list (bv 8) → iProp` (timeless; `fhead`; `False`).  The links
  interface `glinks` is the file's seven laws with `file_era_pin ∗ f0_lb`
  replaced by `W k s0` on the way in AND out (`W` is persistent, so the
  return arm is the bare cursor): `gl_w` (a stream byte at
  `lm_proc_stream`), `gl_blk` (the block-first byte files `a`; premises
  `lm_ok`, `lmh_free`, the byte of `lm_cont` at the round's `lm_upto`
  state -- the pipe's `palt_isforkS = false` IS `lmh_free`), `gl_pro` (a
  prologue choice byte files `a`), `gl_taint`, `gl_rd`, `gl_rd_taint`, and
  `gl_head` (the head arm's first byte: `H k v I` in, the cursor at
  `[3] [] s0 0 ∗ W k s0` out -- `file_link_first` at the file, vacuous at
  `H := False`).  Each tier proves `file_links ⊢ glinks file_lm (f0w g)
  (fhead g)` / `pipe_links ⊢ glinks pipe_lm emp False` once, and every S8+
  law (`fban_step`, `fblk_step`, the prompt steps, `fwc_read*`,
  `fowed_read_taint`, `fban_read_taint`, `fwc_panic_done`, `fturn0` --
  the last is stage-side, M3) is proved once over `glinks`.  The `_at s0`
  twins (`FileLinksAt`) are the generic families with `s0` hoisted (the
  generic file states both shapes and the packing lemmas).  The pipe's
  `pwc_line2`/`pwc_lpr2` and `pipe_link_file` stay module-level wrappers.
- **M2b `GenLinksLine.v`** (Iris; after `EchoOut`/`LinkRec`): the cursor
  `gcur`, the families (both the closed and the `_at s0` shapes), the
  timeless/persistent dispatch, the taint/loose-tight/indexed laws, the
  reader's residue; the links interface `glinks M W` and the write laws
  over it.  Exit: `LinkRec`'s ~60 laws proved once as `gen_link_inst M K
  T W Wb H : LinkRec` (minus `lk_rr`/`lk_turn`, which are stage fields).
- **M2c** the instances: `FileLinksLine` S8's families REDEFINED as the
  generic at `file_lm`/`f0w`/`fhead`, `FileLinksAt`'s as the `_at` twins,
  `PipeLinksLine` S5's at `pipe_lm`/`emp`/`False`; `file_links`/`pipe_links`
  ⊢ `glinks`; the landed lemmas as corollaries; `FileLinkInst`/
  `PipeLinkInst` built from `gen_link_inst` plus the module extras
  (`flw`, `pwc_line2`).  MEASURE consumer breakage per family (a consumer
  that unfolds a family sees the generic body); a family whose consumers
  compute on its body is kept as a definitional alias
  (`fwc_pro := gwc_pro …`, which IS the body up to the wr-equation).

## RESUME HERE (2026-09-22, late)

M1 STARTED.  Landed: `iris/LineModel.v` -- the record `lmodel` (state,
line, alternatives with their code and panic bit, continuation at a
state, step) and over it `lm_at`, `lm_pro_idx`, `lm_upto`, `lm_cont_at`,
`lm_blk`, `lm_seq`, `lm_sess`, `lm_after`, `lm_pro_ok`, `lm_pro_pin`
(+ `lm_pro_pin_of_ok`); `iris/LineModelInst.v` -- `file_lm`, `pipe_lm`,
`echo_lm` and the equations `sessf_lm`, `sessp_lm`, `sess_lm`.  FOUND:
the file's and the pipe's sessions are the generic fold BY CONVERSION
(`alt_seq_f_lm`/`alt_seq_p_lm` are `reflexivity` -- Coq compares the
fixpoints structurally), echo's is not (its panic test is `decide`, the
model's `bool_decide`), hence an equation.  Nothing imports the two files
yet.

SECOND CUT (same day): `lmodel` gained `lm_ok` (admissibility),
`lm_body_ok`/`lm_body_byte` (the input discipline's two readings);
`LineModel.v` now has `lm_alts_ok`, `lm_disc_input`, the stream folds
(`lm_pending_at`, `lm_proc_before_from`, `lm_proc_before`,
`lm_proc_stream`) and the writer's stages (`lm_wr_pro/blk/open/owed/sp/
ban/tail/blk_t/sp_t/open_t/banp`, `lm_wr_pre`, `lm_blkcs`).
`LineModelInst.v` (registered after `PipeOutPure`): `alts_ok`,
`disc_input_{f,p}`, `pending_at_{f,p}` by conversion; the stream folds by
induction (the state is a fixpoint PARAMETER: the file's at `option
fstate`, the pipe's absent, so those fixes do not convert).
`LineModelWr.v` (after `PipeLinksLine`, since the `wr_*` predicates live
in the Iris-tier link files): all fifteen file/pipe writer equations,
the base ones by rewriting the stream equations, the derived ones
(`owed`, `sp`, `blk_t`, `banp`) through the base ones (`banp`'s S arm by
`functional_extensionality`, already an axiom of the tree).  Echo's
writer equations are NOT stated (echo is the pipe's corollary; its
`decide`-vs-`bool_decide` panic test makes them lemmas, not
conversions -- state them only if M2 needs the echo instance directly).

THIRD CUT (2026-09-23): DETERMINACY ONCE.  `lmodel` gained four fields
(`lm_line_ok`, `lm_st_ok`; `lm_term` the coverage-ending arm, `lm_merge`
what it can have written) and a laws record `lm_laws M` (body parses to a
well-formed line; the step keeps `lm_st_ok`; a panic prints `alt_panic`;
a coverage-ending arm never panics and prints a mergeable output;
`lm_merge` is prefix-closed; `lml_cont_shape`: every other continuation is
a `$`-free run then the prompt AND, put beside the panic line on one
wire, IS the panic line -- stated in that consequence form because the
file proves it from a newline-shape disjunction and the pipe from a
three-way one).  `LineModel.v` §3 (section `determinacy`, `Context (L :
lm_laws M)`): `lm_cont_pair_det` (the block step, the pipe's four cases
with D4's two guards), `lm_seq_prefix_det` (the induction, at two states
and with the round-by-round block equality), `lm_sess_prefix_det` (AT
TWO STATES `s s'`).  The byte facts both models had proved twice
(`fd_*`/`pd_*`: the `$`-split, prompt-of-`$`, the out-vs-panic
collision, the list helpers) moved to a new pure `iris/LineBytes.v`
(`lb_*`, `nodollar`), registered after `EchoDisc`; `FileDisc` and
`PipeDisc` `Require Export` it and `Require Import LineModel`.
`FileDisc` §6 and `PipeDisc` §7 (the two ~700-line determinacy
sections) are DELETED and replaced by the instances (`file_lm`,
`pipe_lm`, the session/pointer/range/discipline equations, which moved
there from `LineModelInst`), the laws (`file_lm_laws`, `pipe_lm_laws`:
each a `constructor` over the landed byte lemmas) and the landed
theorems as one-line corollaries: `FileDisc.sessf_prefix_det2` (two
states; MOVED from `FileOutPure` §8, whose own 70-line proof is gone),
`FileDisc.sessf_prefix_det` (its `s' := s` case),
`PipeDisc.sessp_prefix_det` (the D4 guards discharged by
`palt_isforkS_inv`/`palt_ok_forkS_pipe`).  `LineModelInst.v` keeps only
the stream-fold equations and `echo_lm`.  Net: -614 lines.  Echo's
`EchoOutPure.sess_prefix_det` is NOT a corollary: its statement is at
`cs_ok` (every code below 4 at every index), not the model's range
condition, and echo is the pipe's corollary in the landed tree; it goes
with the echo tier at M5.  Gotchas met: a variable named `I` shadows
`True`'s constructor (`Logic.I`); comments must not contain `"`.

M2a IN FLIGHT (2026-09-23): `iris/LineModelLinks.v` (pure; after
`LineModel.v`) -- the hooks record `lm_hooks M` (data: `lmh_free`,
`lmh_st0`, `lmh_pan/exf/exfb/noc`, `lmh_ok_dec`; laws: the named
alternatives are admissible/free/their panic bits/their continuations,
`lmh_free_cont` (state-freedom), `lmh_free_term`, `lmh_cont_prompt` and
`lmh_cont_nonnil` WITHOUT the discipline's premises), `lm_line_at`,
`lm_ab`, `lm_apr`, `lm_abs`, `lm_aprs` (= ok ∧ ¬panic ∧ ¬term -- the pipe's
`papr` shape; the file's `faprs` is it with `term` constantly false),
`lm_alts_pre`, `lm_rd_stage`, `lm_wr_pban`, `lm_wr_pdiag`, and the pure
lemma list ONCE (§2 model structure, §3 the stream incl. the gap law and
the line's read, §4 the block bytes, §5-§7 the steps, §8 the discipline
lemma `lm_wr_owed_read_refute`, §9 `lm_wr_pban_of_ban`/`lm_wr_pdiag_S`).
`FileLinksLine`: `file_hooks : lm_hooks file_lm` (with `cont_prompt`
extracted from `fabs_prompt`, `cont_nonnil_dec`), the equations
`fline_lm`/`fab_lm`/`fapr_lm`/`fabs_lm`/`faprs_lm`/`rd_stage_f_lm` and the
`_o` stream equations at an `option fstate`, the `wr_*_f_lm` equations
(moved from `LineModelWr`), and S0/S2-S7 as one-line corollaries.
`PipeLinksLine`: `pipe_hooks : lm_hooks pipe_lm` (`lmh_free := negb ∘
palt_isforkS`, pan := 3), `pline_at_lm`/`pab_lm`/`papr_lm`/`rd_stage_p_lm`,
the `wr_*_p_lm` equations, S0-S4 as corollaries EXCEPT the pipe-shaped
ones kept with their own proofs: `wr_blk_pending_p` (at `alt_cont_p`),
`wr_blk_line_p`, `wr_blk_cont3_p` (a panic at an ARBITRARY code),
`wr_blk_byte_p` (no `papr` premise), `wr_blk_dollar_c_p`, and the three
`wr_pdiag_{byte,1_of_pro,done_1}_p` (their generic forms need
`EchoLinksPro.pro_of_fail_snoc` re-proved in the pure layer -- M2 leftover
PDIAG-GEN).  `LineModelWr.v` DELETED.  Gotchas: apply a generic lemma AT
its instance (`apply (lm_x file_lm file_hooks)`), never bare -- the
unifier cannot invert `lm_ok ?M` against the unfolded `ralt_ok`; a
section variable used only through another section lemma must still be
declared (`Proof using L K`; scratchpad `closure.py` computes it).

M1 EXIT REACHED: landed as `f284dcfb4` (whole-tree gate EXIT=0, 108
files; audits 13/13/14/14).  NEXT:
M2 -- `GenLinksLine.v`, the twelve families over an `lmodel`, a cursor
and a state-witness family, with the per-shape block arm hook; read
`FileLinksLine.v`/`PipeLinksLine.v` side by side first and write the
family-shape table into this file before coding.
