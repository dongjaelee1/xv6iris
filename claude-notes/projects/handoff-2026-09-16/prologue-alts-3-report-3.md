# PROLOGUE-ALTS-3 report 3 -- rebased onto IO-LEAF step 3 (main = eab906990)

Checkout /shared/xv6iris-2-tlw, branch `lane/prologue-alts-3`, now on top of
origin/main `eab906990` (IO-LEAF step 3, the glue).  `git fetch origin && git
rebase origin/main` replayed the three lane commits WITHOUT ANY CONFLICT: the
one-liners in UShLine.v / UShOut.v landed where they were (step 3 moved the
surrounding code but not those lines).  Nothing pushed; working tree clean
(`git status --porcelain` empty); nothing was left uncommitted.

## Commits (on top of eab906990)
- `7c269ea8f` PROLOGUE-ALTS-3: the banner is optional -- letter 3, the bare prompt, the discipline lemma
- `58b586b52` PROLOGUE-ALTS-3: EchoLinksBan -- the bare prompt and the discipline lemma at the tight shapes
- `39544b6af` PROLOGUE-ALTS-3: EchoLinksPro at the banner letter (INIT-DIAG rebase fix)
(content identical to `da61f6275` / `fcd6e6c08` / `5612d819d` of report 2.)

## `git diff origin/main --stat`
```
 iris/EchoDisc.v      | 634 +++++++++++++++++++++++++++++++++------------------
 iris/EchoLinks.v     | 457 ++++++++++++++++++++++++++++++-------
 iris/EchoLinksBan.v  | 187 +++++++++++++++
 iris/EchoLinksLine.v |   6 +-
 iris/EchoLinksPro.v  | 115 ++++++----
 iris/EchoOut.v       | 369 +++++++++++++++++++++---------
 iris/EchoOutPure.v   |  14 +-
 iris/UShLine.v       |   2 +-
 iris/UShOut.v        |   4 +-
 iris/_CoqProject     |   1 +
 10 files changed, 1327 insertions(+), 462 deletions(-)
```

## Outside the Echo files: ONLY the one-liners (verified with
`git diff origin/main -- iris/UShLine.v iris/UShOut.v iris/EchoLinksLine.v`)
- `iris/UShLine.v:1087` (`ush_read_recv_leaf_holds`): the `read_ret`
  destructuring pattern `"(#Hcs & #Hps & #HE & %Hbd)"` -> `"(#Hcs & #Hps & #HE & %Hbd & _)"`.
- `iris/UShOut.v:130,133`: `sh_pro_stage : length (proc_upto [3%nat] [] (S 0%nat)) = 18%nat`,
  `sh_space_stream : proc_upto [3%nat; 0%nat] [] (S 0%nat) !! 19%nat = Some sh_space_b`.
- `iris/EchoLinksLine.v` `ewc_ban_done_line`, proof only (6 lines: destructure
  `wr_banp .. 18`, `iExists (ps' ++ [3%nat])`, `wr_ban_done`).
- `iris/_CoqProject`: the one bare row `EchoLinksBan.v` after `EchoLinksLine.v`.
NOTHING in UShPanic.v, UkSh*.v, UInit*.v, UserConsole.v or any other step-3 file
had to change; a grep of step 3's changed files for every renamed/changed
name (`wr_owed_round0`, `wr_ban_pro`, `wr_ban_byte`, `pro_of_banner`,
`pro_open_replicate`, `pro_of_replicate_*`, `pcount_zero`, `turn_update`,
`pending_nonnil`, `sess_n_nonnil`, `read_ret` patterns, prologue literals)
finds only the two UShOut literals above.

## GATE (build `pa3-5`, the full EchoDisc cone after the rebase)
- COMPILED=38, `grep -c "^Error" /tmp/pa3-5.log` = 0, EXIT=0.
- VM `make -f CoqMakefile -n` prints 0 `ROCQ compile`.
- VM `make audit-only 2>&1 | grep -v '^make\|^cd ' | md5sum` = 57f7327206c4b276d05035342fea8ecf (the thirteen).
- `python3 tools/lemma_diff.py --ref origin/main` (against eab906990): 7 GONE,
  no Admitted/admit/Abort, no new axiom.  Justified: `pro_of_banner` (false at
  the new `pro_of`), `pro_of_replicate_banner`, `pro_open_replicate`,
  `pro_of_replicate_length`, `pro_done_replicate` (an open round is no longer
  `replicate j 1`; the `pro_fail` family -- `pro_fail_S`, `pro_fail_cont`,
  `pro_done_fail`, `pro_of_fail_length`, `pro_of_fail_banner` -- replaces them),
  `pcount_zero` (false at `ps = []`, no consumer), `pro_of_replicate_snoc`
  (false; `pro_of_fail_snoc` replaces it).  None had a consumer outside the
  Echo files.
- No `Admitted` in any of the ten changed files; no `∨ True`.
- `run-on-gcp --check-dumps` RC=0.

## State for the coordinator
The lane is complete and green on main `eab906990`: the trusted diff of report 1
(section 2, incl. the WIDENING note for the owner: the predicate admits every
word over {1,3} before the round's ending letter 0/2), the step-3 deliverables
(`EchoLinks.echo_prompt_dollar_ban` / `EchoLinksBan.echo_prompt_dollar_ban` to
pay the shell's '$' from `ewc_ban v n 0`; `EchoLinks.ewc_ban_owed`;
`EchoLinks.ewc_owed_read_taint` / `EchoLinksBan.ewc_line_read_taint` /
`EchoLinksBan.ewc_ban_read_taint` to refute an untainted read at an unwritten
prompt), and EchoLinksPro at the banner letter (report 2).  Reports 1-3 are in
this scratchpad as `prologue-alts-3-report.md`, `-2.md`, `-3.md`.
