# Project: the echo application at ANY disciplined line

Design of record: [`../design/applications.md`](../design/applications.md) for
the application seam, [`../completed/app-echo.md`](../completed/app-echo.md) for the theorem this
generalises.

The landed theorem is about `echo hello world`, typed over and over.

**THE TARGET IS A SESSION IN WHICH EACH ROUND TYPES ITS OWN LINE** —
`echo foo` answered by `foo`, then `echo bar baz` answered by `bar baz`, and
so on. NOT `∀ ws, <the theorem at that one line>`: quantifying the whole
session over a single word list still says the user types the same thing
every round, which is the hard-coding, only hidden behind a binder.

The distinction decides the work. Generalising WHICH line is a statement-level
change and is essentially done (below). Generalising so that each ROUND
carries its own line is a change to the SESSION MODEL, and that is where the
remaining cost is.

**The method is IN-PLACE.** A general lemma may be developed in a fresh file
and then moved in, but the specialised thing it replaces is DELETED: no
literal definition survives beside the structured one, and no bridge lemma
exists whose only job is to connect the two. A `vm_compute` at a literal is a
proof worth exactly one command line.

## The vocabulary

- **[`iris/LineWords.v`]** — a line IS a list of WORDS joined by single spaces
  and closed by the newline `gets` keeps (`wl_line`). Word `i` sits at
  `wl_off` and is named by token `i` of `wl_toks`. A word is nonempty and
  ALPHANUMERIC (`wl_wf`), stated positively so that everything the line must
  avoid is a consequence: `wl_line_byte_val` reads every byte of the line
  numerically and `wl_line_nl_last` says the only newline is the last.
  Depends on stdpp alone, so `EchoDisc.v` spells its line with it.
- **[`iris/UkShWords.v`]** — what sh's lexer makes of such a line, for an
  arbitrary word list: `wl_no_symbols`, `wl_tokens` (one `UshpTokCons` per
  word, `UshpTokNil` on the newline) and the cut `wl_cut_in`/`wl_cut_end`.
  `wl_alnum_plain` is where the discipline's positive condition becomes the
  lexer's negative one.

The tokenization induction runs on `wl_tail`, whose offset always points AT a
blank — which is where `UshpTokCons` leaves the scan — so the first word is
the only case outside it.

## Landed

- `EchoDisc.echo_line` IS `wl_line echo_ws`; `echo_line_words` is its one
  sanctioned unfolding and the line is `Opaque` past it. Its byte-level facts
  (`echo_line_byte_val`, `echo_line_nl_last`) are instances, and the five
  consumers that used to case-bash seventeen literals — no carriage return, no
  erase byte, no `^D`, no NUL, no early newline — now spend one `lia`.
- `UkShEcho.echo_toks` / `echo_off` / `echo_alen` ARE `wl_toks` / `wl_off` /
  the word's length. `echo_toks_lookup` is `wl_toks_at_lookup`; the lexing and
  cut obligations are `wl_tokens` / `wl_cut_*` applied.
- The transcript layer (`EchoOut`, `EchoOutPure`, `EchoLinks*`, `UEchoOut`)
  no longer knows the line's length is 17: it spends `echo_line_pos`, which is
  `wl_line_pos` — every line carries its newline.
- **ECHO'S OUTPUT IS THE LINE MINUS ITS COMMAND NAME.**
  `EchoDisc.echo_line_out := wl_line (drop 1 echo_ws)` and the good line
  alternative is `echo_line_out ++ "$ "`. `UShEcho.echo_out` is deleted, and
  `UShEchoOut`'s bridge is `echo_alt0_word` — word `k` of the tail and word
  `S k` of the line are the same byte of the same word.
- **THE EXEC'D KEY'S ARGV READING IS GENERAL.** `UShEcho.echo_key_args`
  quantifies over `(na, alen, afun)`; its one side condition is that no pushed
  byte is a NUL. The addresses come off `KexecDefs`' push geometry
  (`kxc_sp_anti`, `kxc_sp_range`, `kxc_argc_bound`, `kxc_len_bound`), which is
  where "the string is short" becomes a stated inequality.
- The cursor laws a write chain over the words needs: `wl_off_S_at` (the next
  word starts one blank past this one's end), `wl_line_sep` (a separator
  follows a word while another word remains), `wl_off_last` + `wl_line_nl_at`
  (the last word's end IS the body's end, which is where the newline is).
- **ECHO'S WRITE CHAIN IS AN INDUCTION OVER THE WORDS.**
  `UEchoOut.echo_out_argv` says argv IS the line's words and argument `i` sits
  where the output join puts it (`EchoDisc.echo_ocur`);
  `kecho_pay_of_link_from` walks them, writing a word and then a separator or
  the closing newline exactly as `echo_out_sep` / `echo_out_last` decide. The
  two bytes echo writes that are not argv's ARE `wl_sp` and `wl_nl`. The exit
  payload's cursor is `length echo_line_out`, not 12.
- **THE LITERAL READINGS ARE GONE.** `echo_off_1`/`_2`, `echo_alen_1`/`_2` and
  `echo_alen_le5` are deleted — nothing reads an argument's offset or length
  as a number any more. What remains is `echo_off_0 = 0` (true of every line,
  `wl_off_0`) and `echo_alen_0 = 4` (the COMMAND NAME, which stays "echo").
- **THE ENTRY'S STACK ROOM IS AN INEQUALITY.** `echo_sp_final`'s
  `kxc_sp_final 0x4000 alen 3 = 0x3FB0` is gone. `KexecDefs.kxc_span` /
  `kxc_sp_ge` / `kxc_sp_final_ge` bound how far down the push can reach —
  each argument costs its bytes, its NUL and at most fifteen of alignment;
  the vector its words and fifteen more — and `UShEcho.echo_argv_fits` is
  the side condition that earns echo's twelve-word frame its room. A line
  long enough to crowd that frame off the stack page is a line the claim
  must not be about, and now it says so.
- **THE EXEC CHANNEL COUNTS TO `length echo_ws`.** `echo_args_det`,
  `echo_argv_is`, `UShEchoOut.echo_out_argv_of_image` and `UShEchoPay`
  state the count and the per-index rows at the word list; the `Hna`
  derivation counts the vector's arguments to it by the same NULL-terminator
  argument as before, and `echo_ws_lt10` is what puts the vector's own
  addresses in machine range. No statement in the exec chain says 3.
- **THE ARGV NODE IS READ OUT OF THE HEAP BY INDUCTION.**
  `UShEcho.echo_node_row` is one argument's four rows and
  `echo_node_rows_of_cmd` inducts on the count; `echo_node_img` is stated
  at `length echo_ws`. This was twelve `iDestruct`s at indices 0/1/2.
  `uheap`'s readings are pure, so the heap survives the induction.
- **THE ARITY IS THE WORD LIST'S, up to the node.** `UkShEcho`'s argv-node
  vocabulary — `echo_off_lt`, `echo_toks_lookup`, `echo_cmd_args_length` /
  `_lookup`, `echo_argv_bytes`, `echo_cmd_str` / `_word` / `_cap` — is
  stated at `length echo_ws`, not 3. `EchoDisc.echo_ws_pos` and
  `echo_ws_lt10` name the two bounds a caller owes.
- **THE LENGTH IS GONE.** Three sites still name 17, and each is a
  deliberate one: the two anti-vacuity demos at a literal wire
  (`EchoOut.v`, `EchoLinksPro.v`), and `UkSh`'s check that the line fits
  `getcmd`'s buffer — a SIDE CONDITION on the line, flagged as such in
  place. `UkSh`'s three closed `forallb`s over seventeen indices are gone:
  its byte rows are `EchoDisc.echo_line_byte_nl` / `_ncr` / `_nonzero` and
  `echo_line_nl_val`. `ush_echo_first` stays literal on purpose — it is the
  COMMAND NAME's first byte.
- **Formerly:** `UConsLine.ush_disc_line`
  divides by `length echo_line`, `UShEcho.echo_line_nonul` and
  `UkShEcho.echo_off_lt` are stated at it, and `ush_line_toks` reports it —
  none of them says 17. `EchoDisc.echo_line_nl_at_end` is where the closing
  newline is, positionally.
- **THE WIRE SAYS WHAT WAS TYPED.** This is the fact the whole target rests
  on: a claim "echo prints back whatever you type" is empty unless the
  observer can recover WHAT was typed, and with the line hard-coded that
  question never arose. `LineWords.wl_line_det` settles it — two lines
  followed by two remainders make the same wire only if they are the same
  line and the same remainder. Its core is one splitting lemma,
  `wl_split_pred`: a run of bytes satisfying `P` followed by something that
  does not start with `P` splits uniquely. Both parses are instances — a
  WORD ends at the first blank (`P = wl_alnum`) and a LINE ends at the first
  newline (`P = wl_body_byte`) — because a word is alphanumeric and both
  separators are not. `wl_line_prefix_det` and `wl_line_of_wire` are the
  forms the discipline spends, the prefix witness folded into the remainder.
- The assumption audit is unchanged throughout (`make audit-echo-only`,
  fourteen assumptions, md5 `a78bf9a051fb56b084795d782df04045`).

## The ruling on the line choice (owner, this lane), and where it landed

The claim used to read WHICH alternative ran off ONE byte of the wire —
`h`, `e`, `$`, `f` are distinct. That is a property of what echo happens to
print, and at an arbitrary line it fails.

**Ported down, not side-conditioned** — and the port turned out to pay for
itself. `EchoDisc.line_alts_of_prefix_det` states prefix-freeness at ANY
line, and proving it in the word vocabulary collapses the side condition to
two inequalities:

```coq
drop 1 ws <> dg_exec    (* [exec; echo; failed] *)
drop 1 ws <> dg_fork    (* [fork] *)
```

**You may type anything except `echo fork` and `echo exec echo failed`.**

That reduction is not a coincidence to be worked around: sh's two diagnostics
ARE well-formed word lines (`dg_exec_line`, `dg_fork_line` — alphanumeric
words, single blanks, one closing newline), which is exactly WHY they can
collide with echo's output. Stating them in the same vocabulary makes
`wl_line_det`'s parse settle every comparison the output takes part in; the
other six pairs are closed literals. The remaining pair — the bare prompt
against an echoed line — needs no condition at all, because `'$'` is not a
byte any line carries (`line_prompt_not_out`).

`EchoOutPure.line_alts_prefix_det` is now that lemma applied at `echo_ws`,
with the two inequalities discharged by computation; the literal case-bash
over sixteen pairs is gone.

## What is left

The blocker is `EchoDisc.sess_n`, which finds the round by DIVIDING the wire
position by the line length:

```coq
Definition sess_n (ps cs : list nat) (n : nat) : list (bv 8) :=
  pro_of ps ++ alt_seq ps cs (n `div` length echo_line)
            ++ take (n `mod` length echo_line) echo_line.
```

and `alt_blk ps cs i = echo_line ++ alt_cont ps cs i`, the SAME line in every
block. The round list `cs` records only WHICH OF FOUR OUTCOMES round `i` had.
Division is meaningful only because every round is the same length, so rounds
of differing length break it directly.

0. **THE INPUT PREDICATE IS THE ROOT OF THE HARD-CODING**, and it is one
   line:

   ```coq
   Definition disc_seg (seg : list mobs) : Prop := star_prefix echo_line (ins seg).
   ```

   `star_prefix pat l` says `l` is a prefix of `pat` REPEATED. The general
   form is a prefix of a CONCATENATION of lines, which is
   `LineWords.wl_lines`, already landed with its determinism.

   **It must stay DECIDABLE.** `EchoDisc.disc_seg_dec` feeds
   `disc_seg'_dec` -> `disc_dec`, and `EchoOut.v:2310` spends
   `decide (disc h)` inside the taint ghost state. `star_prefix` got
   decidability free from a closed-form `take`; `wl_lines` will not, so
   this needs a PARSER: split the input at newlines, each complete segment
   being a valid body and the trailing one a valid partial. A valid body is
   `[]`, or alphanumeric runs separated by SINGLE blanks with no leading or
   trailing blank; a valid partial is the same minus the trailing-blank
   ban. Uniqueness of the parse is already proved (`wl_body_inj`), so what
   is owed is existence-decidability, not well-definedness.
   Do NOT reach for a bounded search over word lists instead: it is finite
   but astronomical, and the anti-vacuity demos `vm_compute` through this.
1. **THE ROUND CARRIES ITS OWN WORD LIST.** `cs : list nat` becomes a list of
   rounds, each a word list and an outcome; `alt_blk` opens with
   `wl_line` of that round's words.
2. **THE ROUND INDEX BECOMES A CUMULATIVE OFFSET.** `n `div` length echo_line`
   / `n `mod` length echo_line` become a walk over the rounds' lengths.
   `LineWords.wl_lines_prefix_det` is the law that stands in for the
   division: the rounds do not have to be COMPUTED from a position,
   because a wire already determines them.
   **This is the bulk of the work**: ~400 sites over 11 files, ~110 of them in
   lemma STATEMENTS and ~290 inside proofs. The proof-body ones are the
   expensive half and not for a dull reason — `lia` knows div and mod
   natively, so those sites are free today; a cumulative-offset function is
   opaque to `lia` and each becomes a lemma application. `EchoOut.v` alone
   holds 164.
3. **THE ITERATED CLAIM.** The Iris side (`UShLine`, `UShOut`, `UkShLoop`)
   must carry the remaining word lists in the loop invariant rather than
   re-proving one fixed round. NOT YET SCOPED.
4. **THE CALLER'S BOUNDS**, unchanged from before: `EchoDisc.echo_ws_pos` and
   `echo_ws_lt10` name two (the line has a command name; fewer words than
   sh's MAXARGS). Still unnamed: the line inside `getcmd`'s 100-byte buffer
   (flagged in place at `UkSh`) and the console's 128. The argv block's fit
   inside exec's stack page is already an inequality
   (`KexecDefs.kxc_len_bound`).

## The swap test, and what it measured

Point `EchoDisc.echo_ws` at a DIFFERENT word list and rebuild. Run at
`[echo; hi; there; you]` — four words where the landed line has three, of
lengths 4/2/5/3 where it has 4/5/5 — the whole echo cone went green except
for sites that are deliberately AT a literal, plus exactly two real
findings, both since fixed:

- `UConsLine.ush_echo_tokens` named the token list as `[(0,4);(5,10);(11,16)]`.
  It names `wl_toks echo_ws`, and `UkShEcho`'s bridging `replace` is gone.
- `EchoLinksLine`'s block end was `length (line_alts !!! 0) - 2 = 12`. It is
  `length echo_line_out`, via the new `EchoDisc.line_alts_0_length` — the
  alternative is the output and then the prompt.

WHAT LEGITIMATELY NEEDS RETARGETING at another line, and is not a defect:
`echo_line_length`, `echo_line_string`, `echo_line_out_string`/`_length`,
`echo_ws_length`, `EchoLinksLine.line_alts_len0`, and the anti-vacuity
demos that embed a literal wire (`EchoOut.pro_choice_round1_live`,
`EchoLinksPro.wr_owed_ambiguous`, `EchoDisc`'s five `demo_seg*`). Those are
transcription checks and satisfiability witnesses; at a parameterized line
they become computations at whatever instance is supplied.

RE-RUN IT after any further structural work — it is the cheapest check
that the cone has not re-acquired a literal dependence, and it found two
that reading the code had missed.

## The two traps this lane keeps walking into

Both are in [`../durable-notes.md`](../durable-notes.md) under "Arithmetic":
`rewrite !length_app` takes a structured line apart and `Opaque` does not stop
it; `vm_compute in H` changes the atom `lia` was going to match.
