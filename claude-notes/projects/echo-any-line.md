# Project: the echo application at ANY disciplined line

Design of record: [`../design/applications.md`](../design/applications.md) for
the application seam, [`app-echo.md`](app-echo.md) for the theorem this
generalises.

The landed theorem is about `echo hello world`. The target is
`∀ ws, wf ws → <the same theorem at that line>` for a word list of short
alphanumeric words — which is what a console session can actually type, and
what makes the claim worth more than one literal.

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
- The assumption audit is unchanged throughout (`make audit-echo-only`,
  fourteen assumptions, md5 `a78bf9a051fb56b084795d782df04045`).

## The ruling on the line choice (owner, this lane)

The claim used to read WHICH alternative ran off ONE byte of the wire —
`h`, `e`, `$`, `f` are distinct. That is a property of what echo happens to
print, and at an arbitrary line it fails.

**Ported down, not side-conditioned.** `EchoOutPure.line_alts_prefix_det` is
the prologue's whole-block reading (`EchoDisc.pro_alts_prefix_det`) at the
line: the four alternatives are pairwise PREFIX-FREE. That excludes exactly
two outputs — `fork\n` and `exec echo failed\n`, where the observer genuinely
cannot tell echo's printing from sh's own diagnostic — where distinct heads
would have excluded every line whose first printed word begins with `e` or
`f`. The exclusion belongs to sh's diagnostics, not to any letter, and the
property is decidable, so it is a computation at any given line and becomes a
premise once the word list is a parameter.

## What is left

1. **THE SWAP TEST.** Everything in the chain is now structural, so
   changing `EchoDisc.echo_ws` to a different word list and rebuilding
   should go green apart from the checks that are deliberately AT the
   literal. Expected to fail, by design: `echo_line_length = 17`,
   `echo_line_string`, `echo_line_out_string`/`_length`,
   `EchoLinksLine.line_alts_len0 = 14`, and the six `demo_*` anti-vacuity
   segments (they embed a literal wire). Anything ELSE that fails is a
   remaining literal dependence and the next thing to fix. Run it before
   attempting the parameterization — it measures what is actually left.
2. **THE CALLER'S BOUNDS.** `EchoDisc.echo_ws_pos` and `echo_ws_lt10` name
   two of them (the line has a command name; fewer words than sh's
   MAXARGS). Still unnamed: the line inside `getcmd`'s 100-byte buffer
   (flagged in place at `UkSh`) and the console's 128. The argv block's fit
   inside exec's stack page is already an inequality
   (`KexecDefs.kxc_len_bound`).
3. **THE WORD LIST ITSELF.** Once 1-2 are done, `EchoDisc.echo_ws` becomes
   a parameter with `wl_wf`, item 2's bounds and prefix-freeness as its
   premises, and the theorem reads
   `forall ws, ... -> <the claim at that line>`.

## The two traps this lane keeps walking into

Both are in [`../durable-notes.md`](../durable-notes.md) under "Arithmetic":
`rewrite !length_app` takes a structured line apart and `Opaque` does not stop
it; `vm_compute in H` changes the atom `lia` was going to match.
