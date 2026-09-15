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
- The assumption audit is unchanged (`make audit-echo-only`, fourteen
  assumptions, md5 `a78bf9a051fb56b084795d782df04045`).

## What is left

In execution order. The first two are the only NEW proofs of size; the rest is
replacing literal readings with the general ones.

1. **THE NUMBERS.** `UkShEcho.echo_off_0..2` / `echo_alen_0..2` are the
   literal's last foothold. Every use of one marks a consumer that still
   reasons at this line rather than at `wl_off` and `length`; the general
   statement has none, so the lane is done when they are deleted.
   `echo_off_lt` (an argument's bytes are inside the line) is the shape they
   should all take.
2. **EXEC'S STACK ARITHMETIC** (`UShEcho.echo_key_args_holds`). It computes
   `kxc_sp_final 0x4000 alen 3 = 0x3FB0` and the three string addresses as
   closed numbers. `KexecDefs.kxc_sp` is already general in `alen`; what is
   missing is its monotonicity and range against `kxc_stack_ok`, which is
   where "the string is short" becomes a stated inequality rather than an
   arithmetic accident.
3. **ECHO'S WRITE CHAIN** (`UEchoOut.kecho_pay_of_link`). A fully unrolled
   four-write chain at cursor offsets 0/5/6/11/12. It becomes an induction
   over the words carrying a byte cursor; `ech_step` and
   `kecho_w_of_link_data`/`_txt` are already offset-generic, and
   `UkEcho.kecho_pay` is already a fixpoint over the argument list — so is
   `UkEcho.wp_kecho_main`, which walks argv's loop at an arbitrary `args`.
   Nothing about echo's own machine code needs generalising.
4. **THE LINE CHOICE IS READ OFF ONE BYTE** (`EchoOutPure.line_alts_head_det`).
   The four alternatives' first bytes are `h e $ f`; an arbitrary echoed
   string collides with `"fork\n"` on `echo foo` and with
   `"exec echo failed"` on `echo eggs`. Either add "the first word printed
   does not begin with `e` or `f`" as a side condition, or port down the
   prologue's whole-block argument (`EchoDisc.pro_of_prefix_free`), which is
   the cleaner shape. THIS IS A DESIGN DECISION, not labour.
5. **THE CALLER'S SIDE CONDITIONS**, none of which `LineWords`/`UkShWords`
   state: at most `MAXARGS` words (sh's parser), the line inside `getcmd`'s
   100-byte buffer and the console's 128, and the argv block inside exec's
   stack page (item 2's inequality).
6. **`UConsLine.ush_disc_line`** still reads `echo_line !! (i mod 17)`.

## The two traps this lane keeps walking into

Both are in [`../durable-notes.md`](../durable-notes.md) under "Arithmetic":
`rewrite !length_app` takes a structured line apart and `Opaque` does not stop
it; `vm_compute in H` changes the atom `lia` was going to match.
