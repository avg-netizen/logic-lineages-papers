# P17: exact raw positional read of the original Boolean terminal

Printed source: `arithmetic.tex`, `thm:arithmetic`, the original terminal
formula's separate Boolean witness, after preserving its signed row tape.

* From the literal source `NormalForm.Formula.encode`, generate one
  primitive-recursive postorder opcode tape using the original radix-six
  tags and ordered child decoding. There is one atom opcode per occurrence
  in order, including repeated identical coded atoms; the exact marker
  count is the length of the original ordered atom tape. An atom opcode
  consumes a bit, not an evaluation of its signed arithmetic payload.
* A checked Boolean stack reads both original arms (even for false-AND or
  true-OR), preserves the remaining input tape exactly, and propagates a
  missing bit on either arm as failure. The raw reader is literally equal
  to `OriginalPlainTerminalMatrix.readBits` on the original formula code.
* Final selection requires an empty remaining bit tape. A full exact false
  result remains `some false`; leftover/short tapes are rejected, not
  encoded as polarity. The opcode constructor, reader and final program
  are primitive recursive.
* This supplies only the positional Boolean terminal reader, not the
  original graph-row encoder, signed terminal row emitter/validator,
  assembly of raw original circuit families, or a raw query theorem.
