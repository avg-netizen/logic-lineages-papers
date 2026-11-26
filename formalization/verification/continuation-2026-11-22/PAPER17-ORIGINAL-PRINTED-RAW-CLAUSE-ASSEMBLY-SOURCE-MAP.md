# P17: raw assembly of supplied authentic signed row tapes

Printed source: `arithmetic.tex`, `thm:arithmetic`, the original positive
graph prefix and Boolean signed terminal suffix, kept separately.

* Enumerate exactly the original ordered Boolean vectors at the supplied
  terminal length. Filter by the exact positional completion code of the
  original formula, not a short-circuit parse, default bit, or names set.
* The two raw row tapes are supplied inputs. Copy every graph row in its
  original place at the front of every clause and mark it true. Zip the
  terminal rows positionally with all accepted bits. Raw prefix and suffix
  positions and total literal length are proved for each emitted clause;
  repeated rows stay repeated and accepted vectors never truncate a row.
* The full emitted raw ordered family on the encoding of any two typed
  tapes equals the encoding of the existing typed clause family for the
  original formula and polarity. Vector generation, filter, and full
  assembly are primitive recursive.
* This does not produce or validate the supplied row tapes, authorize an
  arbitrary raw formula, or implement graph/terminal row emission from an
  original gate list. It is not an executable original query theorem.
