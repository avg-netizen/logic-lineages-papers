# Paper 17: original positive graph and exact ordered Boolean terminal in finite clauses

Printed source: `arithmetic.tex`, `thm:arithmetic`, actual normalized
five-kind computational graph followed by the literal signed plain terminal.

- Retain all actual original graph rows in order, with positive bits
  regardless of the requested terminal polarity. The proof uses
  `ExactPositiveCircuitSnapshots` for genuine normalized graph and exact
  actual rows, not a tautological assumed terminal or a negative graph.
- Enumerate all exact arity Boolean vectors in literal original terminal
  row order; only the original `readBits` interpreter can accept a vector
  at the requested Boolean polarity with no unused bits. Nested not,
  conjunction, disjunction, constants and duplicate positional atoms are
  preserved by that interpreter.
- A branch is the unchanged positive graph prefix plus the exact zipped
  signed terminal suffix; every row must literally have a true admitted
  test, an actual ordered read value, and the requested polarity.
  For any row value snapshot, the recorded bit list matches that ordered
  tape exactly. No erroneous read is treated as test false.
- The final alias is specialized to the actual normalized original printed
  circuit and plain terminal, at a fixed actual valuation. It does not yet
  claim numerical high payments, rank renaming, automatic initial cleanup,
  or mixed-route projection (separate earlier packets), and is not a
  complete decision theorem.
