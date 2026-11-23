# Paper 16: exact repeated drop in the unchanged sparse parser

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex),
74–98 uses original arithmetic certificates. This is a thin recut of a
finite parser-table subargument needed for their real internal graphs.

* [Motive](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParserDropSyntaxProof.lean)
  keeps common original parser parameters. It binds three variable codes:
  lower index, actual lower table output, actual higher table output. An
  object-level proof of the two table observations implies the graph of
  the original `InternalRawListRecursion.drop` at the exact additive gap.
* [Proof](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParserDropProof.lean)
  uses original PA natural induction on gap. At zero, functionality on the
  same table inputs gives the original output. At successor, open the
  genuine intermediate table at one above the lower index, retain the actual
  high table by additive transport, use the smaller gap and the checked
  #1543 physical tail, and compose the original `dropNext`. The parser's
  `scratchTable` and `scratchStep` are unchanged.
* `exact_OriginalSparseParserTableDropAtDifference` uses the existing
  `differenceEquation` to obtain the additive equality from the **actual**
  oriented subtraction graph and an **internal** nontruncation proof
  `lo < suc hi`. It does not reflect numeric truth, assume an arbitrary
  subtraction is a difference, or change the index or table values.
* This is a local proof recut from the established generic ExchangeRowMemo
  argument, not an import of that broad root. It does not yet claim exact
  final row lookup, parser nil/cons, or any numbered proof.

Native author status: source only; two named axiom audits.
