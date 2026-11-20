# Source map: open arithmetic of the actual sparse pair and field cons

Paper 16 `sections/ordinals.tex` 12–29 and 70–76 use literal finite syntax,
all finite lexical contexts, and numerical witnesses for the finite
quotient and positive paths. Paragraph 84–98 requires arithmetic definitions,
and 112–127 uses function-side path transport.

The repository's selected current codec `NumberedWindowPairAlgorithm.pair`
is exactly `(x+y)*(x+y)+x`, with gaps in range; it is not the unrelated
Mathlib `Nat.pair` used in the earlier generic list implementation.
`NumberedWindowFieldAlgorithm.pack` has nil zero and cons
`pair head (pack tail) + 1`. The same encoded list layout is used for
ordered path certificates. The new append-only `NumberedWindowInternalSparsePair`
uses the retained literal source Program addition/multiplication projectors
and successor, with the same argument order and the same formula compiler.

`PairValue` and `FieldConsValue` state the exact unconditioned numerical
equalities for the chosen literal AST, including when the supplied tail is
an arbitrary natural. `OpenPairGraph` and `OpenFieldConsGraph` ask for actual
finitary ID1 proof trees equating each unchanged compiled graph with its
arithmetic term graph, at every open term. `OpenPairInjective` and
`OpenFieldConsInjective` ask for actual object implications with shared output.
`OpenFieldConsTailDecrease` asks for actual nonzeroness and strict raw tail
decrease for a certified cons. Existing square intervals, order and addition
cancellation will supply arithmetic reasoning without identifying the two
pairing algorithms.

This supports later decoding and raw-certificate induction. It does not
assert that nonzero codes always parse, give the inverse of the actual
bounded optional decoder, change the accepted positive program or selected
sourceBody, discharge local hop compatibility, lift a path, or establish
the numbered ID1 accessibility lemma.
