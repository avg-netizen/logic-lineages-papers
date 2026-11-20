# Source map: outer cell of the actual sparse ordered-field parser

Paper 16, `ordinals.tex` 12–29, 70–76, 84–98, and 112–127, retains all finite
context syntax, the actual numerical path witnesses, and their use in the
arithmetic path-mirroring argument. The checked implementation commits to
`NumberedWindowFieldAlgorithm`: zero operates as a nil cursor, and a nonzero
cursor n+1 calls the literal bounded `NumberedWindowPairAlgorithm.decode n`.
Failure is absorbing; successful cell decoding sends its second coordinate
to the raw tail cursor and conses its first coordinate to the accumulator.

The selected parser AST keeps the precise old input/output positions:
`cellGood` refuses nil and otherwise calls the real sparse selector after
original arithmetic predecessor; `cellHead` and `cellTail` are the selected
first/second programs at the same predecessor, read only on success.
A false selector does not make the already-literal sparse pairing
surjective. `AllInputCell` retains exact optional equality on zero and
every successor. `ActualFieldStep` additionally states original failure,
successful nil, and all ordered accumulator/state transitions at once.

The three open contracts use the same retained original proof calculus
and actual compiled graph formulas for arbitrary free terms.
`OpenCellSuccess` gives the two-way constructor/destructor graph
interface at the actual `fieldCons` AST from packet 616. `OpenCellFailure`
identifies rejected outer cell selection with absence of a literal
two-witness constructor, including sparse nonzero gaps. `OpenNilCell`
excludes a cons at zero without confusing nil with terminal parser failure.
The open proofs must use ordinary object predecessor cases and the actual
sparse decoder graph proof, not its external all-input truth as a rule.

None of these is a proof about complete `unpack` or a path fold. In
particular a valid first cell can have a recursively malformed tail.
A later checked list recursion or induction packet must treat that tail
and preserve the printed original bounded loop. No old selected AST or
sourceBody has been rewritten, and no numbered theorem is paid here.
