# Proposed next comparator: original fresh-variable emitter and open shape

Source: Paper16 ordinals.tex112–127, with original
`NumberedWindowTypedProbe.probe`, `NumberedWindowFreeAddress.freeAddress`,
and checked same-context fresh name/FreeAt (597), original #608 arbitrary
raw option-code calibration, and exact open typed probe assembly.
Scope proposal only. No definitions, proof, native gate, or acceptance
for this next packet. The mixed original selected-typing comparator
remains a separate pending work item.

## Literal program design

* On the external side define `probeFields s q : Option (Nat × Nat × Nat)`
  by the **same** `scalar s q`, original `addressView q`, original
  `arrowView` on that address's result type, and actual
  `freshName` of its literal representative. A successful row is
  `(pack a.context, domain, freshName a.least)`. Here the first Nat is
  the ordered sparse field list code `pack Γ`, not Mathlib
  `Encodable.encode Γ`; the type is the actual original arrow domain,
  and zero is a legitimate type (ground) or packed context (empty).
  Malformed or rejected raw inputs retain none.
* Select four actual unary Program leaves using checked primitive
  recursion of those exact original algorithms: indicator of the same
  successful row and the three total coordinate selections (0 default
  only on none). Separating the indicator from coordinate outputs avoids
  confusing ground/empty zero with rejection. Each gets exact all-raw
  evaluation, not object truth from standard values.
* The explicit emitter e : Program3 uses only original sparse
  `fieldCons` (616), constants, projections, and composition. Its seven
  actual cons operations form the ordered list `[type,name]` then tag0
  free payload, and the ordered list `[packedContext,type,payload]` then
  the tag3 original address. Terminators are exactly 0. No generic
  `Nat.pair`, no sorting or replacement of lexical-port context, no
  least code search.
* The chosen a : Program1 is the checked literal original conditional:
  zero from the indicator returns 0, otherwise evaluate e on those three
  literal selected coordinates and take its successor. Thus `a` satisfies
  the exact original #608 `Encodable.encode (probe s q)` for **every** raw
  q, including malformed addresses, no implicit source admission guard.
  This explicitly constructs one valid witness for the old existential;
  it is not object equivalence to an arbitrary older a with the same
  standard values, not literal equality to old opaque witness code.
  A future typed selection must use this very same chosen a when
  instantiating the accepted same-p/a typing construction; do not swap it
  after deriving a fact about h.

## Proposed exact source comparators

1. **Actual emitter value:** `evaluate e [packedContext,type,name]` is
   exactly `packNode 3 [packedContext,type,packNode 0 [type,name]]` on
   all raw coordinates. Show the literal `freeAddress Γ type name`
   specialization at `packedContext = pack Γ`. The out-value for an
   arbitrary raw code need not decode as a valid lexical stack.
2. **Actual emitter object graph:** in any fixed positive body and every
   arbitrary open context, `programGraph e u [c,t,n]` and the arithmetic
   equation `u = freePackedTerm c t n` are interderivable by genuine
   original ID1 proof trees. The term has the same seven sparse-successor
   pairs, literal tag3 and tag0, same order and duplicated type. Use
   #616's exact open field-cons equation and original graph composition,
   not the natural-number correctness result above.
3. **Original chosen selector:** at given actual Settings s select the
   exact four leaves by the primitive recursive `probeFields` equations.
   The exact a above has all-raw original #608 calibration with no new
   selected source or algorithm premise; retain the actual a AST for the
   object clause. This cannot imply formulas for an arbitrary other a
   merely calibrated to the same numeric function.
4. **Actual open fresh shape:** in every original body/derivation context,
   an actual `freshAt a q u` for the explicit a yields the three scoped
   coordinate existentials with the actual graph of each selected
   coordinate program on the same q, and the actual object equation
   `u = freePackedTerm c t n`. Exclude the zero branch by genuine
   graph uniqueness/PA, open the nonzero branch and original
   composition, and cancel the output successor using the existing
   proof calculus. Use real existential introduction/elimination and
   capture-avoiding renaming, not arbitrary numeric output witnesses.
   This structural theorem can hold for any literal leaves without
   external soundness hypotheses; selection above chooses the actual
   source-calibrated instance.

Still unpaid: internal (not external) proof that c is exactly the lexical
stack code of the source address q and t exactly the source typing σ,
hence a genuine internal typed variable on that stack; original scalar
carrier and no-lambda/direct-reduct/positive-path case analysis; neutral
arrow computability of that same variable, `FreshVariablesComputable`,
actual all-terms accessibility, and BH bound. None are claimed by output
shape or by equality of standard numeral functions.
