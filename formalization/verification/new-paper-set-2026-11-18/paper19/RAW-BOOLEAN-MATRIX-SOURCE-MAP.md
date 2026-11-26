# Raw Boolean matrix Plan lowering for paper19

The source compiler uses every Boolean node on its actual shared
predecessors, including under negation. The local constraint lists and
globally indexed witness block are the exact `BooleanWire.constraints`,
`BooleanFlatten.compile` and `BooleanPlan.matrixPlan` objects.

This supporting comparator serializes the literal newest-first Boolean
rows and the natural-port reference table. Each Boolean node gets the
same nine ground wires, for an output bit and eight auxiliaries. One
last ground wire supplies the common one. An earlier Boolean reference
uses its position in this same table. The reverse row fold emits
constraints in the exact original order, the same root equality and
all the original existential binders. Literal finitary syntax drives
the compiler, with no decision procedure for the source arithmetic.

The typed endpoint pays all six Boolean node constructors, arbitrary
natural-port sharing, and every valid root. The raw endpoint is total
and primitive recursive on all raw row tables. The separate checked
input frontend will validate ports, backwards references, payloads and
root before using this structural operation.
