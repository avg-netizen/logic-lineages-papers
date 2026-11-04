# Context-uniform raw presentations of the original decoders

These six targets recover exactly the raw type/code data of the existing
`decodePacked`, `decodePackedNumber` and `decodeUniverse` outputs, with failure
preserved. Their result type is the fixed product `Ty × Code (Fin n)`, so the
binder context can vary as an ordinary input to the primitive-recursive map.
Signature size and arity remain explicit fixed parameters.

The implementations reuse the already checked joint-context validity Booleans
and original raw parsers. They do not infer uniform computation from the old
pointwise packed-decoder results. Every successful pair is calibrated to the
actual dependent typed decoder followed by `packedCode`; malformed types,
variables, arities, argument spines and numeric inputs retain rejection.

This is the decoding interface required by `stepTest` when `focus` discovers a
different `holeGamma` beneath lambdas. It supports paper06's actual auxiliary
certificate relation, including the arithmetic relation discussion at lines
551–556 and the simulation statement at lines625–658. Effective focus/plug,
context-uniform selector and Mul computations, step/edge/path checking and
arithmetic formulas remain separate targets. No original source statement is
promoted by the decoder component alone.
