# Literal source-arithmetic codec and fixed control compiler

Paper09 `source-realization.tex` lines48–65 and253–289 use finite existential arithmetic over actual ground-source observation atoms, with finite fixed iterations of Phi. This component encodes the already accepted ActualHeadGraph.Arithmetic syntax literally, without adding a graph predicate, evaluator, or runtime variable-iteration constructor.

Expressions retain numeral, shared variable index, addition and numeral scale. Numeric lifting shifts every variable exactly as Expr.lift, preserving repeated indices. Formula coding retains every existing constructor; an observation stores complete source code, context length (the certified context is all ground), ordered argument-expression codes and result-expression code. Its proof of all-groundness is not a runtime field. Fold conjunction/disjunction preserve order and duplicates, including empty truth/falsity.

Phi code copies all four finite exceptional points and the literal successor source branch with its local n+4 constraint. The iteration parameter is a finite compiler input generating exactly that many syntactic copies; it does not become an arithmetic-language primitive. Existing ControlComputability.Phi_primrec supplies the actual Phi computation. Every listed numeric transformation is primitive recursive. Malformed numeric syntax is totalized without semantic-validity claims.

Exact typed calibration, not an identity with unrelated syntax codecs, is required. Numeric unit-elimination-tree expansion and the final original paid B/C head-graph wiring remain separate. No whole paper theorem promotion is claimed here.
