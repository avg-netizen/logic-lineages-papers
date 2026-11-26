# Finite raw paths and genuinely positive original class certificates

Supporting scope only for ordinals.tex lines 10–76 and 74–92. Retains
the same original fixed signature, subtype-closed type-window where
needed for least reps, de Bruijn finite binder stack, and result type.
No global reachability algorithm, internal arithmetic or ID_1 proof.

NumberedWindowRules.WindowPath is the separately defined source path.
In the empty case its constructor requires admission and equal actual
endpoints, not merely equal types or Primary. Each nonempty certificate
gives the actual next literal vertex and the accepted #454 witness for
the genuine raw step. The checker reuses independent typed endpoint
admission for every edge in the unchanged S/K/Γ/result type.

Class, classOf, ClassEdge and RS are the already existing original
quotient, single raw edge and positive closure in SimulationData.
A supplied class edge names both actual possible representatives,
checks their same typed-window raw edge, and pays the successful
least literal Nat code of each (#452), using explicit some src/dst.
No absent-code equality is sufficient. Consecutive supplied raw
edges may name different but genuinely Primary-equivalent
representatives, identified by their actual equal successful codes.
The arithmetic-data walk carries an explicit intermediate code
per edge. Its empty case is only the final equality test; the public
positive checker requires a nonempty supplied list. It neither assumes
consecutive raw representatives are literal equal nor uses Primary
alone as a positive edge.

ActualCodeAt relates arbitrary Nat inputs to an actual existing
original class through an original admitted representative with a
successful least code; no alternate quotient or definition by
accepted path checking. The contracts relate supplied witness
existence at those arbitrary codes to actual ClassEdge and actual
positive RS; complete same-class code/actual fiber uniqueness is
made explicit. They are not search procedures for unknown witnesses,
bare finite reachability decidability, a claim of finite global
classes, Nat coding of the whole witness yet, or an internal
arithmetic/positive-inductive-definition derivation.
