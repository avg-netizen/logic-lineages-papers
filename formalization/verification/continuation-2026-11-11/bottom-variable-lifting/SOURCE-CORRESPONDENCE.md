# Bottom-or-variable inverse lifting: frozen first packet

Status: six supporting contracts prepared for preflight; proofs are pending.
These do not promote paper06 `lem:id1` or establish internal graph C.

## Exact existing semantics

The source is paper06's numbered auxiliary reduction construction (the paper's
individual Bachmann–Howard upper-bound section and Kop2012 section 5.3), as
already encoded by `NumberedRewriteSyntaxDefinitions`,
`NumberedRewriteReductionDefinitions`, `NumberedFiniteUniverseDefinitions`,
`NumberedUniverseBindingTargets`, and `NumberedPrimarySubstitutionDefinitions`.
No existing declaration or manuscript is edited. All image terms, typed
variables, primitive marks, and primitive multiset rules are literal existing
objects. The substitution has no injectivity requirement.

## Six contracts

1. `ActualLiftBottomOrVariable`: the introduced binder maps to itself; old
   bottom/variable images remain bottom/variable under actual weakening.
2. `ActualBottomOrVariableGood`: for arbitrary K and H, images of variables
   already satisfying K satisfy the existing Good predicate. There is no new
   finite-window assumption on a discarded binder.
3. `ActualSingleBottomOrVariable`: actual singleSubstitution at same-type bottom
   lies in this class, for any binder type.
4. `ActualFiniteMarkInverse`: every actual finiteMark of a substituted source
   has an original marked preimage. The same finite label is retained.
5. `ActualPrimitiveMarkInverse`: the packed version retains the original
   PrimitiveMark constructor and exact transformed endpoint.
6. `ActualPrimitiveMultisetInverse`: map a literal source list, then lift every
   actual primitive multiset transition occurrence-wise. The target preimage
   maps to the exact requested ordered target list; the nonempty removed
   submultiset and all inserted mark witnesses are retained.

## Deliberate boundaries

The next packets will lift WindowStep, Exchange/WindowPrimary, count-preserving
WindowTrace, and quotient successors. Their intended final consequence is
native accessibility preservation under single-bottom substitution, converse
to the accepted ranked-accessibility reflection. Finite S, subtype closure,
original relation orientation, and genuine self-edges will remain unchanged.
Raw inverse lifting needs no universe hypothesis. This packet asserts none of
those later results and makes no native-to-internal arithmetic inference.

Arbitrary GoodSubstitution cannot replace BottomOrVariable: a variable can be
sent to an ordinary head and thereby gain a Put step. Fixed-endpoint erasure
reflection is also not claimed: erasure is not injective. The inverse endpoint
is existential throughout.

Definitions, Targets, and Preflight are frozen before candidate implementation.
Only the coordinator runs the fixed serialized native checker and Git actions.
