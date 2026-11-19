# Typed trace, ordinary translation and one reserved mark: source-first only

Source pins cover paper16 `sections/ordinals.tex` and `sections/ordering.tex`,
the literal original six-sort certificates and mark, actual numeric raw
rules/window/primary relation, and these new comparator bytes. This is
neither the full positive simulation nor a ranked quotient/arithmetic
accessibility proof.

| Exact claim(s) | Manuscript match |
| --- | --- |
| LiteralTermVertices, LiteralArgsVertices, JoinTermTraces, JoinArgsTraces | Ordinals 55–58 and 70–76: finite traces carry actual raw steps and finite equivalence witnesses. The term carrier is the existing lexical typed mixed trace. The ordered-base trace uses original `RawArgsStep` and typed `OrderedPrimary`, with no tuple-wide raw rule and no new permutation. Gluing removes the single duplicate joint vertex (edge source list followed by right trace's literal vertex list); actual raw-edge counts add. |
| LiftTypedLambda, LiftTypedAuxFunction | Ordinals 51–58, 219–225 and 271/276: actual lambda body path and actual auxiliary function-side contexts, with original binder/domain/codomain/kept argument. Every new vertex is the literal constructor image, and the original raw count remains exact. There is no auxiliary argument-side raw lifting. |
| WindowPathAsRawTrace | Ordinals 235–253 and 273–275: adapt the already defined actual whole-tuple helper's fixed-window raw path, with all its edges. The new `onlyRaw` certificate forbids any inserted primary equivalence transitions. This step does not attempt to recover path existence by replacing the tuple lemma. |
| ConsTypedTrace, LiftTypedOrdinaryBase | Ordinals 271–291: inside actual base arguments, first perform the verified first-term trace with the rest unchanged, then the verified tail trace with that final first-term fixed. Both use the original list-position raw constructor and ordered primary congruence; map all vertices and preserve the sum of raw counters. Lift the entire identical typed ordered base to the same original ordinary head; equivalent-head swap may only happen in the existing separate primary relation. |
| OrdinaryTrDomain, OrdinaryTrArgsDomain, UniqueOrdinaryRealization, UniqueOrdinaryArgsRealization | Ordinals 228–233 and 267/300: original ordinary syntax only; literal binders, typed free/bound names, original head identity and complete ordered base, including the original application head rather than auxiliary application. The executable partial `tr` is undefined on any marked subtree. Whenever defined it yields the unique realization at every threshold; no hidden selected realization or zero label at a marked head. `ordering.tex` elementary lemma gives ordinary original targets. |
| OneReservedMarkStep | Ordinals 33–37, 60–68 and 280–296, original Strict (and Stat Coverage's literal strict premise): assume the real partial `Spine.mark q = some r`, not an invented head-only case. Preserve the same original lambda prefix. Ordinary omega becomes finite at the lower threshold; an already-numbered leading label is large enough to choose its strict predecessor, regardless of the symbolic mark being identical. The result must pay **both** the primitive decrease witness for Stat and exactly one actual raw step for Strict, ordinary numerical typing/window and actual realization of the literal result at threshold n. Symbolic variables have no mark premise; label zero cannot be reused. |

All typed trace claims use a fixed signature, type window and context,
except the exact lambda binder extension. No claim that these traces
represent an arbitrary original derivation yet. The two real Stat trees
are still retained in the source certificate; the new mark supplier
builds an actual replaced occurrence but does not create a simultaneous
multiset witness or bypass the earlier locality/owner-scope conditions.
No native or proof work before independent source scope and preflight.
