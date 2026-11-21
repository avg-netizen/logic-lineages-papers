# Paper 16: original physical guarded application frontend (target freeze)

The manuscript's auxiliary application (QU) and finite least-code classes
are in `16-persistent-marking-termination-ordering/sections/ordinals.tex`
(lines 10–29, 70–77, 103–114). The exact executable comparator here is
`NumberedWindowAddressApplication` (`arrowView`, `applyAddresses`,
`application`, `graph`), not a semantic substitute for (QU), not a new
carrier, and not the numbered accessibility target. The later proof of
internal matching at open variables remains separate.

## Actual physical choice

The new `applicationCore least` is the physical **unguarded** (p_0) on
the ordered original tape `[f,u,y]`. It computes the real tag-three/arity-three
test at slots 0 and 1; the real sparse arrow-cell test at slot 0 only; equality
of the two original packed context fields; and equality of the function's
selected domain with the argument's selected result. There is no arrow
condition on the argument. Its last call is the same already verified physical
`outputCore least` (supporting records 717 and 719), with actual projections
`[rawContext f, rawDomain f, rawCodomain f, rawLeast f, rawLeast u, y]`.
The proposed output y itself is unchanged. `applicationGuard i least` is
literally existing `guard i (applicationCore least)`, not a normalization or
an extensional replacement. Existing `guard` uses actual whole-address i at
slot 0 and slot 1 and then this (p_0). The new unguarded (p_0) is not
claimed to equal original opaque old (p_0), either as an AST or numerically.

## Exact all-raw target

`ExactAllInputGuardedApplication` uses the actual source calibration
`evaluate i [q] = (NumberedWindowScalarAlgorithm.scalar s q).toNat` and
`ActualLeastCalibration s least` for the actual packed optional least call.
These are numerical premises only. The exact comparator is
`evaluate (applicationGuard i least) [f,u,y] =
(NumberedWindowAddressApplication.graph s f u y).toNat`, including zero,
malformed f/u, malformed arrow, wrong context/domain, missing least, and
mismatched proposed y. There is no assumed typed or closed window.

* Missing/invalid `addressView`, or its decoded canonical check false:
  the original graph rejects; the corresponding actual i callback rejects.
  The actual source `scalar` is `(addressView q).any (canonical s)`.
* Success of both decoded canonical addresses gives the literal tag-three
  shapes and original raw selectors via
  `InternalFreshProbeParsedEmitterAddressProof.addressCoordinates`.
  Its `arrowMissing` rejects an absent source arrow, and
  `exactCoordinates` exposes the actual selected domain and codomain on a
  successful source arrow. `arrowView` is zero rejection or the original
  sparse-pair decoder on the predecessor.
* At two successful source `contextView`s, literal packed-context equality
  matches equality of the original ordered lists, repeats included.
  `InternalSparseAddressPositiveNumericShapeProof.viewDecoded`,
  `unpackContext`, `sameContext` and `packOfUnpack` justify this without
  changing invalid contexts to `[]`. Selected raw domain versus argument
  raw result is the literal original domain test.
* With guards passed, the 717 output core performs the unchanged
  `packNode 6 [domain,codomain,sourceLeast,argumentLeast]`,
  actual least at the actual unpacked context/codomain, and original
  `packNode 3 [pack context,codomain,k]` only for a successful optional
  least k. The resulting optional value is compared to `some y`, exactly as
  in original `graph`. There is no separate scalar or carrier check at y.

## Exact open target

`ExactOpenGuardedApplication` is a single genuine derivation of both
directions in the same arbitrary positive body and ordinary context, for any
physical `i`, `least` and arbitrary ordinary terms f/u/y. No numerical
calibration, inferred runtime typing, `ValidWindow`, or semantic predicate
reflection enters its premises.

The report retains the actual unit i graph at f and at u, and binds in order
`[ctx,result,dom,cod,fn,arg]` using the original finite object existential
block. The same f and u have actual tag-three unit graphs, actual complete
address selector graphs sharing one `ctx`, and the argument's actual result
is that same source `dom`. It also keeps the actual source arrow unit
and selectors, and the genuine literal object equations
`f = addressTerm ctx result fn`, `result = rawCons dom cod`,
and `u = addressTerm ctx dom arg`. Here `rawCons` is the actual ordinary
polynomial sparse pair plus one; it is not raw equality inferred from Lean
evaluation. The existing 719 `outputReport` uses those exact bound fields
and the unchanged y, retaining one inner genuine existential k with the same
selected `least` graph at `[ctx,cod,auxiliaryTerm dom cod fn arg]` producing
`S k` and the actual equation `y = addressTerm ctx cod k`.

The intended proof (not yet authored) uses the actual conjunction rules and
composition on the same tapes. It opens actual coordinate graphs, recovers
object equality from the real comparisons, and transports the right context
and argument result to the shared witnesses. It uses the retained
`exact_OpenAddressArrowCoordinates`/source equivalent for the function
shell and actual `readNode` plus argument selector graphs for the argument
shell; no argument-arrow theorem is used. It delegates the exact least/output
witness to 719. Conversely the same witnesses supply the two reflexive
comparison graphs, the same physical shape/selector calls, and the actual
six-coordinate return through 719, then the unmodified outer guard using
the two real scalar graphs already in the report. All existential steps
must be genuine finite-binder/ordinary-graph derivations at the same body.

The frozen endpoint does not assert output scalar admission, full matching,
least congruence, functional/unique result, or reinstall at a new tuple.
Existing scalar meanings, fixed-source predicates, original application,
selected p/h/sourceBody and checked files are not modified or transported.
