# Paper 16: conditional full-prefix orbit inference on a true native index order

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
lines 458–498, convention (I) and the actual finite-type iterator's
carrier reasoning. This packet factors the order inference without using
`Ordinal` or the low-memory-unavailable native ordinal realization/rank gate.

* `FullPrefixOrderOrbitProof` defines the original index cases from the
  actual strict relation: no predecessor, greatest predecessor, and
  nonempty prefix without a greatest predecessor. The orbit is supplied
  with zero, successor and true full-prefix IsLUB equations. The caller
  supplies actual seed realization, backward closure, action of the
  actual step, and closure of the same realization relation on one term
  under the actual full prefix at a limit. The last law is quantified
  independently of the chosen orbit. In the limit proof **every** earlier
  orbit value is transported to the same current carrier before applying
  closure; no cofinal subsequence is used, and f and the orbit need not
  be monotone. Well-founded induction proves both the same-stage result
  and realization of all earlier stages by each later carrier.
* `NativeIndexedFullPrefixOrderOrbitProof` derives the three required
  edges from the checked original `NativeIndexedCarrierChecks.exact_IndexedCarrier`:
  actual seed, actual earlier indexed carrier, and actual step applied to
  that earlier carrier are all strictly below the same current term. It
  uses literal typed `indexedW` via `indexedTerm`, one actual P/U pair and
  the exact supplied strict-preserving native index map. The equality
  case is not an artificial strict edge.

The remaining hypotheses are genuine: well-foundedness of the source
order, its true NativeBelow preservation, actual full-prefix equations
and relation-lifting laws including seed and step. No construction of
ordinal-valued orbits, countable supremum realization theorem, native
rank exhaustion, the original closed iterator beta wrapper, or Simmons
calibration is asserted. No actual Ordinal import.
