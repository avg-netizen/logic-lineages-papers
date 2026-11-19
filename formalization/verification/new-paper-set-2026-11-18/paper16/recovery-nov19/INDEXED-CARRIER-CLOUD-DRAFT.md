# Indexed carrier: thin cloud draft, exact target unchanged

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
native lower construction, equations immediately above and proof immediately
below `lem:indexed-carrier`. The owner-frozen 11-pin comparator
`NativeIndexedCarrierTargets.IndexedCarrier` remains unchanged: the index
has actual type `o→o` in the closed native fragment, the original semantic
types translate homomorphically, both template branches are literal, and the
same original strict index edge yields both strict carrier conclusions.

- `NativeIndexedSelectorProof.selectP` marks the original outer application
  and uses its first base occurrence with the one actual owner copy at type
  eta. The returned marked inner application retains both base occurrences,
  so its second occurrence gives the original P by empty-call Select and
  original ordinary reflexivity. Literal support is retained from that
  syntactic occurrence. This does not compose beta steps.
- `NativeIndexedContextThinProof` retains the owner draft's original single
  hole, lambda context and fill equations. It assembles strict context
  stability from the unchanged checked structural strict context proof,
  exact filled endpoint typing and ordinaryhood, and unchanged support
  confinement. This removes unrelated composition imports from the old
  draft (221→125 modules) without replacing the actual typed context, typed
  fills or confined judgment. The owner draft is still present unchanged.
- `NativeIndexedCarrierChecks.exact_IndexedCarrier` invokes that exact
  context edge and the same native carrier theorem (in its new thin proof
  root, using unchanged `NativeCarrierTargets.Carrier`). K-to-P weak
  inclusion, the literal target typing and the support guard all come from
  the original checked/candidate statements, not new hypotheses. The thin
  complete indexed draft has 130 recursive local modules; the earlier import
  pattern would have had 231 and included the stopped carrier leaf.

These are source-preserving drafts. Neither the new thin carrier root nor
this exact indexed endpoint is claimed to have a cloud pass without a
successful native receipt and independent review.
