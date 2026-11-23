# Paper 16: fixed-window ordinal rank dominance from actual local witnesses

Exact first theorem of the existing frozen `NumberedWindowConfinedRankDominanceTargets`
at the rank inequality in `sections/ordinals.tex` 315–327. The proposition
`ConfinedRankBelowFixedQuote` is imported, not restated or changed. It
takes the same literal confined strict source, original closed fixed
window, actual typed canonical positive quotient translation, and
actual source `Acc` and numerical `Acc` witnesses, and compares their
ordinary Mathlib `Acc.rank` values.

The previous two-theorem draft imported global native and numerical
well-foundedness to obtain restricted accessibility. For this first
theorem the supplied source accessibility witness already gives the
restricted one via pinned Lean `InvImage.accessible` along `Subtype.val`.
Predecessor closure supplied by the exact original guard theorem makes
both actual source ranks equal (supporting #522). The existing
source-exact quote/positive-edge map at the initial fixed window
(supporting #521) then gives the actual numerical rank inequality.

The global wrapper `OriginalInitialQuoteRankDominance`, which constructs
both witnesses rather than receiving them, is not in this packet and
still requires its original global suppliers. This proves neither
object-theoretic ID₁ membership nor the Pohlers calibration nor any
individual strict Bachmann–Howard bound. No register promotion.

Proposed single named native gate:
`LogicLineages.PersistentMarking.NumberedWindowConfinedLocalRankDominanceProof`.
The source-static closure is 176 local files vs. 434 in the old
two-theorem draft, without importing global well-foundedness. The old
frozen target itself still imports actual Mathlib Ordinal Rank alongside
legacy sources; this is a materially smaller source closure, not a
prediction that it meets the existing RSS cap. Do not retry an
unchanged resource-stopped root or relax the gate limits.
