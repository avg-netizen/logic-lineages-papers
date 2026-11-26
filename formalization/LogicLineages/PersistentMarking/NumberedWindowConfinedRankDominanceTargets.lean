import LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapTargets
import LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankTargets

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankDominanceTargets
open Spine NumberedWindowSimulationData NumberedWindowConfinedRankMap

def OriginalBelow (S : Signature) (target source : Expr) : Prop :=
  ConfinedPair.Strict S source target

def FixedPositiveBelow (S : Signature) (K : List Ty) (τ : Ty)
    (target source : Class S K EmptyContext τ) : Prop :=
  RS S K EmptyContext τ source target

def ConfinedRankBelowFixedQuote : Prop :=
  ∀ S K τ, DecisionSourceUniverse.Closed K →
    ∀ q : GuardedTerm S K τ, (full : Acc (OriginalBelow S) q.val) →
      (numerical : Acc (FixedPositiveBelow S K τ) (quote q)) → full.rank ≤ numerical.rank

def OriginalInitialQuoteRankDominance : Prop :=
  ∀ S q τ, PaperTerm S q τ → Ordinary q →
    ∃ start : GuardedTerm S (TypeSupport.support q) τ,
    ∃ symbolicWF : WellFounded (OriginalBelow S),
    ∃ numericalWF : WellFounded (FixedPositiveBelow S (TypeSupport.support q) τ),
      start.val = q ∧
      (symbolicWF.apply q).rank ≤ (numericalWF.apply (quote start)).rank

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankDominanceTargets
