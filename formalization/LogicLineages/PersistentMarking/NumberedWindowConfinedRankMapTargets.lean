import LogicLineages.PersistentMarking.NumberedWindowConfinedRankMap

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapTargets
open Spine NumberedWindowDomain NumberedWindowOrdinaryTranslation NumberedWindowSimulationData
open NumberedWindowConfinedRankMap

def InitialConfinedWindowGuard : Prop :=
  ∀ S q τ, PaperTerm S q τ → Ordinary q →
    DecisionSourceUniverse.Closed (TypeSupport.support q) ∧
    ∃ start : GuardedTerm S (TypeSupport.support q) τ, start.val = q

def ConfinedPredecessorInGuard : Prop :=
  ∀ S K τ q t, Guard S K τ q → ConfinedPair.Strict S q t → Guard S K τ t

def GuardedQuoteLiteral : Prop :=
  ∀ S K τ (q : GuardedTerm S K τ) Q (hQ : InWindow S K EmptyContext τ Q),
    tr q.val = some Q → quote q = classOf ⟨Q, hQ⟩

def GuardedQuotePreservesStrict : Prop :=
  ∀ S K τ, DecisionSourceUniverse.Closed K →
    ∀ source target : GuardedTerm S K τ, below target source →
      RS S K EmptyContext τ (quote source) (quote target)

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapTargets
