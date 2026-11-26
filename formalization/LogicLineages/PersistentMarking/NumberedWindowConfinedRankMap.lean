import LogicLineages.PersistentMarking.NumberedWindowFixedConfinedSimulationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankMap
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData

def Guard (S : Signature) (K : List Ty) (τ : Ty) (q : Expr) : Prop :=
  PaperTerm S q τ ∧ Ordinary q ∧ ∀ ρ ∈ TypeSupport.support q, ρ ∈ K

def GuardedTerm (S : Signature) (K : List Ty) (τ : Ty) := {q : Expr // Guard S K τ q}

def below {S K τ} (target source : GuardedTerm S K τ) : Prop :=
  ConfinedPair.Strict S source.val target.val

noncomputable def quote {S K τ} (q : GuardedTerm S K τ) : Class S K EmptyContext τ :=
  let h := NumberedWindowFixedConfinedSimulationChecks.exact_OrdinaryQuoteInSuppliedWindow S K q.val τ
    q.property.1 q.property.2.1 q.property.2.2
  classOf ⟨Classical.choose h, (Classical.choose_spec h).2⟩

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankMap
