module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationData
public import LogicLineages.NativeModule.PersistentMarking.ConfinedPair

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPositiveSimulationTargets
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NumberedWindowPreservationTargets NumberedWindowTupleTargets
open NumberedWindowOrdinaryTranslation NumberedWindowSimulationData

def WeakResult (S : Spine.Signature) (K : List Ty) (τ : Ty)
    (Q : NTerm) (t : Spine.Expr) : Prop :=
  ∃ T, tr t = some T ∧
    ∃ trace : TypedTrace S K Spine.EmptyContext τ Q T, AdmittedTrace trace

def StrictResult (S : Spine.Signature) (K : List Ty) (τ : Ty)
    (Q : NTerm) (t : Spine.Expr) : Prop :=
  ∃ T, tr t = some T ∧
    ∃ trace : TypedTrace S K Spine.EmptyContext τ Q T,
      AdmittedTrace trace ∧ 0 < rawLength trace

/-- Every sufficiently high realization of the source of the actual
finite original weak derivation. The trace may have no raw edge, but
weakness does not require an empty trace. Both endpoint support guards
stay in exactly the one supplied subtype-closed window. -/
def BudgetedWeakSimulation : Prop := ∀ S K q t (tree : Tree S (.weak q t)),
  DecisionSourceUniverse.Closed K → SymbolicAdmissible K q → SymbolicAdmissible K t →
  ∀ n Q, budget tree ≤ n → Realizes n q Q → WeakResult S K q.type Q t

/-- The actual strict original derivation requires at least one real raw
edge. Primary equivalence edges do not contribute to its raw length. -/
def BudgetedStrictSimulation : Prop := ∀ S K q t (tree : Tree S (.strict q t)),
  DecisionSourceUniverse.Closed K → SymbolicAdmissible K q → SymbolicAdmissible K t →
  ∀ n Q, budget tree ≤ n → Realizes n q Q → StrictResult S K q.type Q t

def PositiveTraceToClassPath : Prop := ∀ S K C τ Q T
    (trace : TypedTrace S K C τ Q T), AdmittedTrace trace → 0 < rawLength trace →
  ∃ hQ : InWindow S K C τ Q, ∃ hT : InWindow S K C τ T,
    RS S K C τ (classOf ⟨Q,hQ⟩) (classOf ⟨T,hT⟩)

def ConfinedOrdinarySimulation : Prop := ∀ S s t,
  ConfinedPair.Strict S s t →
  ∃ Q T, tr s = some Q ∧ tr t = some T ∧
    ∃ hQ : InWindow S (TypeSupport.support s) Spine.EmptyContext s.type Q,
    ∃ hT : InWindow S (TypeSupport.support s) Spine.EmptyContext s.type T,
      RS S (TypeSupport.support s) Spine.EmptyContext s.type (classOf ⟨Q,hQ⟩) (classOf ⟨T,hT⟩)

end LogicLineages.PersistentMarking.NumberedWindowPositiveSimulationTargets
