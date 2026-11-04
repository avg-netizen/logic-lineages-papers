module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionTargets
public import Mathlib.Logic.Relation

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionFixedWindowTargets
open Source Source.SourceTypeSupport NumberedRewriteSyntax NumberedRewriteReduction
open NumberedOrdinaryWindow NumberedConfinedSourceSimulation NumberedFiniteUniverse
open NumberedQuotientPaths LiteralContexts SourceSimulationCompletion

/-- The same already fixed translation works in any subtype-closed finite
universe containing the source support. These are universe-domain conditions,
not extra source-relation or simulation premises. -/
def AnyFixedUniverseSimulation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (S : List Ty),
    SubtypeClosed (fun u => u ∈ S) →
    ∀ (tau : Ty) (s t : Term (Fin n) arity Gamma tau),
      (∀ u ∈ typeSupport s, u ∈ S) →
      ConfinedStrict above s t →
      InUniverse (symbols n) S (translateOriginal s) ∧
      InUniverse (symbols n) S (translateOriginal t) ∧
      PositivePath (QuotientEdge n arity (symbols n) S above Gamma)
        (tr S ⟨tau,s⟩) (tr S ⟨tau,t⟩)

/-- A later comparison uses the ORIGINAL root's universe, including when its
source has strictly smaller support or a different result type. -/
def OriginalRootWindowSimulation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (rho tau : Ty) (root : Term (Fin n) arity Gamma rho)
    (s t : Term (Fin n) arity Gamma tau),
    typeSupport s ⊆ typeSupport root →
    ConfinedStrict above s t →
    let S := sourceWindow root
    InUniverse (symbols n) S (translateOriginal s) ∧
    InUniverse (symbols n) S (translateOriginal t) ∧
    PositivePath (QuotientEdge n arity (symbols n) S above Gamma)
      (tr S ⟨tau,s⟩) (tr S ⟨tau,t⟩)

/-- A nonempty chain preserves one ORIGINAL root window at every step. Its
endpoints are translated by the same `tr S`, even as their supports shrink. -/
def OriginalRootWindowChainSimulation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (rho tau : Ty) (root : Term (Fin n) arity Gamma rho)
    (s t : Term (Fin n) arity Gamma tau),
    typeSupport s ⊆ typeSupport root →
    Relation.TransGen (fun q r : Term (Fin n) arity Gamma tau => ConfinedStrict above q r) s t →
    let S := sourceWindow root
    PositivePath (QuotientEdge n arity (symbols n) S above Gamma)
      (tr S ⟨tau,s⟩) (tr S ⟨tau,t⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionFixedWindowTargets
