module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenProjectionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem projectTwo (p : Program 2) (i j : Fin 4) (xs : Fin 4 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph
      (.composition p ![.projection i,.projection j]) (suc z) xs)) ↔
    Nonempty (Derivation body Γ (programGraph p (suc z) ![xs i,xs j])) := by
  let selectors : Fin 2 → Program 4 := ![.projection i,.projection j]
  let ys : Fin 2 → OTerm α := ![xs i,xs j]
  have hg (slot : Fin 2) : Nonempty (Derivation body Γ (programGraph (selectors slot) (ys slot) xs)) := by
    exact Fin.cases (projectionValue i xs) (Fin.cases (projectionValue j xs)
      (fun e => Fin.elim0 e)) slot
  exact ⟨fun h => compositionRecover p selectors (suc z) xs ys h hg,
    fun h => compositionValue p selectors (suc z) xs ys h hg⟩

theorem projectThree (p : Program 3) (i j k : Fin 4) (xs : Fin 4 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph
      (.composition p ![.projection i,.projection j,.projection k]) (suc z) xs)) ↔
    Nonempty (Derivation body Γ (programGraph p (suc z) ![xs i,xs j,xs k])) := by
  let selectors : Fin 3 → Program 4 := ![.projection i,.projection j,.projection k]
  let ys : Fin 3 → OTerm α := ![xs i,xs j,xs k]
  have hg (slot : Fin 3) : Nonempty (Derivation body Γ (programGraph (selectors slot) (ys slot) xs)) := by
    exact Fin.cases (projectionValue i xs) (Fin.cases (projectionValue j xs)
      (Fin.cases (projectionValue k xs) (fun e => Fin.elim0 e))) slot
  exact ⟨fun h => compositionRecover p selectors (suc z) xs ys h hg,
    fun h => compositionValue p selectors (suc z) xs ys h hg⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenProjectionProof
