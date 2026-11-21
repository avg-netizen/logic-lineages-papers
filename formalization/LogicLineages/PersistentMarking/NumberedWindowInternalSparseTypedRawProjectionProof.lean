module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawProjectionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem projectOne (p : Program 1) (slot : Fin 5) (xs : Fin 5 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph
      (.composition p (fun _ : Fin 1 => .projection slot)) (suc z) xs)) ↔
    Nonempty (Derivation body Γ (programGraph p (suc z) ![xs slot])) := by
  let selectors : Fin 1 → Program 5 := fun _ => .projection slot
  let ys : Fin 1 → OTerm α := ![xs slot]
  have hg (i : Fin 1) : Nonempty (Derivation body Γ (programGraph (selectors i) (ys i) xs)) := by
    obtain rfl := Fin.eq_zero i
    exact projectionValue slot xs
  exact ⟨fun h => compositionRecover p selectors (suc z) xs ys h hg,
    fun h => compositionValue p selectors (suc z) xs ys h hg⟩

theorem projectThree (p : Program 3) (i j k : Fin 5) (xs : Fin 5 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph
      (.composition p ![.projection i,.projection j,.projection k]) (suc z) xs)) ↔
    Nonempty (Derivation body Γ (programGraph p (suc z) ![xs i,xs j,xs k])) := by
  let selectors : Fin 3 → Program 5 := ![.projection i,.projection j,.projection k]
  let ys : Fin 3 → OTerm α := ![xs i,xs j,xs k]
  have hg (atSlot : Fin 3) : Nonempty (Derivation body Γ (programGraph (selectors atSlot) (ys atSlot) xs)) := by
    exact Fin.cases (projectionValue i xs)
      (Fin.cases (projectionValue j xs) (Fin.cases (projectionValue k xs) (fun e => Fin.elim0 e))) atSlot
  exact ⟨fun h => compositionRecover p selectors (suc z) xs ys h hg,
    fun h => compositionValue p selectors (suc z) xs ys h hg⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawProjectionProof
