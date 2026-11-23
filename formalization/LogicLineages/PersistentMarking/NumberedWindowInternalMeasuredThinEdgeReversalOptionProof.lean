module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalOptionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (optionAtSlot compareOptions)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalMeasuredThinEdgeReversalTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem slotGraph (C : Program 3) (s : Settings) (i : Fin 2) (out : OTerm α)
    (xs : Fin 2 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph (optionAtSlot C s i) out xs)) ↔
      Nonempty (Derivation body Γ (programGraph (coverOption C s) out ![xs i])) := by
  have projections (k : Fin 1) : Nonempty (Derivation body Γ
      (programGraph (.projection i) ((![xs i] : Fin 1 → OTerm α) k) xs)) := by
    obtain rfl := Fin.eq_zero k
    exact projectionValue i xs
  constructor
  · intro h
    exact compositionRecover (coverOption C s) (fun _ => .projection i) out xs ![xs i] h projections
  · intro h
    exact compositionValue (coverOption C s) (fun _ => .projection i) out xs ![xs i] h projections

private theorem tupleTwo {T : Type} (values : Fin 2 → T) : ![values 0,values 1] = values := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem reverseOptions : ExactOptionReversal := by
  intro C s body α Γ a b
  let accept := programGraph (compareOptions C s) (suc z) (exchangeTape a b)
  let Δ := accept :: Γ
  have h : Derivation body Δ accept := Derivation.hypothesis List.mem_cons_self
  have reverse : Nonempty (Derivation body Δ (programGraph (compareOptions C s) (suc z) (exchangeTape b a))) := by
    apply programCompositionCases equalityTest ![optionAtSlot C s 0,optionAtSlot C s 1]
      (suc z) (exchangeTape a b) _ ⟨h⟩
    intro β j values Θ _ result fields
    simp only [programRename,exchangeTape,binaryInputsRename,sucRelabel,zRelabel]
    rw [sucRelabel,zRelabel,← tupleTwo values] at result
    obtain ⟨same⟩ := equalityOfAcceptance (values 0) (values 1) result
    have left := fields 0
    have right := fields 1
    simp only [exchangeTape,binaryInputsRename] at left right
    let xs := exchangeTape (a.relabel j) (b.relabel j)
    let ys := exchangeTape (b.relabel j) (a.relabel j)
    have la := (slotGraph C s 0 (values 0) xs).mp left
    have rb := (slotGraph C s 1 (values 1) xs).mp right
    apply compositionValue equalityTest ![optionAtSlot C s 0,optionAtSlot C s 1] (suc z)
      ys ![values 1,values 0] (equalityOfEqual _ _ ⟨symm same⟩)
    intro i
    exact Fin.cases ((slotGraph C s 0 (values 1) ys).mpr rb)
      (Fin.cases ((slotGraph C s 1 (values 0) ys).mpr la) (fun k => Fin.elim0 k)) i
  obtain ⟨reverse⟩ := reverse
  exact ⟨Derivation.implicationIntroduction reverse⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalOptionProof
