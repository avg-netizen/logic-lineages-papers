module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFieldsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases moveBit)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev rawBottom {α : Type} (cod : OTerm α) : OTerm α := stateTerm (numeral 3) cod

/-- Bind the original source's four actual raw fields. The successful
source guard yields both its literal shape and all genuine selector
calls, even for open variables. -/
theorem sourceParts (q w r : OTerm α) (goal : Formula α)
    (source : D B Γ (bit sourceIsAux ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod fn arg : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (auxiliaryTerm dom cod fn arg)) →
      Reports B Δ (q.relabel j) cellTail [dom,cod,fn,arg] →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply nodeAtCases 6 4 0 ![q,w,r] goal source
  intro β j Δ xs keep size shaped reports
  rcases xs with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨arg,_ | ⟨extra,rest⟩⟩⟩⟩⟩ <;> simp at size
  exact use β j Δ dom cod fn arg keep shaped reports

/-- At an auxiliary source a success of the physical beta observation
is a lambda-header call on the actual original function selector. -/
theorem exact_OpenAuxiliaryBetaHeader (q w r : OTerm α) (goal : Formula α)
    (source : D B Γ (bit sourceIsAux ![q,w,r]))
    (header : D B Γ (bit functionLambdaHeader ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod fn arg : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (auxiliaryTerm dom cod fn arg)) →
      D B Δ (unary lambdaHeader (suc z) fn) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply sourceParts q w r goal source
  intro β j Δ dom cod fn arg keep shaped reports
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  have selected := onTape (field 2) 0 fn xs reports.2.2.1
  have move := moveBit functionLambdaHeader q w r j Δ keep header
  have result : D B Δ (unary lambdaHeader (suc z) fn) := by
    apply compositionRecover lambdaHeader ![frameSlot 2 0] (suc z) xs ![fn] move
    intro i
    obtain rfl := Fin.eq_zero i
    exact selected
  exact use β j Δ dom cod fn arg keep shaped result

/-- At an auxiliary source a success of the physical bottom observation
is exact raw target equality at the same actual result type field. -/
theorem exact_OpenAuxiliaryBottomEquality (q w r : OTerm α) (goal : Formula α)
    (source : D B Γ (bit sourceIsAux ![q,w,r]))
    (target : D B Γ (bit targetBottom ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod fn arg : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (auxiliaryTerm dom cod fn arg)) →
      D B Δ (eqn (r.relabel j) (rawBottom cod)) → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  apply sourceParts q w r goal source
  intro β j Δ dom cod fn arg keep shaped reports
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  have selected := onTape (field 1) 0 cod xs reports.2.1
  have emitted : D B Δ (programGraph expectedBottom (rawBottom cod) xs) :=
    emitGraph _ _ (numeral 3) cod xs (literalGraph 3 xs) selected
  have move := moveBit targetBottom q w r j Δ keep target
  have result : D B Δ (eqn (r.relabel j) (rawBottom cod)) := by
    apply equalityOfAcceptance
    apply compositionRecover equalityTest ![.projection 2,expectedBottom] (suc z)
      xs ![r.relabel j,rawBottom cod] move
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases emitted (fun k => Fin.elim0 k)) i
  exact use β j Δ dom cod fn arg keep shaped result

#print axioms sourceParts
#print axioms exact_OpenAuxiliaryBetaHeader
#print axioms exact_OpenAuxiliaryBottomEquality
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFieldsProof
