module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedResultProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue valueUnique equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt)
open NumberedWindowProbeCode (code)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchControlChecks
  (exact_DispatchControlAST exact_DispatchObjectTypeCode)
open NumberedWindowInternalFreshProbeDispatchObjectGraphProof (memberAt dispatchReject)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

section
attribute [local irreducible] programGraph

private theorem verifyTypeLeaf (l : Leaves) (τ : ProbeTy) (q : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (verify l τ) (suc z) ![q]))) :
    Nonempty (Derivation body Γ (programGraph (typeLeaf l τ) (suc z) ![q])) := by
  cases τ with
  | ground => exact h
  | arrow σ τ =>
    rw [verify,exact_DispatchControlAST.2.2.2.2.2] at h
    obtain ⟨d⟩ := conjunctionRecover (typeLeaf l (.arrow σ τ)) (arrowPart l (verify l τ)) ![q] h
    exact ⟨Derivation.conjunctionLeft d⟩

private theorem actualBaseInput (l : Leaves) (τ : ProbeTy) (q : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (typeLeaf l τ) (suc z) ![q]))) :
    Nonempty (Derivation body Γ
      (programGraph l.baseTyped (suc z) ![numeral (typeCode τ),q])) := by
  let t := code τ
  let ps : Fin 2 → Program 1 := Fin.cons (literal 1 t) (Fin.cons (Program.projection (0 : Fin 1)) Fin.elim0)
  have hl : Nonempty (Derivation body Γ (programGraph (literal 1 t) (numeral t) ![q])) := by
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 1 t ![q]
  have hr := compositionRecover l.baseTyped ps (suc z) ![q] ![numeral t,q] h (fun i =>
    Fin.cases hl (Fin.cases (projectionValue (0 : Fin 1) ![q]) (fun k => Fin.elim0 k)) i)
  have hc : t = typeCode τ := exact_DispatchObjectTypeCode τ
  rw [hc] at hr
  exact hr

private theorem acceptedRequest (i : Inputs) (W : List ProbeTy) (τ : ProbeTy) (q : OTerm α)
    (h : Nonempty (Derivation body Γ (typedAt (chosenH i W) τ q))) :
    Nonempty (Derivation body Γ (programGraph requestedTypeTest (suc z) ![numeral (typeCode τ),q])) := by
  let l := chosenLeaves i
  change Nonempty (Derivation body Γ
    (programGraph (dispatch l W) (suc z) ![numeral (typeCode τ),q])) at h
  by_cases hm : τ ∈ W
  · have v := (memberAt l W τ hm (suc z) q).mp h
    have d := actualBaseInput l τ q (verifyTypeLeaf l τ q v)
    change Nonempty (Derivation body Γ
      (programGraph (baseWithResult i.priorTyped) (suc z) ![numeral (typeCode τ),q])) at d
    rw [baseWithResult,exact_DispatchControlAST.2.2.2.2.2] at d
    obtain ⟨p⟩ := conjunctionRecover i.priorTyped requestedTypeTest ![numeral (typeCode τ),q] d
    exact ⟨Derivation.conjunctionRight p⟩
  · have hz := dispatchReject l W τ hm body α Γ q
    obtain ⟨e⟩ := valueUnique (dispatch l W) (suc z) z ![numeral (typeCode τ),q] h hz
    exact ⟨Derivation.explosion (sucNeZeroApply e)⟩

private theorem atPhysicalResult (t q r : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph rawResult r ![q]))) :
    Nonempty (Derivation body Γ (programGraph resultAtSecond r ![t,q])) := by
  unfold resultAtSecond
  apply compositionValue rawResult (Fin.cons (.projection (1 : Fin 2)) Fin.elim0) r ![t,q] ![q] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (1 : Fin 2) ![t,q]

private theorem requestedEquality (t q r : OTerm α)
    (hs : Nonempty (Derivation body Γ (programGraph requestedTypeTest (suc z) ![t,q])))
    (hr : Nonempty (Derivation body Γ (programGraph rawResult r ![q]))) :
    Nonempty (Derivation body Γ (equal r t)) := by
  let ps : Fin 2 → Program 2 := Fin.cons (Program.projection (0 : Fin 2)) (Fin.cons resultAtSecond Fin.elim0)
  have compare := compositionRecover compareNumbers ps (suc z) ![t,q] ![t,r] hs
    (fun i => Fin.cases (projectionValue (0 : Fin 2) ![t,q])
      (Fin.cases (atPhysicalResult t q r hr) (fun k => Fin.elim0 k)) i)
  rw [exact_DispatchControlAST.2.2.2.1] at compare
  obtain ⟨e⟩ := equalityOfAcceptance t r compare
  rw [equalEqn]
  exact ⟨symm e⟩

end

theorem openResult : ExactOpenRequestedResultField := by
  intro i W τ body α Γ q r h hr
  exact requestedEquality (numeral (typeCode τ)) q r (acceptedRequest i W τ q h) hr

#print axioms openResult

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedResultProof
