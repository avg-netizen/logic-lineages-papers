module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaMachineProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBottomCollapseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawShapeProof (bottomTerm)
open NumberedWindowInternalLiteralSingletonAtomsOpenProof (exact_OpenSingletonRetainBottom)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof (shiftHitLiterals)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof (exact_OpenSingletonBoundShiftedBottomLiteral)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A bound-variable-to-bottom step at the discharged index can collapse
when the replacement is that bottom. At positive depth the literal
singleton gives equal outputs on the two endpoints by its actual graphs. -/
theorem exact_OpenSingletonBottomCollapse (V : Program 1) (H : Program 2) (U : Program 3)
    (ty d left right : OTerm α) :
    let a := bottomTerm ty
    let q := boundTerm ty (suc d)
    let S := shiftHitLiterals V H
    let P := singletonLambda V S (singletonBound V S U)
    D B Γ (unary V (suc z) a) → D B Γ (unary V (suc z) q) →
    D B Γ (programGraph P (suc left) ![a,suc d,q]) →
    D B Γ (programGraph P (suc right) ![a,suc d,a]) →
    D B Γ (eqn left right) := by
  intro a q S P bottomValid boundValid first second
  have boundRun : D B Γ (programGraph P (suc a) ![a,suc d,q]) :=
    exact_OpenSingletonBoundShiftedBottomLiteral V H (singletonLambdaDispatch (singletonBound V S U))
      ty d ty bottomValid boundValid
  have bottomRun : D B Γ (programGraph P (suc a) ![a,suc d,a]) := by
    unfold P singletonLambda singletonBound
    exact exact_OpenSingletonRetainBottom V _ a (suc d) ty bottomValid bottomValid
  obtain ⟨fromBound⟩ := valueUnique P (suc left) (suc a) ![a,suc d,q] first boundRun
  obtain ⟨fromBottom⟩ := valueUnique P (suc a) (suc right) ![a,suc d,a] bottomRun second
  exact ⟨cancelSuc (trans fromBound fromBottom)⟩

#print axioms exact_OpenSingletonBottomCollapse
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBottomCollapseProof
