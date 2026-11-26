module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess rejectOfEqual)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (retainSingleton)
open NumberedWindowInternalLiteralSingletonAtomsOpenProof (exact_OpenSingletonRetain)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem readBoundComparison (C : Program 2) (a d t i out : OTerm α)
    (compared : D B Γ (programGraph C out ![i,d])) :
    D B Γ (programGraph (.composition C ![boundIndex,.projection 1])
      out ![a,d,boundTerm t i]) := by
  apply compositionValue C ![boundIndex,.projection 1] out ![a,d,boundTerm t i] ![i,d] compared
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact onTape (field 1) 2 i _ (exact_OpenBoundRead t i).2.2
  · obtain rfl := Fin.eq_zero j
    exact projectionValue 1 ![a,d,boundTerm t i]

/-- Bound indices below the substitution depth keep their original code.
The order hypothesis is a derivation in the same open arithmetic context. -/
theorem exact_OpenSingletonBoundBeforeDepth (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (before : D B Γ (ltF i d)) :
    D B Γ (programGraph (singletonBound V H U) (suc (boundTerm t i))
      ![a,d,boundTerm t i]) := by
  have selected : D B Γ (programGraph boundBeforeDepth (suc z) ![a,d,boundTerm t i]) :=
    readBoundComparison ltTest a d t i (suc z) (acceptOfLess i d before)
  apply exact_OpenBoundProgram V H U a d t i (suc (boundTerm t i)) inserted typedNode
  exact successorBranchIntro boundBeforeDepth (branch boundAtDepth boundLowered (shiftedInsertion H))
    retainSingleton (suc (boundTerm t i)) z ![a,d,boundTerm t i] selected
    (exact_OpenSingletonRetain a d (boundTerm t i))

/-- At index and depth zero, the substitution program takes its direct
insertion branch and returns the original replacement code plus one. -/
theorem exact_OpenSingletonBoundAtZero (V : Program 1) (H : Program 2) (U : Program 3)
    (a t : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t z))) :
    D B Γ (programGraph (singletonBound V H U) (suc a) ![a,z,boundTerm t z]) := by
  let xs : Fin 3 → OTerm α := ![a,z,boundTerm t z]
  have before : D B Γ (programGraph boundBeforeDepth z xs) :=
    readBoundComparison ltTest a z t z z (rejectOfEqual z z ⟨refl z⟩)
  have atDepth : D B Γ (programGraph boundAtDepth (suc z) xs) :=
    readBoundComparison equalityTest a z t z (suc z) (equalityOfEqual z z ⟨refl z⟩)
  have direct : D B Γ (programGraph directInsertion (suc a) xs) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 0) (suc a) xs ![a]
      (successorValue ![a])
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 0 xs
  have shifted : D B Γ (programGraph (shiftedInsertion H) (suc a) xs) :=
    zeroBranchIntro (.projection 1) directInsertion (.composition H ![.projection 0,.projection 1])
      (suc a) xs (projectionValue 1 xs) direct
  have equalCase : D B Γ
      (programGraph (branch boundAtDepth boundLowered (shiftedInsertion H)) (suc a) xs) :=
    successorBranchIntro boundAtDepth boundLowered (shiftedInsertion H) (suc a) z xs atDepth shifted
  exact exact_OpenBoundProgram V H U a z t z (suc a) inserted typedNode
    (zeroBranchIntro boundBeforeDepth (branch boundAtDepth boundLowered (shiftedInsertion H))
      retainSingleton (suc a) xs before equalCase)

#print axioms exact_OpenSingletonBoundBeforeDepth
#print axioms exact_OpenSingletonBoundAtZero
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof
