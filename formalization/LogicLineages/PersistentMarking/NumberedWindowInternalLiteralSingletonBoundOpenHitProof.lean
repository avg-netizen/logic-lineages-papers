module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenHitProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (rejectOfEqual)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (retainSingleton)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof (readBoundComparison)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- At a successor-shaped depth the insertion program takes its positive
branch: the supplied `H` graph on the first two tape slots is the result.
The third slot is arbitrary and is never read. -/
theorem exact_OpenShiftedInsertionPositive (H : Program 2) (a d q out : OTerm α)
    (hit : D B Γ (programGraph H out ![a,suc d])) :
    D B Γ (programGraph (shiftedInsertion H) out ![a,suc d,q]) := by
  let xs : Fin 3 → OTerm α := ![a,suc d,q]
  have depth : D B Γ (programGraph (.projection (1 : Fin 3)) (suc d) xs) :=
    projectionValue (1 : Fin 3) xs
  have composed : D B Γ
      (programGraph (.composition H ![.projection 0,.projection 1]) out xs) := by
    apply compositionValue H (![.projection 0,.projection 1] : Fin 2 → Program 3)
      out xs ![a,suc d] hit
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact projectionValue (0 : Fin 3) xs
    · obtain rfl := Fin.eq_zero j
      exact projectionValue (1 : Fin 3) xs
  exact successorBranchIntro (.projection 1) directInsertion
    (.composition H ![.projection 0,.projection 1]) out d xs depth composed

/-- A bound index equal to a successor-shaped substitution depth returns
exactly the output of the supplied shift program on replacement and depth.
Both syntax premises are retained; the only hypothesis on `H` is an actual
open graph derivation in the same arithmetic context. -/
theorem exact_OpenSingletonBoundAtPositiveDepth (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t out : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc d))))
    (hit : D B Γ (programGraph H out ![a,suc d])) :
    D B Γ (programGraph (singletonBound V H U) out ![a,suc d,boundTerm t (suc d)]) := by
  let xs : Fin 3 → OTerm α := ![a,suc d,boundTerm t (suc d)]
  have before : D B Γ (programGraph boundBeforeDepth z xs) :=
    readBoundComparison ltTest a (suc d) t (suc d) z
      (rejectOfEqual (suc d) (suc d) ⟨refl (suc d)⟩)
  have atDepth : D B Γ (programGraph boundAtDepth (suc z) xs) :=
    readBoundComparison equalityTest a (suc d) t (suc d) (suc z)
      (equalityOfEqual (suc d) (suc d) ⟨refl (suc d)⟩)
  have shifted : D B Γ (programGraph (shiftedInsertion H) out xs) :=
    exact_OpenShiftedInsertionPositive H a d (boundTerm t (suc d)) out hit
  have equalCase : D B Γ
      (programGraph (branch boundAtDepth boundLowered (shiftedInsertion H)) out xs) :=
    successorBranchIntro boundAtDepth boundLowered (shiftedInsertion H) out z xs atDepth shifted
  exact exact_OpenBoundProgram V H U a (suc d) t (suc d) out inserted typedNode
    (zeroBranchIntro boundBeforeDepth (branch boundAtDepth boundLowered (shiftedInsertion H))
      retainSingleton out xs before equalCase)

#print axioms exact_OpenShiftedInsertionPositive
#print axioms exact_OpenSingletonBoundAtPositiveDepth
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenHitProof
