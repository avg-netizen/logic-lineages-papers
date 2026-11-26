module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalReflexiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum
open InternalApplicationCertificateConstructors (graph2)
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalEqualityTestCompositionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal internal equality and branch introduction, independent of every
native class calibration and of the finite signature. -/
theorem actualOriginalTransparentMinimumInternalReflexive :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumInternalReflexive := by
  intro T P body α Delta seed parameter
  let A := graph2 T InternalOriginalStepGuard.one seed parameter
  let xs : Fin 3 → OTerm α := Fin.cons seed (Fin.cons seed (Fin.cons parameter Fin.elim0))
  have ht : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he : Nonempty (Derivation body (A :: Delta)
      (programGraph (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
        (suc z) xs)) := by
    apply compositionValue InternalEqualityTest.equalityTest ![.projection 1,.projection 0]
      (suc z) xs (Fin.cons seed (Fin.cons seed Fin.elim0))
      (equalityOfEqual seed seed ⟨refl seed⟩)
    intro i
    exact Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j)) i
  have hb : Nonempty (Derivation body (A :: Delta)
      (programGraph (.composition T ![.projection 0,.projection 2])
        InternalOriginalStepGuard.one xs)) := by
    apply compositionValue T ![.projection 0,.projection 2] InternalOriginalStepGuard.one xs
      (Fin.cons seed (Fin.cons parameter Fin.elim0)) ht
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (fun j => Fin.elim0 j)) i
  obtain ⟨h⟩ := successorBranchIntro
    (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0]) P
    (.composition T ![.projection 0,.projection 2]) InternalOriginalStepGuard.one z xs he hb
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalReflexiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalReflexiveProof
