module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyKernelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRelationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalEqualityTestCompositionProof (equalityOfEqual)
open OriginalVariableDecoderEqualityProof (equalityReject)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalActiveClassKernelEqualityProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EvaluatorKeyKernelProof
open OriginalActiveClassKernelBranchProof (equalityControl)
theorem matrixOfEqual (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (seed candidate parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
 (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
 Nonempty (Derivation body Delta (Matrix p H G W seed candidate parameter)) :=
 andIntro (OriginalActiveClassKernelBranchProof.domainOfEqual (prepared p H G W) H G W seed candidate parameter hd he)
   (keyOfEqual (evaluatorKey p H G W) seed candidate parameter he)

theorem fromRelation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation body Delta (graph3 (relationTest p H G W P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta (Matrix p H G W seed candidate parameter)) := by
  apply formulaCases (eqn candidate seed)
  · exact matrixOfEqual p H G W seed candidate parameter (withHyp hd (eqn candidate seed))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
    have hz : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
          z seed candidate parameter)) := equalityControl z seed candidate parameter
      (equalityReject candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (classTest p H G W P) (suc z) seed candidate parameter)) := zeroBranchElim
      (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (classTest p H G W P)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) xs hz (withHyp hr (eqn candidate seed).not)
    exact fromClass p H G W P seed candidate parameter
      (withHyp hd (eqn candidate seed).not) ho

theorem toRelation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hm : Nonempty (Derivation body Delta (Matrix p H G W seed candidate parameter))) :
    Nonempty (Derivation body Delta (graph3 (relationTest p H G W P) (suc z) seed candidate parameter)) := by
  apply formulaCases (eqn candidate seed)
  · let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
    have he : Nonempty (Derivation body (eqn candidate seed :: Delta)
        (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
          (suc z) seed candidate parameter)) := equalityControl (suc z) seed candidate parameter
      (equalityOfEqual candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ht : Nonempty (Derivation body (eqn candidate seed :: Delta)
        (programGraph (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
          (suc z) xs)) := binaryValue (OriginalTypedDecoder.target H G) (.projection 0) (.projection 2)
      (suc z) seed parameter xs (andLeft (withHyp hd (eqn candidate seed)))
        (projectionValue 0 xs) (projectionValue 2 xs)
    exact successorBranchIntro
      (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (classTest p H G W P)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) z xs he ht
  · let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
    have hz : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
          z seed candidate parameter)) := equalityControl z seed candidate parameter
      (equalityReject candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (classTest p H G W P) (suc z) seed candidate parameter)) :=
      toClass p H G W P seed candidate parameter
        (withHyp hd (eqn candidate seed).not) (withHyp hm (eqn candidate seed).not)
    exact zeroBranchIntro
      (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (classTest p H G W P)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) xs hz ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRelationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRelationProof
