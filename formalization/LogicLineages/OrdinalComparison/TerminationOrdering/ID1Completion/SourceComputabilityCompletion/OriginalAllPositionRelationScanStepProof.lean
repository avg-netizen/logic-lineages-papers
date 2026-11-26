module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalLessThanSupportProof (oneConstantValue)
open InternalRawListRecursionSupportProof (recursionNext)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalAllPositionRelationScanSyntaxProof

theorem zeroAccepted (R : Program 2) (seed candidate parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (graph4 (scan R) (suc z) z seed candidate parameter)) :=
 recursionZeroValue (InternalLessThan.constantOne 3) (scanStep R) (suc z)
   (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))) (oneConstantValue _)

theorem successorAccepted (R : Program 2) (count seed candidate parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed candidate parameter)))
 (ht : Nonempty (Derivation body Delta (graph4 (positionTest R) (suc z) count seed candidate parameter))) :
 Nonempty (Derivation body Delta (graph4 (scan R) (suc z) (suc count) seed candidate parameter)) := by
 let params : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
 let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons (suc z) params)
 let g : Fin 4 → Program 5 := ![.projection 0,.projection 2,.projection 3,.projection 4]
 have htest := compositionValue (positionTest R) g (suc z) xs (Fin.cons count params) ht
   (fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 2 xs)
     (Fin.cases (projectionValue 3 xs) (Fin.cases (projectionValue 4 xs) (fun k => Fin.elim0 k)))) i)
 have step := conjunctionAccept (.projection (1 : Fin 5)) (.composition (positionTest R) g) xs (projectionValue 1 xs) htest
 exact recursionNext (InternalLessThan.constantOne 3) (scanStep R) (suc z) (suc z) count params hp step

theorem succCore (R : Program 2) (count seed other candidate parameter : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row R count)))
 (hso : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) (suc count) seed other parameter))) :
 Nonempty (Derivation body Delta ((graph4 (scan R) (suc z) (suc count) seed candidate parameter).iff
   (graph4 (scan R) (suc z) (suc count) other candidate parameter))) := by
 have split := OriginalClassContextAllPositionScanSupportProof.successorExposure R count seed other parameter hso
 have prior := rowApply R count seed other candidate parameter hrow (andLeft split)
 have point := OriginalAllPositionRelationPointProof.rowAt R count seed other candidate parameter (andRight split)
 let A := graph4 (scan R) (suc z) (suc count) seed candidate parameter
 let B := graph4 (scan R) (suc z) (suc count) other candidate parameter
 have forward : Nonempty (Derivation body (A :: Delta) B) := by
   have h := OriginalClassContextAllPositionScanSupportProof.successorExposure R count seed candidate parameter
     (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact successorAccepted R count other candidate parameter
     (iffForward (withHyp prior A) (andLeft h)) (iffForward (withHyp point A) (andRight h))
 have backward : Nonempty (Derivation body (B :: Delta) A) := by
   have h := OriginalClassContextAllPositionScanSupportProof.successorExposure R count other candidate parameter
     (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact successorAccepted R count seed candidate parameter
     (iffBackward (withHyp prior B) (andLeft h)) (iffBackward (withHyp point B) (andRight h))
 obtain ⟨hf⟩ := forward
 obtain ⟨hb⟩ := backward
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
