module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyKernelProof
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
abbrev Matrix (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (seed candidate parameter : OTerm alpha) : Formula alpha :=
 Domain p H G W candidate parameter ⊓ keyGraph (evaluatorKey p H G W) seed candidate parameter

theorem fromClass (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (seed candidate parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
 (hr : Nonempty (Derivation body Delta (graph3 (classTest p H G W P) (suc z) seed candidate parameter))) :
 Nonempty (Derivation body Delta (Matrix p H G W seed candidate parameter)) := by
 let q := prepared p H G W
 let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
 let A : Program 3 := .composition (OriginalActiveObservedClass.activation q H G W) ![.projection 0,.projection 2]
 have ha := binaryValue (OriginalActiveObservedClass.activation q H G W) (.projection 0) (.projection 2)
   (suc z) seed parameter xs (andRight hd) (projectionValue 0 xs) (projectionValue 2 xs)
 have hk := successorBranchElim A P (kernel p H G W) (suc z) z xs ha hr
 have hm := conjunctionRecover
   (.composition (OriginalActiveClassKernel.domainProgram q H G W) ![.projection 1,.projection 2])
   (OriginalActiveClassKernel.keyTest (evaluatorKey p H G W)) xs hk
 have hc := binaryRecover (OriginalActiveClassKernel.domainProgram q H G W) (.projection 1) (.projection 2)
   (suc z) candidate parameter xs (andLeft hm) (projectionValue 1 xs) (projectionValue 2 xs)
 exact andIntro (OriginalActiveClassKernelBranchProof.domainRecover q H G W candidate parameter hc) (andRight hm)

theorem toClass (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (seed candidate parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
 (hm : Nonempty (Derivation body Delta (Matrix p H G W seed candidate parameter))) :
 Nonempty (Derivation body Delta (graph3 (classTest p H G W P) (suc z) seed candidate parameter)) := by
 let q := prepared p H G W
 let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
 let A : Program 3 := .composition (OriginalActiveObservedClass.activation q H G W) ![.projection 0,.projection 2]
 have ha := binaryValue (OriginalActiveObservedClass.activation q H G W) (.projection 0) (.projection 2)
   (suc z) seed parameter xs (andRight hd) (projectionValue 0 xs) (projectionValue 2 xs)
 have hdom := OriginalActiveClassKernelBranchProof.domainValue q H G W candidate parameter (andLeft hm)
 have hc := binaryValue (OriginalActiveClassKernel.domainProgram q H G W) (.projection 1) (.projection 2)
   (suc z) candidate parameter xs hdom (projectionValue 1 xs) (projectionValue 2 xs)
 have hk := conjunctionAccept
   (.composition (OriginalActiveClassKernel.domainProgram q H G W) ![.projection 1,.projection 2])
   (OriginalActiveClassKernel.keyTest (evaluatorKey p H G W)) xs hc (andRight hm)
 exact successorBranchIntro A P (kernel p H G W) (suc z) z xs ha hk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyKernelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyKernelProof
