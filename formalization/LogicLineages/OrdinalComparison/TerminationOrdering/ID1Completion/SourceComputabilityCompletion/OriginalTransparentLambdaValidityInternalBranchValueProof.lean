module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBranchSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem dispatchTwoValue (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 2 raw)))
    (he : Nonempty (Derivation body Gamma (equal out (numeral 1)))) :
    Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter)) := by
  obtain ⟨he⟩ := he
  have hc := outputTransport (InternalLessThan.constantOne 2) (numeral 1) out ![raw,parameter]
    ⟨symm (by simpa only [equalEqn] using he)⟩
    (InternalLessThanSupportProof.oneConstantValue ![raw,parameter])
  exact successorBranchIntro twoTest (InternalAcceptance.branch oneTest old lambda)
    (InternalLessThan.constantOne 2) out z ![raw,parameter] (twoControl raw parameter ht) hc

theorem dispatchOneValue (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (h : Nonempty (Derivation body Gamma (graph2 lambda out raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter)) :=
  zeroBranchIntro twoTest (InternalAcceptance.branch oneTest old lambda) (InternalLessThan.constantOne 2)
    out ![raw,parameter] (notTwoControl raw parameter (oneNotTwo raw ht))
    (successorBranchIntro oneTest old lambda out z ![raw,parameter] (oneControl raw parameter ht) h)

theorem dispatchOpaqueValue (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not))
    (h : Nonempty (Derivation body Gamma (graph2 old out raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter)) :=
  zeroBranchIntro twoTest (InternalAcceptance.branch oneTest old lambda) (InternalLessThan.constantOne 2)
    out ![raw,parameter] (notTwoControl raw parameter h2)
    (zeroBranchIntro oneTest old lambda out ![raw,parameter] (notOneControl raw parameter h1) h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
