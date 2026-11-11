module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBooleanProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open OriginalHereditaryValidityInternalNodeSupportProof (weakenProof)
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalControlGraphChoiceProof (excludedMiddle)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem conjunctionReject {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Gamma
      (programGraph (InternalAcceptance.conjunction p q) (numeral 1) xs).not)) :
    Nonempty (Derivation body Gamma (programGraph (InternalAcceptance.conjunction p q) z xs)) := by
  obtain ⟨hn⟩ := hn
  let P := programGraph p (numeral 1) xs
  let Q := programGraph q (numeral 1) xs
  have hy : Nonempty (Derivation body (P :: Gamma)
      (programGraph (InternalAcceptance.conjunction p q) z xs)) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hnq : Nonempty (Derivation body (P :: Gamma) Q.not) := by
      obtain ⟨hc⟩ := conjunctionAccept p q xs
        (weakenProof hp (fun r hr => List.mem_cons_of_mem Q hr))
        (show Nonempty (Derivation body (Q :: P :: Gamma) Q) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
      exact ⟨Derivation.implicationIntroduction
        (Derivation.implicationElimination (addHyp (addHyp hn P) Q) hc)⟩
    exact successorBranchIntro (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize p) (InternalAcceptance.constantZero n)
      (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize q) z z xs (normalizeAccept p xs hp) (normalizeReject q xs hnq)
  have hno : Nonempty (Derivation body (P.not :: Gamma)
      (programGraph (InternalAcceptance.conjunction p q) z xs)) :=
    zeroBranchIntro (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize p) (InternalAcceptance.constantZero n)
      (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize q) z xs
      (normalizeReject p xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (constantZeroValue xs)
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

def oneTest : Program 2 :=
  InternalApplicationStepPeel.same tag (InternalLessThan.constantOne 2)

def twoTest : Program 2 := InternalApplicationStepPeel.same tag (two 2)

/-- This is exactly the two nested original callback branches. -/
def rootDispatch (old lambda : Program 2) : Program 2 :=
  InternalAcceptance.branch twoTest (InternalAcceptance.branch oneTest old lambda)
    (InternalLessThan.constantOne 2)

theorem controlValue (constant : Program 2) (k : Nat) (raw parameter : OTerm alpha)
    (hk : Nonempty (Derivation body Gamma (graph2 constant (numeral k) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (TagIs k raw))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationStepPeel.same tag constant) (numeral 1) raw parameter)) :=
  sameAccept tag constant (numeral k) ![raw,parameter]
    (unaryValue OriginalLambdaConstructor.tag (.projection 0) (numeral k) raw ![raw,parameter]
      ht (projectionValue 0 ![raw,parameter])) hk

theorem controlReject (constant : Program 2) (k : Nat) (raw parameter : OTerm alpha)
    (hk : Nonempty (Derivation body Gamma (graph2 constant (numeral k) raw parameter)))
    (hn : Nonempty (Derivation body Gamma (TagIs k raw).not)) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationStepPeel.same tag constant) z raw parameter)) := by
  obtain ⟨hn⟩ := hn
  let A := graph2 (InternalApplicationStepPeel.same tag constant) (numeral 1) raw parameter
  have htag := sameRightRecover tag constant (numeral k) ![raw,parameter]
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (weakenProof hk (fun p hp => List.mem_cons_of_mem A hp))
  obtain ⟨ht⟩ := unaryRecover OriginalLambdaConstructor.tag (.projection 0) (numeral k) raw
    ![raw,parameter] htag (projectionValue 0 ![raw,parameter])
  exact sameReject tag constant ![raw,parameter]
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn A) ht)⟩

theorem oneControl (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma (graph2 oneTest (numeral 1) raw parameter)) :=
  controlValue (InternalLessThan.constantOne 2) 1 raw parameter
    (InternalLessThanSupportProof.oneConstantValue ![raw,parameter]) ht

theorem notOneControl (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma (graph2 oneTest z raw parameter)) :=
  controlReject (InternalLessThan.constantOne 2) 1 raw parameter
    (InternalLessThanSupportProof.oneConstantValue ![raw,parameter]) ht

theorem twoControl (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 2 raw))) :
    Nonempty (Derivation body Gamma (graph2 twoTest (numeral 1) raw parameter)) :=
  controlValue (two 2) 2 raw parameter (twoValue ![raw,parameter]) ht

theorem notTwoControl (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 2 raw).not)) :
    Nonempty (Derivation body Gamma (graph2 twoTest z raw parameter)) :=
  controlReject (two 2) 2 raw parameter (twoValue ![raw,parameter]) ht

theorem oneNotTwo (raw : OTerm alpha)
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma (TagIs 2 raw).not) := by
  let T := TagIs 2 raw
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 1) (numeral 2)
    (Fin.cons raw Fin.elim0) (weakenProof h1 (fun p hp => List.mem_cons_of_mem T hp))
    (show Nonempty (Derivation body (T :: Gamma) T) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (zeroNeSuc (cancelSuc he))⟩

theorem dispatchTwo (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 2 raw)))
    (h : Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter))) :
    Nonempty (Derivation body Gamma (equal out (numeral 1))) := by
  have hc := successorBranchElim twoTest (InternalAcceptance.branch oneTest old lambda)
    (InternalLessThan.constantOne 2) out z ![raw,parameter] (twoControl raw parameter ht) h
  simpa only [equalEqn] using valueUnique (InternalLessThan.constantOne 2) out (numeral 1)
    ![raw,parameter] hc (InternalLessThanSupportProof.oneConstantValue ![raw,parameter])

theorem dispatchOne (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (h : Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 lambda out raw parameter)) :=
  successorBranchElim oneTest old lambda out z ![raw,parameter] (oneControl raw parameter ht)
    (zeroBranchElim twoTest (InternalAcceptance.branch oneTest old lambda) (InternalLessThan.constantOne 2)
      out ![raw,parameter] (notTwoControl raw parameter (oneNotTwo raw ht)) h)

theorem dispatchOpaque (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not))
    (h : Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 old out raw parameter)) :=
  zeroBranchElim oneTest old lambda out ![raw,parameter] (notOneControl raw parameter h1)
    (zeroBranchElim twoTest (InternalAcceptance.branch oneTest old lambda) (InternalLessThan.constantOne 2)
      out ![raw,parameter] (notTwoControl raw parameter h2) h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
