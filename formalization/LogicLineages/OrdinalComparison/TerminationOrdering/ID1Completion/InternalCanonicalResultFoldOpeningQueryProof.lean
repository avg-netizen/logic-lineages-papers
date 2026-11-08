module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalCanonicalResultFoldOpening
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelComponentsProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalCanonicalResultFoldOpeningBoundsProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Original output witnesses in the same order as openingMatrix. -/
def qPayload : Program 1 := rightOf (.projection 0)
def qMiddle : Program 1 := InternalApplicationStepPeel.appBody (.projection 0)
def qChildren : Program 1 := rightOf qMiddle
def qArrow : Program 1 := consOf rootDomain rootCodomain
def qFunctionPayload : Program 1 := InternalApplicationStepPeel.functionPayload (.projection 0)
def qArgumentPayload : Program 1 := InternalApplicationStepPeel.argumentPayload (.projection 0)
def queries : Fin 10 → Program 1 :=
  ![qPayload,qMiddle,qChildren,qArrow,rootDomain,rootCodomain,
    qFunctionPayload,qArgumentPayload,functionChild,argumentChild]

/-- Total original Program outputs are reverse-paired inside the calculus.
The accepted tag test supplies TWO; no source inversion or decode is used. -/
theorem atQueries (V member : Program 1) (parent : OrdinaryArithmetic.Term α)
    (ys : Fin 10 → OrdinaryArithmetic.Term α)
    (hopen : Nonempty (Derivation body Gamma (openingAccepted V member parent)))
    (hq : ∀ i, Nonempty (Derivation body Gamma
      (graph1 (queries i) (ys i) parent))) :
    Nonempty (Derivation body Gamma
      (openingWitnesses V member parent
        (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9))) := by
  let xs : Fin 1 → OrdinaryArithmetic.Term α := Fin.cons parent Fin.elim0
  have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) parent xs
    (hq 0) (projectionValue 0 xs)
  have hl := unaryRecover InternalUnpair.left (.projection 0) (ys 5) parent xs
    (hq 5) (projectionValue 0 xs)
  have hm := unaryRecover InternalUnpair.right qPayload (ys 1) (ys 0) xs (hq 1) (hq 0)
  have hc := unaryRecover InternalUnpair.right qMiddle (ys 2) (ys 1) xs (hq 2) (hq 1)
  have hd := unaryRecover InternalUnpair.left qMiddle (ys 4) (ys 1) xs (hq 4) (hq 1)
  have hfp := unaryRecover InternalUnpair.left qChildren (ys 6) (ys 2) xs (hq 6) (hq 2)
  have hap := unaryRecover InternalUnpair.right qChildren (ys 7) (ys 2) xs (hq 7) (hq 2)
  have har := binaryRecover InternalListCodec.consCode rootDomain rootCodomain
    (ys 3) (ys 4) (ys 5) xs (hq 3) (hq 4) (hq 5)
  have hfn := binaryRecover InternalPairing.pairing qArrow qFunctionPayload
    (ys 8) (ys 3) (ys 6) xs (hq 8) (hq 3) (hq 6)
  have harg := binaryRecover InternalPairing.pairing rootDomain qArgumentPayload
    (ys 9) (ys 4) (ys 7) xs (hq 9) (hq 4) (hq 7)
  have ho := conjunctionRecover _ _ xs hopen
  have ht := sameRightRecover (InternalApplicationStepPeel.constructorTag (.projection 0))
    (two 1) positionTerm xs (andLeft ho) (twoValue xs)
  have htag := unaryRecover InternalUnpair.left qPayload positionTerm (ys 0) xs ht (hq 0)
  have hpv := reconstructPair parent (ys 5) (ys 0) hl hr
  have hpn := reconstructPair (ys 0) positionTerm (ys 1) htag hm
  have hpb := reconstructPair (ys 1) (ys 4) (ys 2) hd hc
  have hpch := reconstructPair (ys 2) (ys 6) (ys 7) hfp hap
  have happ := packedAtPairs (ys 4) (ys 5) (ys 6) (ys 7) (ys 2) (ys 1) (ys 0) parent
    hpch hpb hpn hpv
  have hv := conjunctionRecover _ _ xs (andRight ho)
  have hf := conjunctionRecover _ _ xs (andRight hv)
  have ha := conjunctionRecover _ _ xs (andRight hf)
  have hvalid : Nonempty (Derivation body Gamma
      (validityFactors V member parent (ys 8) (ys 9) (ys 5))) :=
    andIntro (andLeft hv)
      (andIntro (unaryRecover V functionChild (suc z) (ys 8) xs (andLeft hf) (hq 8))
        (andIntro (unaryRecover V argumentChild (suc z) (ys 9) xs (andLeft ha) (hq 9))
          (unaryRecover member rootCodomain (suc z) (ys 5) xs (andRight ha) (hq 5))))
  have hfields : Nonempty (Derivation body Gamma
      (originalFields parent (ys 0) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9))) :=
    andIntro hl (andIntro hr
      (andIntro (pairLeft (ys 8) (ys 3) (ys 6) hfn)
        (andIntro (pairRight (ys 8) (ys 3) (ys 6) hfn)
          (andIntro (pairLeft (ys 9) (ys 4) (ys 7) harg)
            (pairRight (ys 9) (ys 4) (ys 7) harg)))))
  have hpay : Nonempty (Derivation body Gamma
      (InternalPairingSumBounds.applicationPayloadWitnesses
        (ys 0) (ys 1) (ys 2) (ys 4) (ys 6) (ys 7))) := by
    apply andIntro ?_ (andIntro hpb hpch)
    simpa only [positionTermEq, InternalPairingSumBounds.pairGraph, graph2] using hpn
  exact andIntro (andIntro har (andIntro hfn (andIntro harg happ)))
    (andIntro hvalid (andIntro hfields
      (andIntro hpay (payloadStrictChildren (ys 0) (ys 1) (ys 2) (ys 4) (ys 6) (ys 7) hpay))))

/-- Shared original witness graphs reconstruct the literal guard acceptance.
No semantic property of V or member is used in this converse. -/
theorem acceptWitnesses (V member : Program 1)
    (parent payload middle children arrow d e fp ap fn arg : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma
      (openingWitnesses V member parent payload middle children arrow d e fp ap fn arg))) :
    Nonempty (Derivation body Gamma (openingAccepted V member parent)) := by
  let xs : Fin 1 → OrdinaryArithmetic.Term α := Fin.cons parent Fin.elim0
  have hcon := andLeft h
  have hv := andLeft (andRight h)
  have hfld := andLeft (andRight (andRight h))
  have hpay := andLeft (andRight (andRight (andRight h)))
  have hpv := reconstructPair parent e payload (andLeft hfld) (andLeft (andRight hfld))
  have hpn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing payload positionTerm middle)) := by
    simpa only [positionTermEq, InternalPairingSumBounds.pairGraph, graph2] using andLeft hpay
  have hpb := andLeft (andRight hpay)
  have hpch := andRight (andRight hpay)
  have hf := fieldsAtPairs (.projection 0) parent parent d e fp ap children middle payload
    (projectionValue 0 xs) hpch hpb hpn hpv
  have he := andLeft hf
  have htag := andLeft (andRight hf)
  have hd := andLeft (andRight (andRight hf))
  have hfp := andLeft (andRight (andRight (andRight hf)))
  have hap := andRight (andRight (andRight (andRight hf)))
  have har := binaryValue InternalListCodec.consCode rootDomain rootCodomain arrow d e xs
    (andLeft hcon) hd he
  have hfn := binaryValue InternalPairing.pairing qArrow qFunctionPayload fn arrow fp xs
    (andLeft (andRight hcon)) har hfp
  have harg := binaryValue InternalPairing.pairing rootDomain qArgumentPayload arg d ap xs
    (andLeft (andRight (andRight hcon))) hd hap
  have hvg : Nonempty (Derivation body Gamma (graph1 (rootGuard V member) (suc z) parent)) :=
    conjunctionAccept _ _ xs (andLeft hv)
      (conjunctionAccept _ _ xs
        (unaryValue V functionChild (suc z) fn xs (andLeft (andRight hv)) hfn)
        (conjunctionAccept _ _ xs
          (unaryValue V argumentChild (suc z) arg xs (andLeft (andRight (andRight hv))) harg)
          (unaryValue member rootCodomain (suc z) e xs (andRight (andRight (andRight hv))) he)))
  exact conjunctionAccept _ _ xs
    (sameAccept (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1)
      positionTerm xs htag (twoValue xs)) hvg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningQueryProof
