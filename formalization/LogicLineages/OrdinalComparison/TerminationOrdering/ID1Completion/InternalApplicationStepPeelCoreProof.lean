module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The successful concrete transition at original pair witnesses. All facts
below are derivations of original graphs, not evaluations or decoded objects. -/
theorem transitionAtPairs (endpoint : Program 5)
    (d e arrow s t a certificate k lifted fp tp ap path payload sc sb sn tc tb tn prefixed s' t' k' : OTerm α)
    (htag : Nonempty (Derivation body Gamma (taggedEdge d e arrow s t a certificate k)))
    (hend : Nonempty (Derivation body Gamma (graph5 endpoint (suc z) d e s t a)))
    (hlift : Nonempty (Derivation body Gamma (graph4 edgeLift lifted d e a certificate)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp s)))
    (htp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right tp t)))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hpath : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left path k)))
    (hpay : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload k)))
    (hsc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing sc fp ap)))
    (hsb : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing sb d sc)))
    (hsn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing sn positionTerm sb)))
    (htc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tc tp ap)))
    (htb : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tb d tc)))
    (htn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tn positionTerm tb)))
    (hpre : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode prefixed positionTerm path)))
    (hs' : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing s' e sn)))
    (ht' : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing t' e tn)))
    (hk' : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing k' prefixed payload))) :
    Nonempty (Derivation body Gamma (graph1 (transition endpoint) certificate lifted)) := by
  have har := andLeft htag
  have hst := andLeft (andRight htag)
  have htt := andLeft (andRight (andRight htag))
  have hat := andLeft (andRight (andRight (andRight htag)))
  have hedge := andRight (andRight (andRight (andRight htag)))
  have hk := reconstructPair k path payload hpath hpay
  have hsapp := applicationBackward d e s a fp ap s' hfp hap
    (packedAtPairs d e fp ap sc sb sn s' hsc hsb hsn hs')
  have htapp := applicationBackward d e t a tp ap t' htp hap
    (packedAtPairs d e tp ap tc tb tn t' htc htb htn ht')
  have hstep := stepBackward k path payload prefixed k' hk hpre hk'
  have lp := andIntro hedge (andIntro hsapp (andIntro htapp hstep))
  have hed := liftedEdgeSelectors d e a certificate s t k s' t' k' lifted lp hlift
  have hvS := andLeft hed
  have hvT := andLeft (andRight hed)
  have hvK := andRight (andRight hed)
  have sf := fieldsAtPairs source lifted s' d e fp ap sc sb sn hvS hsc hsb hsn hs'
  have tf := fieldsAtPairs target lifted t' d e tp ap tc tb tn hvT htc htb htn ht'
  have hcod := andLeft sf
  have htcod := andLeft tf
  have hstag := andLeft (andRight sf)
  have httag := andLeft (andRight tf)
  have hdom := andLeft (andRight (andRight sf))
  have htdom := andLeft (andRight (andRight tf))
  have hfun := andLeft (andRight (andRight (andRight sf)))
  have htfun := andLeft (andRight (andRight (andRight tf)))
  have harg := andRight (andRight (andRight (andRight sf)))
  have htarg := andRight (andRight (andRight (andRight tf)))
  let xs : Fin 1 → OTerm α := Fin.cons lifted Fin.elim0
  have hraw := unaryValue InternalUnpair.left step prefixed k' xs (pairLeft k' prefixed payload hk') hvK
  have hpd := InternalListCodecSupportProof.consDestruction prefixed positionTerm path hpre
  have hhead := unaryValue InternalListCodec.headCode rawPath positionTerm prefixed xs (andLeft hpd) hraw
  have htail := unaryValue InternalListCodec.tailCode rawPath path prefixed xs
    (andLeft (andRight hpd)) hraw
  have hpay' := unaryValue InternalUnpair.right step payload k' xs (pairRight k' prefixed payload hk') hvK
  have harrow := binaryValue InternalListCodec.consCode domain codomain arrow d e xs har hdom hcod
  have hsf := binaryValue InternalPairing.pairing arrowType (functionPayload source) s arrow fp xs
    (reconstructPair s arrow fp hst hfp) harrow hfun
  have htf := binaryValue InternalPairing.pairing arrowType (functionPayload target) t arrow tp xs
    (reconstructPair t arrow tp htt htp) harrow htfun
  have hva := binaryValue InternalPairing.pairing domain (argumentPayload source) a d ap xs
    (reconstructPair a d ap hat hap) hdom harg
  have hvk := binaryValue InternalPairing.pairing pathTail (rightOf step) k path payload xs hk htail hpay'
  have hpeeled : Nonempty (Derivation body Gamma (graph1 peeledState certificate lifted)) := by
    apply compositionValue edgeCode ![functionCode,targetFunctionCode,peeledStep] certificate xs
      (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hedge
    intro i
    exact Fin.cases hsf (Fin.cases htf (Fin.cases hvk (fun j => Fin.elim0 j))) i
  have hstructure : Nonempty (Derivation body Gamma (graph1 structuralGuard (suc z) lifted)) := by
    apply conjunctionAccept _ _ xs (nonemptyAccept lifted prefixed path hraw hpre)
    apply conjunctionAccept _ _ xs (sameAccept _ _ positionTerm xs hhead (twoValue xs))
    apply conjunctionAccept _ _ xs (sameAccept _ _ positionTerm xs hstag (twoValue xs))
    apply conjunctionAccept _ _ xs (sameAccept _ _ positionTerm xs httag (twoValue xs))
    apply conjunctionAccept _ _ xs (sameAccept _ _ e xs hcod htcod)
    apply conjunctionAccept _ _ xs (sameAccept _ _ d xs hdom htdom)
    exact sameAccept _ _ ap xs harg htarg
  have hepg : Nonempty (Derivation body Gamma (graph5 (endpointGuard endpoint) (suc z) d e s t a)) :=
    conjunctionAccept endpointTypeGuard endpoint
      (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0)))))
      (endpointTypesAccept d e arrow s t a har hst htt hat) hend
  have hatEnd : Nonempty (Derivation body Gamma (graph1 (endpointAt endpoint) (suc z) lifted)) := by
    apply compositionValue (endpointGuard endpoint) ![domain,codomain,functionCode,targetFunctionCode,argumentCode]
      (suc z) xs (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0))))) hepg
    intro i
    exact Fin.cases hdom (Fin.cases hcod (Fin.cases hsf (Fin.cases htf
      (Fin.cases hva (fun j => Fin.elim0 j))))) i
  have hguard : Nonempty (Derivation body Gamma (graph1 (guard endpoint) (suc z) lifted)) :=
    conjunctionAccept structuralGuard (endpointAt endpoint) xs hstructure hatEnd
  exact successorBranchIntro (guard endpoint) (.projection 0) peeledState certificate z xs hguard hpeeled

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelCoreProof
