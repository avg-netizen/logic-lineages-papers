module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (oneRename)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Original selector totality supplies the whole connected lambda coordinate
system. No arrow shape, membership, decoder run or child acceptance is assumed. -/
theorem lambdaCoordinatesCases (packed parameter : OTerm alpha) (psi : Formula alpha)
    (htag : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaConstructor.tag (numeral 1) packed)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (typ payload middle domain bodyPayload requestedDomain codomain c gamma extended child childParam : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepPair (packed.relabel j) typ payload)) →
      Nonempty (Derivation body Theta (StepPair payload (numeral 1) middle)) →
      Nonempty (Derivation body Theta (StepPair middle domain bodyPayload)) →
      Nonempty (Derivation body Theta (StepArrowFields typ requestedDomain codomain)) →
      Nonempty (Derivation body Theta (StepPair (parameter.relabel j) c gamma)) →
      Nonempty (Derivation body Theta (StepCons extended domain gamma)) →
      Nonempty (Derivation body Theta (StepPair child codomain bodyPayload)) →
      Nonempty (Derivation body Theta (StepPair childParam c extended)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let p0 : Program 2 := .projection 0
  let p1 : Program 2 := .projection 1
  let typ := leftOf p0
  let payload := rightOf p0
  let middle := rightOf payload
  let domain := leftOf middle
  let bodyPayload := rightOf middle
  let requestedDomain := headOf typ
  let codomain := tailOf typ
  let context := leftOf p1
  let gamma := rightOf p1
  let extended := consOf domain gamma
  let child := pairOf codomain bodyPayload
  let childParam := pairOf context extended
  let qs : Fin 12 → Program 2 :=
    ![typ,payload,middle,domain,bodyPayload,requestedDomain,codomain,context,gamma,extended,child,childParam]
  apply programsCases qs (Fin.cons packed (Fin.cons parameter Fin.elim0)) psi
  intro beta j Theta ys hj hq
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 2 → OTerm beta := Fin.cons (packed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hp := pairFields p0 (packed.relabel j) (ys 0) (ys 1) xs
    (projectionValue 0 xs) (hq 0) (hq 1)
  have hmid := unaryRecover InternalUnpair.right payload (ys 2) (ys 1) xs (hq 2) (hq 1)
  have htag' := renameInto htag j Theta hj
  simp only [graph1Rename,oneRename] at htag'
  let ux : Fin 1 → OTerm beta := Fin.cons (packed.relabel j) Fin.elim0
  have hpay := pairRightValue (.projection 0) (packed.relabel j) (ys 0) (ys 1) ux
    (projectionValue 0 ux) hp
  have htagPayload := unaryRecover InternalUnpair.left (rightOf (.projection 0))
    (numeral 1) (ys 1) ux htag' hpay
  have ht := reconstructPair (ys 1) (numeral 1) (ys 2) htagPayload hmid
  have hm := pairFields middle (ys 2) (ys 3) (ys 4) xs (hq 2) (hq 3) (hq 4)
  have hf := arrowFields typ (ys 0) (ys 5) (ys 6) xs (hq 0) (hq 5) (hq 6)
  have hparam := pairFields p1 (parameter.relabel j) (ys 7) (ys 8) xs
    (projectionValue 1 xs) (hq 7) (hq 8)
  have hext := binaryRecover InternalListCodec.consCode domain gamma (ys 9) (ys 3) (ys 8) xs
    (hq 9) (hq 3) (hq 8)
  have hchild := binaryRecover InternalPairing.pairing codomain bodyPayload (ys 10) (ys 6) (ys 4) xs
    (hq 10) (hq 6) (hq 4)
  have hchildParam := binaryRecover InternalPairing.pairing context extended (ys 11) (ys 7) (ys 9) xs
    (hq 11) (hq 7) (hq 9)
  exact step beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)
    (ys 7) (ys 8) (ys 9) (ys 10) (ys 11) hj hp ht hm hf hparam hext hchild hchildParam
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
