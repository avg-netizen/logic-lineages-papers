module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelChildBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalSourceInversionSupportProof
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight oneRename)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalListProof
open OriginalTransparentLambdaValidityInternal OriginalTransparentLambdaValidityInternalShapeSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawTagValue (packed typ payload middle : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) packed)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons packed Fin.elim0
  exact pairLeftValue (rightOf (.projection 0)) payload (numeral 1) middle xs
    (pairRightValue (.projection 0) packed typ payload xs (projectionValue 0 xs) hp) ht

theorem rawDomainValue (packed typ payload middle domain bodyPayload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.domain domain packed)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons packed Fin.elim0
  have hpay := pairRightValue (.projection 0) packed typ payload xs (projectionValue 0 xs) hp
  have hmid := pairRightValue (rightOf (.projection 0)) payload (numeral 1) middle xs hpay ht
  exact pairLeftValue (rightOf (rightOf (.projection 0))) middle domain bodyPayload xs hmid hm

theorem rawBodyPayloadValue (packed typ payload middle domain bodyPayload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.bodyPayload bodyPayload packed)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons packed Fin.elim0
  have hpay := pairRightValue (.projection 0) packed typ payload xs (projectionValue 0 xs) hp
  have hmid := pairRightValue (rightOf (.projection 0)) payload (numeral 1) middle xs hpay ht
  exact pairRightValue (rightOf (rightOf (.projection 0))) middle domain bodyPayload xs hmid hm

theorem childPayloadValue (child codomain bodyPayload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (StepPair child codomain bodyPayload))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right bodyPayload child)) :=
  pairRight child codomain bodyPayload hc

theorem bodyPayloadStrict (payload middle domain bodyPayload : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess bodyPayload payload)) :=
  OriginalLambdaTraversalInternalPayloadArithmeticProof.lambdaDescent payload bodyPayload
    (OriginalTypedDecoderInternalFuelChildBoundsProof.lambdaBound payload middle domain bodyPayload ht hm)

theorem shapeArrowIntro (packed typ domain codomain : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ packed)))
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.domain domain packed)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode codomain typ)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow typ domain codomain))) :
    Nonempty (Derivation body Delta (LambdaShape packed)) :=
  shapeIntro packed typ domain codomain (andIntro ht (andIntro hd (andIntro hc ha)))

/-- Functionality identifies every existential shape witness with the supplied
actual original selectors, including malformed and zero outer type codes. -/
theorem shapeArrowRecover (packed typ domain codomain : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ packed)))
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.domain domain packed)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode codomain typ)))
    (hs : Nonempty (Derivation body Delta (LambdaShape packed))) :
    Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow typ domain codomain)) := by
  apply shapeCases packed _ hs
  intro beta j Theta actualType actualDomain actualCodomain hj hf
  rw [graph2Rename]
  have ht' := renameInto ht j Theta hj
  have hd' := renameInto hd j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [graph1Rename] at ht' hd' hc'
  have et := valueUnique InternalUnpair.left actualType (typ.relabel j)
    (Fin.cons (packed.relabel j) Fin.elim0) (andLeft hf) ht'
  have ed := valueUnique OriginalLambdaConstructor.domain actualDomain (domain.relabel j)
    (Fin.cons (packed.relabel j) Fin.elim0) (andLeft (andRight hf)) hd'
  have actualTail := headTransport InternalListCodec.tailCode actualCodomain actualType (typ.relabel j)
    Fin.elim0 et (andLeft (andRight (andRight hf)))
  have ec := valueUnique InternalListCodec.tailCode actualCodomain (codomain.relabel j)
    (Fin.cons (typ.relabel j) Fin.elim0) actualTail hc'
  have ha := outputTransport OriginalLambdaConstructor.arrow actualType (typ.relabel j)
    (Fin.cons actualDomain (Fin.cons actualCodomain Fin.elim0)) et (andRight (andRight (andRight hf)))
  apply graphInputTransport body beta 2 Theta (OrdinaryArithmetic.graphFormula OriginalLambdaConstructor.arrow)
    (typ.relabel j) (Fin.cons actualDomain (Fin.cons actualCodomain Fin.elim0))
    (Fin.cons (domain.relabel j) (Fin.cons (codomain.relabel j) Fin.elim0)) _ ha
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]; exact ed
  · rw [onEquality]; exact ec

theorem lambdaShapeForward (packed typ payload middle domain bodyPayload requestedDomain codomain : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hs : Nonempty (Derivation body Delta (LambdaShape packed))) :
    Nonempty (Derivation body Delta
      ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain)) := by
  have ha := shapeArrowRecover packed typ domain codomain (pairLeft packed typ payload hp)
    (rawDomainValue packed typ payload middle domain bodyPayload hp ht hm)
    (listTail typ requestedDomain codomain hf) hs
  have hh := listHead typ domain codomain (consArrowFields typ domain codomain ha)
  have he := valueUnique InternalListCodec.headCode requestedDomain domain
    (Fin.cons typ Fin.elim0) (listHead typ requestedDomain codomain hf) hh
  exact andIntro (consNonzero typ domain codomain ha) (by simpa only [equalEqn] using he)

theorem lambdaShapeBackward (packed typ payload middle domain bodyPayload requestedDomain codomain : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hs : Nonempty (Derivation body Delta
      ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))) :
    Nonempty (Derivation body Delta (LambdaShape packed)) := by
  have he : Nonempty (Derivation body Delta (eqn requestedDomain domain)) := by
    simpa only [equalEqn] using andRight hs
  have ha := headTransport InternalListCodec.consCode typ requestedDomain domain
    (Fin.cons codomain Fin.elim0) he (consFields typ requestedDomain codomain (andLeft hs) hf)
  exact shapeArrowIntro packed typ domain codomain (pairLeft packed typ payload hp)
    (rawDomainValue packed typ payload middle domain bodyPayload hp ht hm)
    (listTail typ requestedDomain codomain hf) ha

theorem lambdaShape_iff (packed typ payload middle domain bodyPayload requestedDomain codomain : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain))) :
    Nonempty (Derivation body Delta ((LambdaShape packed).iff
      ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))) := by
  let P := LambdaShape packed
  let Q := (equal typ (numeral 0)).not ⊓ equal requestedDomain domain
  obtain ⟨hp⟩ := hp
  obtain ⟨ht⟩ := ht
  obtain ⟨hm⟩ := hm
  obtain ⟨hf⟩ := hf
  obtain ⟨hforward⟩ := lambdaShapeForward packed typ payload middle domain bodyPayload requestedDomain codomain
    ⟨InternalBetaTotalityProof.addHyp hp P⟩ ⟨InternalBetaTotalityProof.addHyp ht P⟩
    ⟨InternalBetaTotalityProof.addHyp hm P⟩ ⟨InternalBetaTotalityProof.addHyp hf P⟩
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hbackward⟩ := lambdaShapeBackward packed typ payload middle domain bodyPayload requestedDomain codomain
    ⟨InternalBetaTotalityProof.addHyp hp Q⟩ ⟨InternalBetaTotalityProof.addHyp ht Q⟩
    ⟨InternalBetaTotalityProof.addHyp hm Q⟩ ⟨InternalBetaTotalityProof.addHyp hf Q⟩
    (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hforward)
    (Derivation.implicationIntroduction hbackward)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
