module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedPayloadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalBinaryProof OriginalTypedDecoderInternalNumberedPayloadProof
open OriginalLambdaConstructorGraphSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variablePair (raw index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    Nonempty (Derivation body Delta (StepPair raw (numeral 0) index)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  exact pairFields (.projection 0) raw (numeral 0) index xs (projectionValue 0 xs)
    (variableTag (.projection 0) raw index xs (projectionValue 0 xs) hc)
    (variableIndex (.projection 0) raw index xs (projectionValue 0 xs) hc)

theorem bottomPair (raw typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ))) :
    Nonempty (Derivation body Delta (StepPair raw (numeral 3) typ)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  exact pairFields (.projection 0) raw (numeral 3) typ xs (projectionValue 0 xs)
    (bottomTag (.projection 0) raw typ xs (projectionValue 0 xs) hc)
    (bottomType (.projection 0) raw typ xs (projectionValue 0 xs) hc)

theorem nilPair (raw : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (StepPair raw (numeral 6) (numeral 0))) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  exact pairFields (.projection 0) raw (numeral 6) (numeral 0) xs (projectionValue 0 xs)
    (nilTag (.projection 0) raw xs (projectionValue 0 xs) hc)
    (nilPayload (.projection 0) raw xs (projectionValue 0 xs) hc)

/-- Open the original numeric payload without changing the raw constructor.
The resulting field is an internal totality witness, never an added premise. -/
theorem payloadCases (raw : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (payload : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph1 (rightOf (.projection 0)) payload (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases (rightOf (.projection 0)) (Fin.cons raw Fin.elim0) psi
  intro beta j Theta payload hj hp
  simp only [consTermRename,emptyRename] at hp
  exact next beta j Theta payload hj hp

theorem lambdaPairs (raw payload domain child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload raw))) :
    Nonempty (Derivation body Delta
      (StepPair raw (numeral 1) payload ⊓ StepPair payload domain child)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  have htag := lambdaTag (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  have hd := lambdaDomain (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  have hb := lambdaBody (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  exact andIntro (pairFields (.projection 0) raw (numeral 1) payload xs (projectionValue 0 xs) htag hp)
    (pairFields (rightOf (.projection 0)) payload domain child xs hp hd hb)

theorem applicationPairs (raw payload domain fn arg : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload raw))) :
    Nonempty (Derivation body Delta
      (StepPair raw (numeral 2) payload ⊓ StepBinaryPayload payload domain fn arg)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  have htag := applicationTag (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
  have hd := applicationDomain (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
  have hf := applicationFunction (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
  have ha := applicationArgument (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
  exact andIntro (pairFields (.projection 0) raw (numeral 2) payload xs (projectionValue 0 xs) htag hp)
    (binaryFields (rightOf (.projection 0)) payload domain fn arg xs hp hd hf ha)

theorem ordinaryPairs (raw payload head base : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload raw))) :
    Nonempty (Derivation body Delta
      (StepPair raw (numeral 4) payload ⊓ StepPair payload head base)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  have htag := ordinaryTag (.projection 0) raw head base xs (projectionValue 0 xs) hc
  have hh := ordinaryHead (.projection 0) raw head base xs (projectionValue 0 xs) hc
  have hb := ordinaryBase (.projection 0) raw head base xs (projectionValue 0 xs) hc
  exact andIntro (pairFields (.projection 0) raw (numeral 4) payload xs (projectionValue 0 xs) htag hp)
    (pairFields (rightOf (.projection 0)) payload head base xs hp hh hb)

theorem numberedPairs (raw payload label head recorded base types extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,types,extras])))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload raw))) :
    Nonempty (Derivation body Delta
      (StepPair raw (numeral 5) payload ⊓
        StepNumberedPayload payload label head recorded base types extras)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  have htag := numberedTag (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc
  apply andIntro (pairFields (.projection 0) raw (numeral 5) payload xs (projectionValue 0 xs) htag hp)
  apply OriginalTypedDecoderInternalNumberedPayloadProof.numberedFields
    (rightOf (.projection 0)) payload label head recorded base types extras xs hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => ?_))))) i
  · exact numberedLabel (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc
  · exact numberedHead (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc
  · exact numberedType (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc
  · exact numberedBase (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc
  · exact numberedTypes (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc
  · obtain rfl : k = 0 := Fin.eq_zero k
    exact numberedExtras (.projection 0) raw label head recorded base types extras xs (projectionValue 0 xs) hc

theorem consPairs (raw payload domain head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload raw))) :
    Nonempty (Derivation body Delta
      (StepPair raw (numeral 7) payload ⊓ StepBinaryPayload payload domain head tail)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  have htag := consTag (.projection 0) raw domain head tail xs (projectionValue 0 xs) hc
  have hd := consType (.projection 0) raw domain head tail xs (projectionValue 0 xs) hc
  have hh := consHead (.projection 0) raw domain head tail xs (projectionValue 0 xs) hc
  have ht := consTail (.projection 0) raw domain head tail xs (projectionValue 0 xs) hc
  exact andIntro (pairFields (.projection 0) raw (numeral 7) payload xs (projectionValue 0 xs) htag hp)
    (binaryFields (rightOf (.projection 0)) payload domain head tail xs hp hd hh ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportConstructorProof
