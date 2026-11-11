module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedPayloadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder (ifSame)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalNumberedPayloadProof
open OriginalUniverseDecoderInternalBooleanProof OriginalUniverseDecoder
open OriginalUniverseDecoderInternalAcceptanceGuardRootProof
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The source numbered guard reads only the actual packed head and the SAME
outer context. It does not compare the head signature's result with the request. -/
theorem numberedExtraForward (M W : Program 2)
    (request gamma typ raw payload label head recorded base extraTypes extras c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (hn : Nonempty (Derivation body Delta (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (ho : Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) request c))) :
    Nonempty (Derivation body Delta (graph2 W (numeral 1) head c)) := by
  let xs : Fin 2 → OTerm alpha := ![request,c]
  have hv := requestTagPayload request (numeral 0) gamma typ raw (numeral 5) payload c hr hp
  have hh := numberedFieldValue OriginalUniverseDecoder.payload 1 payload label head recorded base extraTypes extras xs hv.2 hn
  have he : Nonempty (Derivation body Delta (equal (numeral 5 : OTerm alpha) (numeral 5))) := by
    rw [equalEqn]; exact ⟨refl (numeral 5)⟩
  have h1 := sameNoElim tag (constant 2 1) _ _ (numeral 1) (numeral 5) (numeral 1) xs
    hv.1 (constantValue 1 xs) (excludeNumeral (numeral 5) 5 1 (by decide) he) ho
  have h4 := sameNoElim tag (constant 2 4) _ _ (numeral 1) (numeral 5) (numeral 4) xs
    hv.1 (constantValue 4 xs) (excludeNumeral (numeral 5) 5 4 (by decide) he) h1
  have h5 := sameYesElim tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)
    (numeral 1) (numeral 5) (numeral 5) xs hv.1 (constantValue 5 xs) he h4
  have hw := andLeft (filterForward (windowAt W numberedHead) (constant 2 1) xs h5)
  exact binaryRecover W numberedHead context (numeral 1) head c xs hw hh (projectionValue 1 xs)

theorem numberedExtraBackward (M W : Program 2)
    (request gamma typ raw payload label head recorded base extraTypes extras c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (hn : Nonempty (Derivation body Delta (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (hw : Nonempty (Derivation body Delta (graph2 W (numeral 1) head c))) :
    Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) request c)) := by
  let xs : Fin 2 → OTerm alpha := ![request,c]
  have hv := requestTagPayload request (numeral 0) gamma typ raw (numeral 5) payload c hr hp
  have hh := numberedFieldValue OriginalUniverseDecoder.payload 1 payload label head recorded base extraTypes extras xs hv.2 hn
  have he : Nonempty (Derivation body Delta (equal (numeral 5 : OTerm alpha) (numeral 5))) := by
    rw [equalEqn]; exact ⟨refl (numeral 5)⟩
  apply sameNoIntro tag (constant 2 1) _ _ (numeral 1) (numeral 5) (numeral 1) xs
    hv.1 (constantValue 1 xs) (excludeNumeral (numeral 5) 5 1 (by decide) he)
  apply sameNoIntro tag (constant 2 4) _ _ (numeral 1) (numeral 5) (numeral 4) xs
    hv.1 (constantValue 4 xs) (excludeNumeral (numeral 5) 5 4 (by decide) he)
  apply sameYesIntro tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)
    (numeral 1) (numeral 5) (numeral 5) xs hv.1 (constantValue 5 xs) he
  exact filterBackward (windowAt W numberedHead) (constant 2 1) xs
    (binaryValue W numberedHead context (numeral 1) head c xs hw hh (projectionValue 1 xs))
    (constantValue 1 xs)

theorem numberedRootForward (M W : Program 2)
    (request gamma typ raw payload label head recorded base extraTypes extras c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (hn : Nonempty (Derivation body Delta (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (ho : Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) request c))) :
    Nonempty (Derivation body Delta (graph2 M (numeral 1) typ c ⊓ graph2 W (numeral 1) head c)) := by
  have hroot := termRootForward M W request gamma typ raw c hr ho
  exact andIntro (andLeft hroot)
    (numberedExtraForward M W request gamma typ raw payload label head recorded base extraTypes extras c hr hp hn (andRight hroot))

theorem numberedRootBackward (M W : Program 2)
    (request gamma typ raw payload label head recorded base extraTypes extras c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (hn : Nonempty (Derivation body Delta (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (hm : Nonempty (Derivation body Delta (graph2 M (numeral 1) typ c)))
    (hw : Nonempty (Derivation body Delta (graph2 W (numeral 1) head c))) :
    Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) request c)) :=
  termRootBackward M W request gamma typ raw c hr hm
    (numberedExtraBackward M W request gamma typ raw payload label head recorded base extraTypes extras c hr hp hn hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardNumberedProof
