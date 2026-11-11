module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardUnaryProof
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
open OriginalTypedDecoderInternalBranchProof
open OriginalUniverseDecoderInternalBooleanProof OriginalUniverseDecoder
open OriginalUniverseDecoderInternalAcceptanceGuardRootProof
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaExtraForward (M W : Program 2) (r d c : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag (numeral 1) r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (he : Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (graph2 M (numeral 1) d c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hsame : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  have h := sameYesElim tag (constant 2 1) (oneIf (memberAt M domain)) _
    (numeral 1) (numeral 1) (numeral 1) xs hv (constantValue 1 xs) hsame he
  exact binaryRecover M domain context (numeral 1) d c xs
    (andLeft (filterForward (memberAt M domain) (constant 2 1) xs h)) hd (projectionValue 1 xs)

theorem lambdaExtraBackward (M W : Program 2) (r d c : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag (numeral 1) r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (hm : Nonempty (Derivation body Delta (graph2 M (numeral 1) d c))) :
    Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hsame : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  apply sameYesIntro tag (constant 2 1) (oneIf (memberAt M domain)) _
    (numeral 1) (numeral 1) (numeral 1) xs hv (constantValue 1 xs) hsame
  exact filterBackward (memberAt M domain) (constant 2 1) xs
    (binaryValue M domain context (numeral 1) d c xs hm hd (projectionValue 1 xs)) (constantValue 1 xs)

theorem ordinaryExtraForward (M W : Program 2) (r head c : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag (numeral 4) r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain head r c)))
    (he : Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (graph2 W (numeral 1) head c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hsame : Nonempty (Derivation body Delta (equal (numeral 4 : OTerm alpha) (numeral 4))) := by
    rw [equalEqn]; exact ⟨refl (numeral 4)⟩
  have hrest := sameNoElim tag (constant 2 1) (oneIf (memberAt M domain)) _
    (numeral 1) (numeral 4) (numeral 1) xs hv (constantValue 1 xs)
    (excludeNumeral (numeral 4) 4 1 (by decide) hsame) he
  have h := sameYesElim tag (constant 2 4) (oneIf (windowAt W domain)) _
    (numeral 1) (numeral 4) (numeral 4) xs hv (constantValue 4 xs) hsame hrest
  exact binaryRecover W domain context (numeral 1) head c xs
    (andLeft (filterForward (windowAt W domain) (constant 2 1) xs h)) hd (projectionValue 1 xs)

theorem ordinaryExtraBackward (M W : Program 2) (r head c : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag (numeral 4) r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain head r c)))
    (hw : Nonempty (Derivation body Delta (graph2 W (numeral 1) head c))) :
    Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hsame : Nonempty (Derivation body Delta (equal (numeral 4 : OTerm alpha) (numeral 4))) := by
    rw [equalEqn]; exact ⟨refl (numeral 4)⟩
  apply sameNoIntro tag (constant 2 1) (oneIf (memberAt M domain)) _
    (numeral 1) (numeral 4) (numeral 1) xs hv (constantValue 1 xs)
    (excludeNumeral (numeral 4) 4 1 (by decide) hsame)
  apply sameYesIntro tag (constant 2 4) (oneIf (windowAt W domain)) _
    (numeral 1) (numeral 4) (numeral 4) xs hv (constantValue 4 xs) hsame
  exact filterBackward (windowAt W domain) (constant 2 1) xs
    (binaryValue W domain context (numeral 1) head c xs hw hd (projectionValue 1 xs)) (constantValue 1 xs)

theorem unaryGuardSelectors (i : Nat) (r g t rawCode p d child c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode (numeral i) p)))
    (hd : Nonempty (Derivation body Delta (StepPair p d child))) :
    Nonempty (Derivation body Delta (graph2 tag (numeral i) r c)) ∧
      Nonempty (Derivation body Delta (graph2 domain d r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hfields := requestTagPayload r (numeral 0) g t rawCode (numeral i) p c hr hp
  exact ⟨hfields.1,pairLeftValue payload p d child xs hfields.2 hd⟩

theorem lambdaGuardForward (M W : Program 2) (r g t rawCode p d child c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode (numeral 1) p)))
    (hd : Nonempty (Derivation body Delta (StepPair p d child)))
    (hg : Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (graph2 M (numeral 1) t c ⊓ graph2 M (numeral 1) d c)) := by
  have hroot := termRootForward M W r g t rawCode c hr hg
  have hf := unaryGuardSelectors 1 r g t rawCode p d child c hr hp hd
  exact andIntro (andLeft hroot) (lambdaExtraForward M W r d c hf.1 hf.2 (andRight hroot))

theorem lambdaGuardBackward (M W : Program 2) (r g t rawCode p d child c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode (numeral 1) p)))
    (hd : Nonempty (Derivation body Delta (StepPair p d child)))
    (ht : Nonempty (Derivation body Delta (graph2 M (numeral 1) t c)))
    (hm : Nonempty (Derivation body Delta (graph2 M (numeral 1) d c))) :
    Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c)) := by
  have hf := unaryGuardSelectors 1 r g t rawCode p d child c hr hp hd
  exact termRootBackward M W r g t rawCode c hr ht (lambdaExtraBackward M W r d c hf.1 hf.2 hm)

theorem ordinaryGuardForward (M W : Program 2) (r g t rawCode p head base c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode (numeral 4) p)))
    (hd : Nonempty (Derivation body Delta (StepPair p head base)))
    (hg : Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (graph2 M (numeral 1) t c ⊓ graph2 W (numeral 1) head c)) := by
  have hroot := termRootForward M W r g t rawCode c hr hg
  have hf := unaryGuardSelectors 4 r g t rawCode p head base c hr hp hd
  exact andIntro (andLeft hroot) (ordinaryExtraForward M W r head c hf.1 hf.2 (andRight hroot))

theorem ordinaryGuardBackward (M W : Program 2) (r g t rawCode p head base c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode (numeral 4) p)))
    (hd : Nonempty (Derivation body Delta (StepPair p head base)))
    (ht : Nonempty (Derivation body Delta (graph2 M (numeral 1) t c)))
    (hw : Nonempty (Derivation body Delta (graph2 W (numeral 1) head c))) :
    Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c)) := by
  have hf := unaryGuardSelectors 4 r g t rawCode p head base c hr hp hd
  exact termRootBackward M W r g t rawCode c hr ht (ordinaryExtraBackward M W r head c hf.1 hf.2 hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardUnaryProof
