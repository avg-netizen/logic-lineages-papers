module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedCopyCertificate NumberedRootDecomposition
open NumberedTypedFocus NumberedStepContexts NumberedStepCertificate NumberedNumericDecoding NumberedNumericRoot
open NumberedNumericStep
open OriginalApplicationFunctionCertificateDefinitions

theorem actualTypedLift :
    OriginalApplicationFunctionCertificateTargets.ActualTypedLift := by
  intro n arity symbols S Gamma table sigma tau fn fnOut arg child
  cases hf : focus child.path fn with
  | none => simp [stepTest,liftCertificate,focus,hf]
  | some f =>
    cases hb : decodePackedNumber n arity f.holeGamma child.replacement with
    | none => simp [stepTest,liftCertificate,focus,hf,hb]
    | some b =>
      obtain ⟨beta,b⟩ := b
      cases hs : decodeSelector n arity f.holeGamma child.root with
      | none => simp [stepTest,liftCertificate,focus,hf,hb,hs]
      | some selector =>
        simp only [stepTest,liftCertificate,focus,hf,Option.map_some,hb,hs]
        split
        next ht =>
          cases ht
          simp [plug,packedNumber,termCode,codeNumber]
        next _ => simp

theorem actualCoding : OriginalApplicationFunctionCertificateTargets.ActualCoding := by
 refine ⟨?_,?_,?_,?_⟩
 · intro raw; simp [stripStep]
 · intro raw; simp [stripStep,liftStep]
 · intro child
   simp [liftStep,stepCertificateNumber,liftCertificate,pathNumber,NumberedMultisetNumeric.numbersNumber]
 · intro child
   simp [stripStep,stepCertificateNumber,liftCertificate,pathNumber,NumberedMultisetNumeric.numbersNumber]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateProof
