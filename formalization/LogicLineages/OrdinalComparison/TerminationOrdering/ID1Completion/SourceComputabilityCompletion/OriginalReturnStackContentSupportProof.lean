module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnStackContentSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual transition functionality identifies the complete returned cons,
including its old result suffix. Neither head nor suffix equality is supplied. -/
theorem restoreFields (step : Program 1)
 (input candidate out rest outRest candidateStack stack expected value old outOld : OTerm alpha)
 (hcandidate : Nonempty (Derivation body Delta (graph1 step candidate input)))
 (hout : Nonempty (Derivation body Delta (graph1 step out input)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate rest candidateStack)))
 (hcs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode candidateStack expected old)))
 (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out outRest stack)))
 (hos : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value outOld))) :
 Nonempty (Derivation body Delta (eqn expected value ⊓ (eqn rest outRest ⊓ eqn old outOld))) := by
 have heq := valueUnique step candidate out (Fin.cons input Fin.elim0) hcandidate hout
 have hp := OriginalInternalAnnotationEqualityProof.pairFields candidate out rest candidateStack outRest stack hcp hop heq
 have hs := outputTransport InternalListCodec.consCode candidateStack stack
  (Fin.cons expected (Fin.cons old Fin.elim0)) (andRight hp) hcs
 have hv := valueUnique InternalListCodec.headCode expected value (Fin.cons stack Fin.elim0)
  (InternalRawListRecursionSupportProof.consHead stack expected old hs)
  (InternalRawListRecursionSupportProof.consHead stack value outOld hos)
 have ht := valueUnique InternalListCodec.tailCode old outOld (Fin.cons stack Fin.elim0)
  (InternalRawListRecursionSupportProof.consTail stack expected old hs)
  (InternalRawListRecursionSupportProof.consTail stack value outOld hos)
 exact andIntro hv (andIntro (andLeft hp) ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnStackContentSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnStackContentSupportProof
