module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLocalDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalTagBranchProof OriginalTypedDecoderInternalDispatchSpecificationProof
open OriginalTypedDecoderInternalLocalDispatchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tagAtNumeral (state value : OTerm alpha) (i : Nat)
    (ht : Nonempty (Derivation body Delta (graph1 tag value state)))
    (he : Nonempty (Derivation body Delta (equal value (numeral i)))) :
    Nonempty (Derivation body Delta (graph1 tag (numeral i) state)) := by
  have he' : Nonempty (Derivation body Delta (eqn value (numeral i))) := by
    simpa only [equalEqn] using he
  exact outputTransport tag value (numeral i) (Fin.cons state Fin.elim0) he' ht

theorem termDispatchForward (H : Program 1) (state out g t value p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 (termDispatch H) out state))) :
    Nonempty (Derivation body Delta (StepTermDispatch H out g t value p suffix)) := by
  apply tagCases value _
  · intro i Theta inc he
    have htag := tagAtNumeral state value i.val (weakenProof hv inc) he
    have hbranch := termKnownForward H state out i htag (weakenProof ho inc)
    have hspec := termLocalForward H state out g t p suffix
      (weakenProof hg inc) (weakenProof ht inc) (weakenProof hp inc) (weakenProof hr inc) i hbranch
    exact termSpecIntro H out g t value p suffix i (andIntro he hspec)
  · intro Theta inc hn
    have hz := termUnknownForward H state out value (weakenProof hv inc) hn (weakenProof ho inc)
    exact termSpecFallback H out g t value p suffix (andIntro hn hz)

theorem termDispatchBackward (H : Program 1) (state out g t value p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepTermDispatch H out g t value p suffix))) :
    Nonempty (Derivation body Delta (graph1 (termDispatch H) out state)) := by
  apply termSpecCases H out g t value p suffix _ ho
  · intro i Theta inc hf
    have htag := tagAtNumeral state value i.val (weakenProof hv inc) (andLeft hf)
    have hbranch := termLocalBackward H state out g t p suffix
      (weakenProof hg inc) (weakenProof ht inc) (weakenProof hp inc) (weakenProof hr inc) i (andRight hf)
    exact termKnownBackward H state out i htag hbranch
  · intro Theta inc hf
    exact termUnknownBackward H state out value (weakenProof hv inc) (andLeft hf) (andRight hf)

theorem argumentsDispatchForward (state out g t value p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 (argumentsDispatch) out state))) :
    Nonempty (Derivation body Delta (StepArgumentsDispatch out g t value p suffix)) := by
  apply tagCases value _
  · intro i Theta inc he
    have htag := tagAtNumeral state value i.val (weakenProof hv inc) he
    have hbranch := argumentsKnownForward state out i htag (weakenProof ho inc)
    have hspec := argumentsLocalForward state out g t p suffix
      (weakenProof hg inc) (weakenProof ht inc) (weakenProof hp inc) (weakenProof hr inc) i hbranch
    exact argumentsSpecIntro out g t value p suffix i (andIntro he hspec)
  · intro Theta inc hn
    have hz := argumentsUnknownForward state out value (weakenProof hv inc) hn (weakenProof ho inc)
    exact argumentsSpecFallback out g t value p suffix (andIntro hn hz)

theorem argumentsDispatchBackward (state out g t value p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepArgumentsDispatch out g t value p suffix))) :
    Nonempty (Derivation body Delta (graph1 (argumentsDispatch) out state)) := by
  apply argumentsSpecCases out g t value p suffix _ ho
  · intro i Theta inc hf
    have htag := tagAtNumeral state value i.val (weakenProof hv inc) (andLeft hf)
    have hbranch := argumentsLocalBackward state out g t p suffix
      (weakenProof hg inc) (weakenProof ht inc) (weakenProof hp inc) (weakenProof hr inc) i (andRight hf)
    exact argumentsKnownBackward state out i htag hbranch
  · intro Theta inc hf
    exact argumentsUnknownBackward state out value (weakenProof hv inc) (andLeft hf) (andRight hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchProof
