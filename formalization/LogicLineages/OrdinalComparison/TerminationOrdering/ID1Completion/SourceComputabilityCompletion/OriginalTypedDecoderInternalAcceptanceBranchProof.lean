module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalListProof
open OriginalTypedDecoderInternalRequestSelectorsProof
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalTagBranchProof
open OriginalTypedDecoderInternalLocalDispatchProof OriginalTypedDecoderInternalDispatchSpecificationProof
open OriginalTypedDecoderInternalModeProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

def selectors : Fin 6 → Program 1 := ![mode,gamma,typ,tag,payload,rest]

theorem requestValues (state workCode request suffix m g t r tagCode payloadCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request m g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r tagCode payloadCode))) :
    ∀ i : Fin 6, Nonempty (Derivation body Gamma
      (graph1 (selectors i) (![m,g,t,tagCode,payloadCode,suffix] i) state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hw := pairRight state (numeral 1) workCode hs
  have hfields := consArrowFields workCode request suffix hc
  have hrequest := headValue work workCode request suffix xs hw hfields
  have hrest := tailValue work workCode request suffix xs hw hfields
  have hv := fun i => requestFieldValue currentRequest i request m g t r xs hrequest hr
  have htag := pairLeftValue raw r tagCode payloadCode xs (hv 3) hp
  have hpayload := pairRightValue raw r tagCode payloadCode xs (hv 3) hp
  intro i
  exact Fin.cases (hv 0) (Fin.cases (hv 1) (Fin.cases (hv 2)
    (Fin.cases htag (Fin.cases hpayload (Fin.cases hrest (fun k => Fin.elim0 k)))))) i

theorem modeAtForward (H : Program 1) (state workCode request suffix out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (graph1 (modeProgram H) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let live := InternalAcceptance.branch work (.projection 0) (modeProgram H)
  have hstatus := pairLeft state (numeral 1) workCode hs
  have hwork := pairRight state (numeral 1) workCode hs
  have he : Nonempty (Derivation body Gamma (equal (numeral 1) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  have hn : Nonempty (Derivation body Gamma (equal workCode z).not) := by
    simpa only [equalEqn] using andRight (andRight
      (InternalListCodecSupportProof.consDestruction workCode request suffix hc))
  have hlive := sameYesElim status (constant 1 1) live (constant 1 0)
    out (numeral 1) (numeral 1) xs hstatus (constantValue 1 xs) he ho
  exact nonzeroAtElim work (.projection 0) (modeProgram H) out workCode xs hwork hn hlive

theorem modeAtBackward (H : Program 1) (state workCode request suffix out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (ho : Nonempty (Derivation body Gamma (graph1 (modeProgram H) out state))) :
    Nonempty (Derivation body Gamma (graph1 (transition H) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let live := InternalAcceptance.branch work (.projection 0) (modeProgram H)
  have hstatus := pairLeft state (numeral 1) workCode hs
  have hwork := pairRight state (numeral 1) workCode hs
  have he : Nonempty (Derivation body Gamma (equal (numeral 1) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  have hn : Nonempty (Derivation body Gamma (equal workCode z).not) := by
    simpa only [equalEqn] using andRight (andRight
      (InternalListCodecSupportProof.consDestruction workCode request suffix hc))
  exact sameYesIntro status (constant 1 1) live (constant 1 0)
    out (numeral 1) (numeral 1) xs hstatus (constantValue 1 xs) he
    (nonzeroAtIntro work (.projection 0) (modeProgram H) out workCode xs hwork hn ho)

theorem termAtForward (H : Program 1) (i : Fin 8)
    (state workCode request suffix out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (termBranchSpec H out g t p suffix i)) := by
  have hv := requestValues state workCode request suffix (numeral 0) g t r (numeral i.val) p hs hc hr hp
  have hm := modeAtForward H state workCode request suffix out hs hc ho
  have hd := branchNumeralElim 0 0 mode _ (termDispatch H) out (Fin.cons state Fin.elim0) (hv 0) hm
  exact termLocalForward H state out g t p suffix (hv 1) (hv 2) (hv 4) (hv 5) i
    (termKnownForward H state out i (hv 3) hd)

theorem termAtBackward (H : Program 1) (i : Fin 8)
    (state workCode request suffix out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ho : Nonempty (Derivation body Gamma (termBranchSpec H out g t p suffix i))) :
    Nonempty (Derivation body Gamma (graph1 (transition H) out state)) := by
  have hv := requestValues state workCode request suffix (numeral 0) g t r (numeral i.val) p hs hc hr hp
  apply modeAtBackward H state workCode request suffix out hs hc
  apply branchNumeralIntro 0 0 mode _ (termDispatch H) out (Fin.cons state Fin.elim0) (hv 0)
  exact termKnownBackward H state out i (hv 3)
    (termLocalBackward H state out g t p suffix (hv 1) (hv 2) (hv 4) (hv 5) i ho)

theorem argumentsAtForward (H : Program 1) (i : Fin 8)
    (state workCode request suffix out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (argumentsBranchSpec out g t p suffix i)) := by
  have hv := requestValues state workCode request suffix (numeral 1) g t r (numeral i.val) p hs hc hr hp
  have hm := modeAtForward H state workCode request suffix out hs hc ho
  have h0 := branchNumeralElim 1 0 mode _ (termDispatch H) out (Fin.cons state Fin.elim0) (hv 0) hm
  have hd := branchNumeralElim 1 1 mode _ argumentsDispatch out (Fin.cons state Fin.elim0) (hv 0) h0
  exact argumentsLocalForward state out g t p suffix (hv 1) (hv 2) (hv 4) (hv 5) i
    (argumentsKnownForward state out i (hv 3) hd)

theorem argumentsAtBackward (H : Program 1) (i : Fin 8)
    (state workCode request suffix out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ho : Nonempty (Derivation body Gamma (argumentsBranchSpec out g t p suffix i))) :
    Nonempty (Derivation body Gamma (graph1 (transition H) out state)) := by
  have hv := requestValues state workCode request suffix (numeral 1) g t r (numeral i.val) p hs hc hr hp
  apply modeAtBackward H state workCode request suffix out hs hc
  apply branchNumeralIntro 1 0 mode _ (termDispatch H) out (Fin.cons state Fin.elim0) (hv 0)
  apply branchNumeralIntro 1 1 mode _ argumentsDispatch out (Fin.cons state Fin.elim0) (hv 0)
  exact argumentsKnownBackward state out i (hv 3)
    (argumentsLocalBackward state out g t p suffix (hv 1) (hv 2) (hv 4) (hv 5) i ho)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchProof
