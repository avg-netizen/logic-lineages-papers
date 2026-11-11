module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalModeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalDispatchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal mode subtree of the frozen transition, not a replacement program. -/
def modeProgram (H : Program 1) : Program 1 :=
  ifSame mode (constant 1 0) (termDispatch H)
    (ifSame mode (constant 1 1) argumentsDispatch (constant 1 0))

theorem modeOtherForward (H : Program 1) (state out m g t value p suffix : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph1 mode m state)))
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (hn : Nonempty (Derivation body Delta (equal m (numeral 0)).not))
    (ho : Nonempty (Derivation body Delta
      (graph1 (ifSame mode (constant 1 1) argumentsDispatch (constant 1 0)) out state))) :
    Nonempty (Derivation body Delta (StepModeDispatch H out m g t value p suffix)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hc := sameForward mode (constant 1 1) argumentsDispatch (constant 1 0)
    out m (numeral 1) xs hm (constantValue 1 xs) ho
  apply orCases hc
  · have hh : Nonempty (Derivation body
        ((equal m (numeral 1) ⊓ graph1 argumentsDispatch out state) :: Delta)
        (equal m (numeral 1) ⊓ graph1 argumentsDispatch out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andLeft hh
    obtain ⟨hs⟩ := argumentsDispatchForward state out g t value p suffix
      (withHyp hg _) (withHyp ht _) (withHyp hv _) (withHyp hp _) (withHyp hr _) (andRight hh)
    exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction he hs))⟩
  · have hh : Nonempty (Derivation body
        (((equal m (numeral 1)).not ⊓ graph1 (constant 1 0) out state) :: Delta)
        ((equal m (numeral 1)).not ⊓ graph1 (constant 1 0) out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andIntro (withHyp hn _) (andLeft hh)
    obtain ⟨hz⟩ := constantForward 0 out xs (andRight hh)
    exact ⟨orRight (orRight (Derivation.conjunctionIntroduction he hz))⟩

theorem modeForward (H : Program 1) (state out m g t value p suffix : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph1 mode m state)))
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 (modeProgram H) out state))) :
    Nonempty (Derivation body Delta (StepModeDispatch H out m g t value p suffix)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let other := ifSame mode (constant 1 1) argumentsDispatch (constant 1 0)
  have hc := sameForward mode (constant 1 0) (termDispatch H) other
    out m (numeral 0) xs hm (constantValue 0 xs) ho
  apply orCases hc
  · have hh : Nonempty (Derivation body
        ((equal m (numeral 0) ⊓ graph1 (termDispatch H) out state) :: Delta)
        (equal m (numeral 0) ⊓ graph1 (termDispatch H) out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andLeft hh
    obtain ⟨hs⟩ := termDispatchForward H state out g t value p suffix
      (withHyp hg _) (withHyp ht _) (withHyp hv _) (withHyp hp _) (withHyp hr _) (andRight hh)
    exact ⟨orLeft (Derivation.conjunctionIntroduction he hs)⟩
  · have hh : Nonempty (Derivation body
        (((equal m (numeral 0)).not ⊓ graph1 other out state) :: Delta)
        ((equal m (numeral 0)).not ⊓ graph1 other out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact modeOtherForward H state out m g t value p suffix
      (withHyp hm _) (withHyp hg _) (withHyp ht _) (withHyp hv _) (withHyp hp _) (withHyp hr _)
      (andLeft hh) (andRight hh)

theorem modeBackward (H : Program 1) (state out m g t value p suffix : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph1 mode m state)))
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hv : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepModeDispatch H out m g t value p suffix))) :
    Nonempty (Derivation body Delta (graph1 (modeProgram H) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let other := ifSame mode (constant 1 1) argumentsDispatch (constant 1 0)
  apply orCases ho
  · have hh : Nonempty (Derivation body
        ((equal m (numeral 0) ⊓ StepTermDispatch H out g t value p suffix) :: Delta)
        (equal m (numeral 0) ⊓ StepTermDispatch H out g t value p suffix)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameYesIntro mode (constant 1 0) (termDispatch H) other out m (numeral 0) xs
      (withHyp hm _) (constantValue 0 xs) (andLeft hh)
      (termDispatchBackward H state out g t value p suffix
        (withHyp hg _) (withHyp ht _) (withHyp hv _) (withHyp hp _) (withHyp hr _) (andRight hh))
  · let A := (equal m (numeral 1) ⊓ StepArgumentsDispatch out g t value p suffix) ⊔
        (((equal m (numeral 0)).not ⊓ (equal m (numeral 1)).not) ⊓ equal out (numeral 0))
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm' := withHyp hm A
    have hg' := withHyp hg A
    have ht' := withHyp ht A
    have hv' := withHyp hv A
    have hp' := withHyp hp A
    have hr' := withHyp hr A
    apply orCases ha
    · let B := equal m (numeral 1) ⊓ StepArgumentsDispatch out g t value p suffix
      have hb : Nonempty (Derivation body (B :: A :: Delta) B) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have he : Nonempty (Derivation body (B :: A :: Delta) (eqn m (numeral 1))) := by
        simpa only [equalEqn] using andLeft hb
      have hmone := outputTransport mode m (numeral 1) xs he (withHyp hm' B)
      apply branchNumeralIntro 1 0 mode other (termDispatch H) out xs hmone
      apply branchNumeralIntro 1 1 mode (constant 1 0) argumentsDispatch out xs hmone
      exact argumentsDispatchBackward state out g t value p suffix
        (withHyp hg' B) (withHyp ht' B) (withHyp hv' B) (withHyp hp' B) (withHyp hr' B) (andRight hb)
    · let B := ((equal m (numeral 0)).not ⊓ (equal m (numeral 1)).not) ⊓ equal out (numeral 0)
      have hb : Nonempty (Derivation body (B :: A :: Delta) B) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply sameNoIntro mode (constant 1 0) (termDispatch H) other out m (numeral 0) xs
        (withHyp hm' B) (constantValue 0 xs) (andLeft (andLeft hb))
      exact sameNoIntro mode (constant 1 1) argumentsDispatch (constant 1 0) out m (numeral 1) xs
        (withHyp hm' B) (constantValue 1 xs) (andRight (andLeft hb))
        (constantBackward 0 out xs (andRight hb))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalModeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalModeProof
