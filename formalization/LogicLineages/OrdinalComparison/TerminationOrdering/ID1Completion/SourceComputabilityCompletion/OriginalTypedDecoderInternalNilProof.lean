module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalRequestProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The original nil branch accepts only both literal zero tests. -/
theorem nilAtZeroForward (state out t p suffix : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (hz : Nonempty (Derivation body Delta (equal p (numeral 0))))
    (ho : Nonempty (Derivation body Delta (graph1 nilStep out state))) :
    Nonempty (Derivation body Delta (StepArgumentsNil out t p suffix)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let inner := ifSame typ (constant 1 0) pop (constant 1 0)
  have hi := sameYesElim payload (constant 1 0) inner (constant 1 0) out p (numeral 0) xs
    hp (constantValue 0 xs) hz ho
  have hc := sameForward typ (constant 1 0) pop (constant 1 0) out t (numeral 0) xs
    ht (constantValue 0 xs) hi
  apply orCases hc
  · have hh : Nonempty (Derivation body
        ((equal t (numeral 0) ⊓ graph1 pop out state) :: Delta)
        (equal t (numeral 0) ⊓ graph1 pop out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hg⟩ := andIntro (withHyp hz _) (andLeft hh)
    obtain ⟨hl⟩ := liveForward rest out suffix xs (withHyp hr _) (andRight hh)
    exact ⟨orLeft (Derivation.conjunctionIntroduction hg hl)⟩
  · have hh : Nonempty (Derivation body
        (((equal t (numeral 0)).not ⊓ graph1 (constant 1 0) out state) :: Delta)
        ((equal t (numeral 0)).not ⊓ graph1 (constant 1 0) out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hn⟩ := andLeft hh
    obtain ⟨hv⟩ := constantForward 0 out xs (andRight hh)
    exact ⟨orRight (Derivation.conjunctionIntroduction (orRight hn) hv)⟩

theorem nilForward (state out t p suffix : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 nilStep out state))) :
    Nonempty (Derivation body Delta (StepArgumentsNil out t p suffix)) := by
  apply formulaCases (equal p (numeral 0)) _
  · exact nilAtZeroForward state out t p suffix (withHyp ht _) (withHyp hp _) (withHyp hr _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ho _)
  · let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
    have hn : Nonempty (Derivation body ((equal p (numeral 0)).not :: Delta) (equal p (numeral 0)).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := sameNoElim payload (constant 1 0) (ifSame typ (constant 1 0) pop (constant 1 0))
      (constant 1 0) out p (numeral 0) xs (withHyp hp _) (constantValue 0 xs) hn (withHyp ho _)
    obtain ⟨hz⟩ := constantForward 0 out xs hv
    exact ⟨orRight (Derivation.conjunctionIntroduction
      (orLeft (Derivation.hypothesis List.mem_cons_self)) hz)⟩

theorem nilRejectTypeIntro (state out t p : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hn : Nonempty (Derivation body Delta (equal t (numeral 0)).not))
    (hz : Nonempty (Derivation body Delta (equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 nilStep out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let inner := ifSame typ (constant 1 0) pop (constant 1 0)
  apply formulaCases (equal p (numeral 0)) _
  · apply sameYesIntro payload (constant 1 0) inner (constant 1 0) out p (numeral 0) xs
      (withHyp hp _) (constantValue 0 xs) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameNoIntro typ (constant 1 0) pop (constant 1 0) out t (numeral 0) xs
      (withHyp ht _) (constantValue 0 xs) (withHyp hn _) (constantBackward 0 out xs (withHyp hz _))
  · exact sameNoIntro payload (constant 1 0) inner (constant 1 0) out p (numeral 0) xs
      (withHyp hp _) (constantValue 0 xs) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (constantBackward 0 out xs (withHyp hz _))

theorem nilBackward (state out t p suffix : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepArgumentsNil out t p suffix))) :
    Nonempty (Derivation body Delta (graph1 nilStep out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let inner := ifSame typ (constant 1 0) pop (constant 1 0)
  apply orCases ho
  · have hh : Nonempty (Derivation body
        (((equal p (numeral 0) ⊓ equal t (numeral 0)) ⊓ StepLive out suffix) :: Delta)
        ((equal p (numeral 0) ⊓ equal t (numeral 0)) ⊓ StepLive out suffix)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply sameYesIntro payload (constant 1 0) inner (constant 1 0) out p (numeral 0) xs
      (withHyp hp _) (constantValue 0 xs) (andLeft (andLeft hh))
    exact sameYesIntro typ (constant 1 0) pop (constant 1 0) out t (numeral 0) xs
      (withHyp ht _) (constantValue 0 xs) (andRight (andLeft hh))
      (liveBackward rest out suffix xs (withHyp hr _) (andRight hh))
  · let A := ((equal p (numeral 0)).not ⊔ (equal t (numeral 0)).not) ⊓ equal out (numeral 0)
    have hh : Nonempty (Derivation body (A :: Delta) A) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp' := withHyp hp A
    have ht' := withHyp ht A
    have hz := andRight hh
    apply orCases (andLeft hh)
    · exact sameNoIntro payload (constant 1 0) inner (constant 1 0) out p (numeral 0) xs
        (withHyp hp' _) (constantValue 0 xs) ⟨Derivation.hypothesis List.mem_cons_self⟩
        (constantBackward 0 out xs (withHyp hz _))
    · exact nilRejectTypeIntro state out t p (withHyp ht' _) (withHyp hp' _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hz _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNilProof
