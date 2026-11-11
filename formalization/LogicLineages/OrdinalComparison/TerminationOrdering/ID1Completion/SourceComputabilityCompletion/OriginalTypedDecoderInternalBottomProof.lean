module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalRequestProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem bottomForward (state out t p suffix : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 bottomStep out state))) :
    Nonempty (Derivation body Delta (StepBottom out t p suffix)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hc := sameForward payload typ pop (constant 1 0) out p t xs hp ht ho
  apply orCases hc
  · have hh : Nonempty (Derivation body
        ((equal p t ⊓ graph1 pop out state) :: Delta) (equal p t ⊓ graph1 pop out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andLeft hh
    obtain ⟨hl⟩ := liveForward rest out suffix xs (withHyp hr _) (andRight hh)
    exact ⟨orLeft (Derivation.conjunctionIntroduction he hl)⟩
  · have hh : Nonempty (Derivation body
        (((equal p t).not ⊓ graph1 (constant 1 0) out state) :: Delta)
        ((equal p t).not ⊓ graph1 (constant 1 0) out state)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andLeft hh
    obtain ⟨hz⟩ := constantForward 0 out xs (andRight hh)
    exact ⟨orRight (Derivation.conjunctionIntroduction he hz)⟩

theorem bottomBackward (state out t p suffix : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepBottom out t p suffix))) :
    Nonempty (Derivation body Delta (graph1 bottomStep out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply orCases ho
  · have hh : Nonempty (Derivation body
        ((equal p t ⊓ StepLive out suffix) :: Delta) (equal p t ⊓ StepLive out suffix)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameYesIntro payload typ pop (constant 1 0) out p t xs
      (withHyp hp _) (withHyp ht _) (andLeft hh)
      (liveBackward rest out suffix xs (withHyp hr _) (andRight hh))
  · have hh : Nonempty (Derivation body
        (((equal p t).not ⊓ equal out (numeral 0)) :: Delta)
        ((equal p t).not ⊓ equal out (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameNoIntro payload typ pop (constant 1 0) out p t xs
      (withHyp hp _) (withHyp ht _) (andLeft hh) (constantBackward 0 out xs (andRight hh))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBottomProof
