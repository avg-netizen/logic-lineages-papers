module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnSubst eqnRelabel zSubst zRelabel sucRelabel bindEmbedding bindTerm nextEmbedding nextTerm)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceSupportProof
open OriginalTypedDecoderInternalBranchProof (orCases)
open OriginalTypedDecoderStepSpecification
open OriginalUniverseDecoderStepSpecification (nonemptySpec guardSpec)
open OriginalUniverseDecoderInternalSyntaxProof
open OriginalUniverseDecoderInternalFuelInclusionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem nonemptyRefinement (H : Program 1) (M contextWindow : Program 2)
    (out initial work c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (nonemptySpec H M contextWindow out initial work c))) :
    Nonempty (Derivation body Delta (stepResult H out initial)) := by
  apply nonemptyCases H M contextWindow out initial work c _ h
  intro beta j Theta ys hj hq
  rw [stepResultRename]
  let C := guardSpec M contextWindow (numeral 1) (ys 0) (c.relabel j)
  let T := OriginalTypedDecoderStepSpecification.stepSpec H (out.relabel j) (initial.relabel j)
  apply orCases (andRight hq)
  · have ht : Nonempty (Derivation body ((C ⊓ T) :: Theta) (C ⊓ T)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨ht⟩ := OriginalTypedDecoderInternalProof.fullBackward H (out.relabel j)
      (initial.relabel j) (andRight ht)
    exact ⟨orRight ht⟩
  · have hz : Nonempty (Derivation body ((C.not ⊓ equal (out.relabel j) (numeral 0)) :: Theta)
        (C.not ⊓ equal (out.relabel j) (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := andRight hz
    exact ⟨orLeft hz⟩

/-- Exact all-raw one-step refinement: guard rejection is the only extra
outcome. The typed branch is recovered from the accepted original source
arithmetic specification at the SAME raw state. -/
theorem stepRefinement (H : Program 1) (M contextWindow : Program 2)
    (out initial c : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.transition H M contextWindow) out initial c))) :
    Nonempty (Derivation body Delta (stepResult H out initial)) := by
  apply stateCases H M contextWindow out initial c _
    (OriginalUniverseDecoderInternalStepProof.fullForward H M contextWindow out initial c h)
  intro beta j Theta ys hj hq
  rw [stepResultRename]
  let rejected := (equal (ys 0) (numeral 1)).not ⊓ equal (out.relabel j) (numeral 0)
  let empty := equal (ys 1) (numeral 0) ⊓ equal (out.relabel j) (initial.relabel j)
  let pending := (equal (ys 1) (numeral 0)).not ⊓
    nonemptySpec H M contextWindow (out.relabel j) (initial.relabel j) (ys 1) (c.relabel j)
  let active := equal (ys 0) (numeral 1) ⊓ (empty ⊔ pending)
  apply orCases (andRight hq)
  · have hr : Nonempty (Derivation body (rejected :: Theta) rejected) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := andRight hr
    exact ⟨orLeft hz⟩
  · have ha : Nonempty (Derivation body (active :: Theta) active) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases (andRight ha)
    · have he : Nonempty (Derivation body (empty :: active :: Theta) empty) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp (andLeft hq) active) empty
      obtain ⟨hs⟩ := withHyp (andLeft ha) empty
      obtain ⟨he⟩ := he
      have hfields := andIntro hp
        (show Nonempty (Derivation body (empty :: active :: Theta)
          (((equal (ys 0) (numeral 1)).not ⊓ equal (out.relabel j) (numeral 0)) ⊔
            (equal (ys 0) (numeral 1) ⊓
              (empty ⊔ ((equal (ys 1) (numeral 0)).not ⊓
                StepNonemptyWork H (out.relabel j) (ys 1)))))) from
          ⟨orRight (Derivation.conjunctionIntroduction hs (orLeft he))⟩)
      obtain ⟨ht⟩ := OriginalTypedDecoderInternalProof.fullBackward H (out.relabel j)
        (initial.relabel j)
        (OriginalTypedDecoderInternalStateSyntaxProof.stateIntro H (out.relabel j)
          (initial.relabel j) ys hfields)
      exact ⟨orRight ht⟩
    · have hp : Nonempty (Derivation body (pending :: active :: Theta) pending) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact nonemptyRefinement H M contextWindow (out.relabel j) (initial.relabel j)
        (ys 1) (c.relabel j) (andRight hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionStepProof
