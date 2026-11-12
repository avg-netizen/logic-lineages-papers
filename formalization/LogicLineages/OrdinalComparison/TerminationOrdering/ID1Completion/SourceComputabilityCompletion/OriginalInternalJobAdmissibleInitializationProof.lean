module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleInitializationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalQuotientComparisonProof (orLeft)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem initialization : OriginalInternalJobAdmissibleTargets.Initialization := by
 intro body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job hp hc hraw htyped hjob hs
 obtain ⟨facts⟩ := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsElim H G M W packed parameter typ raw c gamma hp hc hs
 have ha : Nonempty (Derivation body Delta (Admissible H M W (numeral 0) typ raw gamma c)) := by
  apply Nonempty.intro
  apply orLeft
  apply Derivation.conjunctionIntroduction
  · simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 0))
  · exact Derivation.conjunctionRight facts
 let xs : Fin 2 → OTerm alpha := ![packed,parameter]
 have ht := unaryValue InternalUnpair.left (.projection 0) typ packed xs (pairLeft packed typ raw hp) (projectionValue 0 xs)
 have hr := unaryValue InternalUnpair.right (.projection 0) raw packed xs (pairRight packed typ raw hp) (projectionValue 0 xs)
 have hj := binaryValue InternalPairing.pairing (rightOf (.projection 0)) (.projection 1)
  rawJob raw parameter xs hraw hr (projectionValue 1 xs)
 have hy := binaryValue InternalPairing.pairing (leftOf (.projection 0)) (pairOf (rightOf (.projection 0)) (.projection 1))
  typed typ rawJob xs htyped ht hj
 have hjobGraph : Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter)) :=
  binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) _
   job (numeral 0) typed xs hjob (constantValue 0 xs) hy
 obtain ⟨hg⟩ := hjobGraph
 obtain ⟨ha⟩ := ha
 exact ⟨Derivation.conjunctionIntroduction hg (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft facts) ha)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleInitializationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleInitializationProof
