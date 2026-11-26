module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)

theorem consTag (H : Program 1) (types raw gamma param value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 7) raw)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ ht
  intro beta j Theta tau head tail hj hc
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  have haj := renameInto ha j Theta hj
  rw [argumentsAcceptedRename] at haj
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have ihj := renameInto ih j Theta hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact ConsProof.consDefined H (types.relabel j) (raw.relabel j) (gamma.relabel j)
    (param.relabel j) (value.relabel j) tau head tail hc haj hvj ihj

theorem notNil (H : Program 1) (types raw gamma param value tag payload : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 6)).not))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply InternalApplicationValidityStackAppendInductionCoreProof.formulaCases (eqn tag (numeral 7))
  · have h7 := outputTransport InternalUnpair.left tag (numeral 7) (Fin.cons raw Fin.elim0)
      ⟨Derivation.hypothesis (body := body) (Gamma := eqn tag (numeral 7) :: Delta) List.mem_cons_self⟩ (withHyp ht _)
    exact consTag H types raw gamma param value h7 (withHyp ha _) (withHyp hv _) (withHyp ih _)
  · have hp' := reconstructPair raw tag payload (withHyp ht (eqn tag (numeral 7)).not) (withHyp hp _)
    have hn' := withHyp hn (eqn tag (numeral 7)).not
    have h7 : Nonempty (Derivation body ((eqn tag (numeral 7)).not :: Delta) (eqn tag (numeral 7)).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hbad := OriginalTypedDecoderInternalAcceptanceRejectedProof.argumentsRejected H raw tag payload types gamma hp'
      (by simpa only [InternalControlGraphSupportProof.equalEqn] using andIntro hn' h7) (withHyp ha _)
    obtain ⟨hbad⟩ := hbad
    exact ⟨Derivation.explosion hbad⟩

theorem atSelectors (H : Program 1) (types raw gamma param value tag payload : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply InternalApplicationValidityStackAppendInductionCoreProof.formulaCases (eqn tag (numeral 6))
  · have h6 := outputTransport InternalUnpair.left tag (numeral 6) (Fin.cons raw Fin.elim0)
      ⟨Derivation.hypothesis (body := body) (Gamma := eqn tag (numeral 6) :: Delta) List.mem_cons_self⟩ (withHyp ht _)
    exact SupportProof.nilDefined H types raw gamma param value payload
      (reconstructPair raw (numeral 6) payload h6 (withHyp hp _)) (withHyp ha _) (withHyp hv _)
  · exact notNil H types raw gamma param value tag payload (withHyp ht _) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hv _) (withHyp ih _)

theorem atTag (H : Program 1) (types raw gamma param value tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
  intro beta j Theta payload hj hp
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hp
  have htj := renameInto ht j Theta hj
  rw [graph1Rename] at htj
  have haj := renameInto ha j Theta hj
  rw [argumentsAcceptedRename] at haj
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have ihj := renameInto ih j Theta hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact atSelectors H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j)
    (value.relabel j) (tag.relabel j) payload htj hp haj hvj ihj

theorem close (H : Program 1) (types raw gamma param value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj ht
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at ht
  have haj := renameInto ha j Theta hj
  rw [argumentsAcceptedRename] at haj
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have ihj := renameInto ih j Theta hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact atTag H (types.relabel j) (raw.relabel j) (gamma.relabel j) (param.relabel j)
    (value.relabel j) tag ht haj hvj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.CoreProof
