module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.ConsProof
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
theorem atList (raw param value tau head tail entries entry listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry entries))) :
    Nonempty (Derivation body Delta (eqn value z).not) :=
  SupportProof.positiveOutput raw param value listCode hv
    (StandaloneConsExtraction.Proof.consSuccess body alpha Delta raw tau head tail param entries entry listCode hc ht hp hl)

theorem at1 (raw param value tau head tail entries entry : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) tail param)))
    (hentry : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    : Nonempty (Derivation body Delta (eqn value z).not) := by
  apply programCases InternalListCodec.consCode (Fin.cons entry (Fin.cons entries (Fin.elim0))) _
  intro beta j Theta listCode hj hx
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at hvj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at htj
  have hentryj := renameInto hentry j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at hentryj
  exact atList (raw.relabel j) (param.relabel j) (value.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (entries.relabel j) (entry.relabel j) listCode hcj hvj htj hentryj hx

theorem at0 (raw param value tau head tail entries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) tail param)))
    : Nonempty (Derivation body Delta (eqn value z).not) := by
  apply programCases InternalPairing.pairing (Fin.cons tau (Fin.cons head (Fin.elim0))) _
  intro beta j Theta entry hj hx
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at hvj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel] at htj
  exact at1 (raw.relabel j) (param.relabel j) (value.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (entries.relabel j) entry hcj hvj htj hx

theorem atTailValue (H : Program 1) (raw gamma param value tau head tail tailTypes tailValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H tailTypes tail gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  have hn := BindingProof.belowRawApply H raw tail tailTypes gamma param tailValue ih
    (CrossRootCacheCoherence.SupportProof.consTailStrict raw tau head tail hc) (andIntro ha ht)
  apply zeroSuccessorCases Delta tailValue _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta entries hj he
    change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
    rw [eqnRelabel,zRelabel]
    have hcj := renameInto hc j Theta hj
    rw [graph3Rename] at hcj
    have hvj := renameInto hv j Theta hj
    rw [graph2Rename] at hvj
    have htj := renameInto ht j Theta hj
    rw [graph2Rename] at htj
    have hs := outputTransport ArgumentEntriesRecursor.extract (tailValue.relabel j) (suc entries)
      (Fin.cons (tail.relabel j) (Fin.cons (param.relabel j) Fin.elim0)) he htj
    exact at0 (raw.relabel j) (param.relabel j) (value.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) entries hcj hvj hs

theorem atTail (H : Program 1) (raw gamma param value tau head tail tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H tailTypes tail gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons tail (Fin.cons param Fin.elim0)) _
  intro beta j Theta tailValue hj ht
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at ht
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have haj := renameInto ha j Theta hj
  rw [argumentsAcceptedRename] at haj
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have ihj := renameInto ih j Theta hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact atTailValue H (raw.relabel j) (gamma.relabel j) (param.relabel j) (value.relabel j) (tau.relabel j)
    (head.relabel j) (tail.relabel j) (tailTypes.relabel j) tailValue hcj haj hvj ihj ht

theorem consDefined (H : Program 1) (types raw gamma param value tau head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H types raw gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)))
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw H raw))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  apply OriginalTypedDecoderTransportContextProof.arrowCases types _
  intro beta j Theta requested tailTypes hj hf
  change Nonempty (Derivation body Theta ((eqn value z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have haj := renameInto ha j Theta hj
  rw [argumentsAcceptedRename] at haj
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have ihj := renameInto ih j Theta hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact atTail H (raw.relabel j) (gamma.relabel j) (param.relabel j) (value.relabel j) (tau.relabel j)
    (head.relabel j) (tail.relabel j) tailTypes hcj
    (SupportProof.tailAccepted H (types.relabel j) (raw.relabel j) (gamma.relabel j) (tau.relabel j)
      (head.relabel j) (tail.relabel j) requested tailTypes hcj hf haj) hvj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.ConsProof
