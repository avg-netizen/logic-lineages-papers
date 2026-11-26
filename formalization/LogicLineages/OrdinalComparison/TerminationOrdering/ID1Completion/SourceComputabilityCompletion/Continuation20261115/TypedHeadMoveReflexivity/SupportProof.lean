module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open OriginalTypedDecoderInternalAcceptance OriginalTypedDecoderInternalAcceptanceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem permutationAtValue (H : Program 1) (argumentTypes base gamma value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H argumentTypes base gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value base (numeral 0)))) :
    Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base base)) := by
  have hn := TypedArgumentEntriesDefined.Proof.typedDefined body H alpha Delta argumentTypes base gamma (numeral 0) value ha hv
  apply zeroSuccessorCases Delta value _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta entries hj he
    have hvj := renameInto hv j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hvj ⊢
    have hs := outputTransport ArgumentEntriesRecursor.extract (value.relabel j) (suc entries)
      (Fin.cons (base.relabel j) (Fin.cons (numeral 0) Fin.elim0)) he hvj
    exact ArgumentPermutationReflexivity.Proof.original body beta Theta (base.relabel j) entries hs

theorem permutation : Targets.InternalPermutation := by
  intro body H alpha Delta argumentTypes base gamma ha
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons base (Fin.cons (numeral 0) Fin.elim0)) _
  intro beta j Theta value hj hv
  simp only [consTermRename,emptyRename,GuardedSourceSyntaxProof.numeralRename] at hv
  have haj := renameInto ha j Theta hj
  rw [argumentsAcceptedRename] at haj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  exact permutationAtValue H (argumentTypes.relabel j) (base.relabel j) (gamma.relabel j) value haj hv

theorem accept (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw base symbols types argumentTypes gamma : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (hs : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H argumentTypes base gamma))) :
    Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
      ![raw,base,raw,base,symbols,types])) :=
  (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta raw base raw base symbols types).mpr
    (andIntro (andIntro (andIntro hw hs) (OriginalHeadMoveReflexivity.ClassProof.classSelf body alpha Delta raw))
      (permutation body H alpha Delta argumentTypes base gamma ha))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.SupportProof
