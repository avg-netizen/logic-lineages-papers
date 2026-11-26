module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.BoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.CutoffProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open PrimaryUncoveredCount
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem cutoffKnown (E : Program 3)
    (size pool initial parameter out next initialRemaining remaining nextRemaining : OTerm alpha)
    (hlen : Nonempty (Derivation body Delta (lengthGraph size pool)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out size pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 count remaining pool out)))
    (hnext : Nonempty (Derivation body Delta (graph2 count nextRemaining pool next))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out)) := by
  let S := PrimaryMonotonicity.included next out
  obtain ⟨hbudget⟩ := InductionProof.iterationBudget E body alpha (S.not :: Delta)
    size pool initial parameter out next initialRemaining remaining
    (withHyp hi S.not) (withHyp he S.not) (withHyp hinit S.not) (withHyp hrem S.not)
  have hb : Nonempty (Derivation body (S.not :: Delta)
      (bounded (InternalAdditionLawsProof.add size remaining) initialRemaining)) := by
    exact ⟨disjunctionElimination hbudget
      (Derivation.implicationIntroduction (Derivation.explosion (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.hypothesis List.mem_cons_self))))
      (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩
  have hbound := BoundProof.internalBound body alpha (S.not :: Delta) pool initial initialRemaining size
    (withHyp hinit S.not) (withHyp hlen S.not)
  have hzero := ArithmeticProof.budgetZero size remaining
    (ArithmeticProof.boundTrans (InternalAdditionLawsProof.add size remaining) initialRemaining size hb hbound)
  obtain ⟨hcase⟩ := StepProof.stepAlternative E body alpha (S.not :: Delta)
    pool out next parameter remaining nextRemaining (withHyp he S.not)
    (withHyp hrem S.not) (withHyp hnext S.not)
  have hd : Nonempty (Derivation body (S.not :: Delta) (ltF nextRemaining remaining)) := by
    exact ⟨disjunctionElimination hcase
      (Derivation.implicationIntroduction (Derivation.explosion (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.hypothesis List.mem_cons_self))))
      (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩
  obtain ⟨hzero⟩ := hzero
  obtain ⟨hd⟩ := hd
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha nextRemaining
  exact ⟨Derivation.classical (Derivation.implicationElimination (weakenClosed hn (S.not :: Delta))
    (orderRight nextRemaining hzero hd))⟩

theorem withCurrent (E : Program 3) (size pool initial parameter out next initialRemaining remaining : OTerm alpha)
    (hlen : Nonempty (Derivation body Delta (lengthGraph size pool)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out size pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 count remaining pool out)))
    : Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out)) := by
  apply programCases count (Fin.cons pool (Fin.cons next Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hv
  have hlen' := renameInto hlen j Theta hj
  rw [lengthRename] at hlen'
  have hi' := renameInto hi j Theta hj
  rw [graph4Rename] at hi'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hinit' := renameInto hinit j Theta hj
  rw [graph2Rename] at hinit'
  have hrem' := renameInto hrem j Theta hj
  rw [graph2Rename] at hrem'
  exact cutoffKnown E (size.relabel j) (pool.relabel j) (initial.relabel j) (parameter.relabel j) (out.relabel j) (next.relabel j) (initialRemaining.relabel j) (remaining.relabel j) value hlen' hi' he' hinit' hrem' hv

theorem withInitial (E : Program 3) (size pool initial parameter out next initialRemaining : OTerm alpha)
    (hlen : Nonempty (Derivation body Delta (lengthGraph size pool)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out size pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 count initialRemaining pool initial)))
    : Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out)) := by
  apply programCases count (Fin.cons pool (Fin.cons out Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hv
  have hlen' := renameInto hlen j Theta hj
  rw [lengthRename] at hlen'
  have hi' := renameInto hi j Theta hj
  rw [graph4Rename] at hi'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hinit' := renameInto hinit j Theta hj
  rw [graph2Rename] at hinit'
  exact withCurrent E (size.relabel j) (pool.relabel j) (initial.relabel j) (parameter.relabel j) (out.relabel j) (next.relabel j) (initialRemaining.relabel j) value hlen' hi' he' hinit' hv

theorem literalLengthCutoffCore (E : Program 3) (size pool initial parameter out next : OTerm alpha)
    (hlen : Nonempty (Derivation body Delta (lengthGraph size pool)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out size pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    : Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out)) := by
  apply programCases count (Fin.cons pool (Fin.cons initial Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hv
  have hlen' := renameInto hlen j Theta hj
  rw [lengthRename] at hlen'
  have hi' := renameInto hi j Theta hj
  rw [graph4Rename] at hi'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  exact withInitial E (size.relabel j) (pool.relabel j) (initial.relabel j) (parameter.relabel j) (out.relabel j) (next.relabel j) value hlen' hi' he' hv

theorem literalLengthCutoff : Targets.LiteralLengthCutoff := by
  intro E body alpha Delta size pool initial parameter out next hlen hi he
  exact literalLengthCutoffCore E size pool initial parameter out next hlen hi he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.CutoffProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.CutoffProof
