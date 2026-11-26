module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalBetaTotalityProof InternalQuotientComparisonProof
open InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem anyMonotonicity : Targets.AnyMonotonicity := by
  intro E body alpha Delta left right candidate parameter hi ha
  have hw := PrimaryExpansionSoundness.AnyProof.anyWitness E body alpha Delta
    left candidate parameter ha
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness E left candidate parameter _ hw
  intro beta j Theta source hj hm he
  simp only [graph3Rename,numeral,sucRelabel,zRelabel]
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  exact PrimaryEdgeInclusion.AnyProof.anyIntroduction E body beta Theta
    (right.relabel j) source (candidate.relabel j) (parameter.relabel j)
    (eliminate (left.relabel j) (right.relabel j) source hi' hm) he

theorem memberStep (E : Program 3)
    (pool left right parameter leftOut rightOut candidate : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta
      (graph3 (PrimaryExpansion.expand E) leftOut pool left parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph3 (PrimaryExpansion.expand E) rightOut pool right parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) leftOut candidate))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) rightOut candidate)) := by
  obtain ⟨hd⟩ := PrimaryExpansionSoundness.Proof.expansionSoundness E pool left parameter leftOut candidate hl hm
  let A := graph2 contains (numeral 1) left candidate
  let B := graph2 contains (numeral 1) pool candidate ⊓
    PrimaryExpansionSoundness.sourceWitness E left candidate parameter
  have old : Nonempty (Derivation body (A :: Delta) (graph2 contains (numeral 1) rightOut candidate)) :=
    PrimaryExpansion.PreservationProof.internalPreservation E body alpha (A :: Delta)
      pool right parameter rightOut candidate (withHyp hr A)
      (eliminate left right candidate (withHyp hi A) ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have new : Nonempty (Derivation body (B :: Delta) (graph2 contains (numeral 1) rightOut candidate)) := by
    apply PrimaryExpansionSoundness.WitnessProof.casesWitness E left candidate parameter _
      (Nonempty.intro (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)))
    intro beta j Theta source hj hsource hedge
    simp only [graph2Rename,numeral,sucRelabel,zRelabel]
    have hi' := renameInto (withHyp hi B) j Theta hj
    rw [includedRename] at hi'
    have hr' := renameInto (withHyp hr B) j Theta hj
    rw [graph3Rename] at hr'
    have hp : Nonempty (Derivation body (B :: Delta) (graph2 contains (numeral 1) pool candidate)) :=
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    have hp' := renameInto hp j Theta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
    exact PrimaryEdgeInclusion.Proof.expansionEdgeInclusion E body beta Theta
      (pool.relabel j) (right.relabel j) source (candidate.relabel j) (parameter.relabel j)
      (rightOut.relabel j) (eliminate (left.relabel j) (right.relabel j) source hi' hsource)
      hp' hedge hr'
  obtain ⟨old⟩ := old
  obtain ⟨new⟩ := new
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction old)
    (Derivation.implicationIntroduction new)⟩

theorem expansionMonotonicity : Targets.ExpansionMonotonicity := by
  intro E body alpha Delta pool left right parameter leftOut rightOut hi hl hr
  apply introduce leftOut rightOut
  intro beta j Theta candidate hj hm
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  have hl' := renameInto hl j Theta hj
  rw [graph3Rename] at hl'
  have hr' := renameInto hr j Theta hj
  rw [graph3Rename] at hr'
  exact memberStep E (pool.relabel j) (left.relabel j) (right.relabel j) (parameter.relabel j)
    (leftOut.relabel j) (rightOut.relabel j) candidate hi' hl' hr' hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.StepProof
