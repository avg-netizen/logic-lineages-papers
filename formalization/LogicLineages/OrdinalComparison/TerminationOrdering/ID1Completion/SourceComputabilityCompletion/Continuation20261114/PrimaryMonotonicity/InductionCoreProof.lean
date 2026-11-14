module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionCoreProof
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

open InductionDefinitions InductionSyntaxProof InclusionProof
open PrimaryIteration.RecursionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowApply (E : Program 3)
    (count pool left right parameter leftOut rightOut : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count)))
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) leftOut count pool left parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) rightOut count pool right parameter))) :
    Nonempty (Derivation body Delta (included leftOut rightOut)) := by
  obtain ⟨h⟩ := elimination body alpha 6 Delta (matrix E count)
    (fun i => emb (![pool,left,right,parameter,leftOut,rightOut] i)) hrow
  rw [InductionSyntaxProof.matrixWitness] at h
  obtain ⟨hf⟩ := andIntro hi (andIntro hl hr)
  exact ⟨Derivation.implicationElimination h hf⟩

theorem zeroCore (E : Program 3)
    (pool left right parameter leftOut rightOut : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) leftOut z pool left parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) rightOut z pool right parameter))) :
    Nonempty (Derivation body Delta (included leftOut rightOut)) := by
  have heL := valueUnique (PrimaryIteration.iterate E) leftOut left ![z,pool,left,parameter]
    hl (zeroValue E pool left parameter)
  have heR := valueUnique (PrimaryIteration.iterate E) rightOut right ![z,pool,right,parameter]
    hr (zeroValue E pool right parameter)
  apply introduce leftOut rightOut
  intro beta j Theta candidate hj hm
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  have heL' := renameInto heL j Theta hj
  have heR' := renameInto heR j Theta hj
  rw [eqnRelabel] at heL' heR'
  obtain ⟨heR'⟩ := heR'
  have hmL := headTransport contains (numeral 1) (leftOut.relabel j) (left.relabel j)
    (Fin.cons candidate Fin.elim0) heL' hm
  have hmR := eliminate (left.relabel j) (right.relabel j) candidate hi' hmL
  exact headTransport contains (numeral 1) (right.relabel j) (rightOut.relabel j)
    (Fin.cons candidate Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm heR'⟩ hmR

theorem successorWithLeft (E : Program 3)
    (count pool left right parameter leftOut rightOut previousLeft : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count)))
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) leftOut (suc count) pool left parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) rightOut (suc count) pool right parameter)))
    (hp : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) previousLeft count pool left parameter))) :
    Nonempty (Derivation body Delta (included leftOut rightOut)) := by
  apply programCases (PrimaryIteration.iterate E)
    (Fin.cons count (Fin.cons pool (Fin.cons right (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta previousRight hj hq
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Theta hj
  rw [atCountRename] at hrow'
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  have hl' := renameInto hl j Theta hj
  simp only [graph4Rename,sucRelabel] at hl'
  have hr' := renameInto hr j Theta hj
  simp only [graph4Rename,sucRelabel] at hr'
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  have hind := rowApply E (count.relabel j) (pool.relabel j) (left.relabel j)
    (right.relabel j) (parameter.relabel j) (previousLeft.relabel j) previousRight hrow' hi' hp' hq
  exact StepProof.expansionMonotonicity E body beta Theta (pool.relabel j)
    (previousLeft.relabel j) previousRight (parameter.relabel j) (leftOut.relabel j)
    (rightOut.relabel j) hind
    (successorRecover E (count.relabel j) (previousLeft.relabel j) (leftOut.relabel j)
      (pool.relabel j) (left.relabel j) (parameter.relabel j) hp' hl')
    (successorRecover E (count.relabel j) previousRight (rightOut.relabel j)
      (pool.relabel j) (right.relabel j) (parameter.relabel j) hq hr')

theorem successorCore (E : Program 3)
    (count pool left right parameter leftOut rightOut : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count)))
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) leftOut (suc count) pool left parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) rightOut (suc count) pool right parameter))) :
    Nonempty (Derivation body Delta (included leftOut rightOut)) := by
  apply programCases (PrimaryIteration.iterate E)
    (Fin.cons count (Fin.cons pool (Fin.cons left (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta previousLeft hj hp
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hp
  have hrow' := renameInto hrow j Theta hj
  rw [atCountRename] at hrow'
  have hi' := renameInto hi j Theta hj
  rw [includedRename] at hi'
  have hl' := renameInto hl j Theta hj
  simp only [graph4Rename,sucRelabel] at hl'
  have hr' := renameInto hr j Theta hj
  simp only [graph4Rename,sucRelabel] at hr'
  exact successorWithLeft E (count.relabel j) (pool.relabel j) (left.relabel j)
    (right.relabel j) (parameter.relabel j) (leftOut.relabel j) (rightOut.relabel j)
    previousLeft hrow' hi' hl' hr' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionCoreProof
