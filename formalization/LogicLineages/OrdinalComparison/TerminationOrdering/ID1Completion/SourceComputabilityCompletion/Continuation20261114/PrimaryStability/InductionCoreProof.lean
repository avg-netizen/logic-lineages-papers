module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionCoreProof
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

open InductionDefinitions.Induction InductionSyntaxProof
open PrimaryMonotonicity.InclusionProof PrimaryIteration.RecursionProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowApply (E : Program 3) (count pool initial first parameter out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) first pool initial parameter)))
    (hs : Nonempty (Derivation body Delta (PrimaryMonotonicity.included first initial)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out count pool initial parameter))) :
    Nonempty (Derivation body Delta (result initial out)) := by
  obtain ⟨h⟩ := elimination body alpha 5 Delta (matrix E count)
    (fun i => emb (![pool,initial,first,parameter,out] i)) hrow
  rw [InductionSyntaxProof.matrixWitness] at h
  obtain ⟨hf⟩ := andIntro he (andIntro hs hi)
  exact ⟨Derivation.implicationElimination h hf⟩

theorem zeroCore (E : Program 3) (pool initial parameter out : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out z pool initial parameter))) :
    Nonempty (Derivation body Delta (result initial out)) := by
  have he := valueUnique (PrimaryIteration.iterate E) out initial ![z,pool,initial,parameter]
    hi (zeroValue E pool initial parameter)
  apply introduce out initial
  intro beta j Theta candidate hj hm
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  exact headTransport contains (suc z) (out.relabel j) (initial.relabel j)
    (Fin.cons candidate Fin.elim0) he' hm

theorem successorCore (E : Program 3) (count pool initial first parameter out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) first pool initial parameter)))
    (hs : Nonempty (Derivation body Delta (PrimaryMonotonicity.included first initial)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out (suc count) pool initial parameter))) :
    Nonempty (Derivation body Delta (result initial out)) := by
  apply programCases (PrimaryIteration.iterate E)
    (Fin.cons count (Fin.cons pool (Fin.cons initial (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta previous hj hp
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hp
  have hrow' := renameInto hrow j Theta hj
  rw [atCountRename] at hrow'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hs' := renameInto hs j Theta hj
  rw [includedRename] at hs'
  have hi' := renameInto hi j Theta hj
  simp only [graph4Rename,sucRelabel] at hi'
  have hind := rowApply E (count.relabel j) (pool.relabel j) (initial.relabel j)
    (first.relabel j) (parameter.relabel j) previous hrow' he' hs' hp
  have hexpand := successorRecover E (count.relabel j) previous (out.relabel j)
    (pool.relabel j) (initial.relabel j) (parameter.relabel j) hp hi'
  have hmono := PrimaryMonotonicity.StepProof.expansionMonotonicity E body beta Theta
    (pool.relabel j) previous (initial.relabel j) (parameter.relabel j)
    (out.relabel j) (first.relabel j) hind hexpand he'
  exact InclusionProof.transitive (out.relabel j) (first.relabel j) (initial.relabel j) hmono hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionCoreProof
