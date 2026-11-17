module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem member (T P : Program 2) (E : Program 3)
    (seed parameter sourcePool sourceOut targetPool candidate : OTerm alpha)
    (had : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 P sourcePool seed parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) sourceOut seed parameter)))
    (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included targetPool sourcePool)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) targetPool candidate)))
    (hw : Nonempty (Derivation body Delta (PrimaryExpansionSoundness.sourceWitness E sourceOut candidate parameter))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) sourceOut candidate)) := by
  have hpool := eliminate targetPool sourcePool candidate hi hm
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness E sourceOut candidate parameter _ hw
  intro beta j Theta source hj hs he
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename]
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at had'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hp'
  have hl' := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hl'
  have hpool' := renameInto hpool j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hpool'
  exact LengthAlignedPrimary.InternalProof.internalEdgeClosure T P E body beta Theta
    (seed.relabel j) (parameter.relabel j) (sourcePool.relabel j) (sourceOut.relabel j)
    source (candidate.relabel j) had' hp' hl' hs hpool' he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureWitnessProof
