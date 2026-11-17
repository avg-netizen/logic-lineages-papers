module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimaryRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.SeedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimarySelfProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn z sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem member (T P : Program 2) (E : Program 3)
 (seed parameter pool out : OTerm alpha)
 (had : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 P pool seed parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) out seed parameter))) :
 Nonempty (Derivation body Delta (graph2 contains (numeral 1) out seed)) := by
 apply programCases (LengthAlignedPrimary.countOfPool P) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta count hj hc
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hc
 have had' := renameInto had j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at had'
 have hp' := renameInto hp j Theta hj
 rw [graph2Rename] at hp'
 have hl' := renameInto hl j Theta hj
 rw [graph2Rename] at hl'
 have hr := PrimaryRunProof.recover T P E (seed.relabel j) (parameter.relabel j) (pool.relabel j) (out.relabel j) count had' hp' hl' hc
 exact PrimaryIteration.SeedProof.internalSeedMembership E body beta Theta count (pool.relabel j) (seed.relabel j) (parameter.relabel j) (out.relabel j) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimarySelfProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimarySelfProof
