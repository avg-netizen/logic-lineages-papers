module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimaryRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.GenericPrimaryAtPoolProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SyntaxProof
theorem preserved (R : Program 1) (T P : Program 2) (E : Program 3)
 (seed parameter out ref pool : OTerm alpha)
 (had : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) out seed parameter)))
 (hs : Nonempty (Derivation body Delta (graph1 R ref seed)))
 (hf : Nonempty (Derivation body Delta (forwardClosed R E ref parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 P pool seed parameter)))
 : Nonempty (Derivation body Delta (allAccepted R ref out)) := by
 apply InternalAcceptanceSupportProof.programCases (LengthAlignedPrimary.countOfPool P) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta count hj hnew
 rw [scalarAllAcceptedRename]
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalRecursionGraphStepSyntaxProof.emptyRename] at hnew
 have had' := renameInto had j Theta hj
 simp only [graph1Rename,graph2Rename,forwardClosedRename,numeral,sucRelabel,zRelabel] at had'
 have hl' := renameInto hl j Theta hj
 simp only [graph1Rename,graph2Rename,forwardClosedRename,numeral,sucRelabel,zRelabel] at hl'
 have hs' := renameInto hs j Theta hj
 simp only [graph1Rename,graph2Rename,forwardClosedRename,numeral,sucRelabel,zRelabel] at hs'
 have hf' := renameInto hf j Theta hj
 simp only [graph1Rename,graph2Rename,forwardClosedRename,numeral,sucRelabel,zRelabel] at hf'
 have hp' := renameInto hp j Theta hj
 simp only [graph1Rename,graph2Rename,forwardClosedRename,numeral,sucRelabel,zRelabel] at hp'
 have hr := OriginalPrimaryReverseMembership.PrimaryRunProof.recover T P E (seed.relabel j) (parameter.relabel j) (pool.relabel j) (out.relabel j) count had' hp' hl' hnew
 exact RunProof.preserved R E count (pool.relabel j) (seed.relabel j) (parameter.relabel j) (out.relabel j) (ref.relabel j) hr hs' hf'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.GenericPrimaryAtPoolProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.GenericPrimaryAtPoolProof
