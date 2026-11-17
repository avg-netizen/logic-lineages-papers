module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.TargetMinimumProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.SeedMinimumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem coherent (n : Nat) (arity : Fin n → Nat) (source : Program 2) (window : Program 1)
 (seed parameter typ raw context gamma types out candidate targetOut guardedOut targetGuardedOut : OTerm alpha)
 (q : OriginalPrimaryRerootInclusion.Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
 (hg : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.representative source (R n arity) window) guardedOut seed parameter)))
 (htg : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.representative source (R n arity) window) targetGuardedOut candidate parameter)))
 : Nonempty (Derivation body Delta (equal guardedOut targetGuardedOut)) := by
 apply programCases (R n arity) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta minimumOut hj hnew
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hnew
 rw [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename]
 have q' := OriginalPrimaryRerootInclusion.RequestRenameProof.rename q j Theta hj
 have hg' := renameInto hg j Theta hj
 rw [graph2Rename] at hg'
 have htg' := renameInto htg j Theta hj
 rw [graph2Rename] at htg'
 exact TargetMinimumProof.coherent n arity source window (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (candidate.relabel j) (targetOut.relabel j) (guardedOut.relabel j) (targetGuardedOut.relabel j) minimumOut q' hg' htg' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.SeedMinimumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.SeedMinimumProof
