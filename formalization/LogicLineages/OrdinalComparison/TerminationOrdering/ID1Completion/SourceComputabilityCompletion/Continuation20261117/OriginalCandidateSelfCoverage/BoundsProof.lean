module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem selfMember (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed parameter typ raw context gamma types out heads : OTerm alpha)
    (q : Request n arity H body Delta seed parameter typ raw context gamma types out)
    (hh : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed parameter)))
    : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out seed)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalCodeBoundsRecursion.bounds n)
    (Fin.cons raw Fin.elim0) _
  intro beta j Theta bounds hj hb
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hb
  have q' := RequestRenameProof.rename q j Theta hj
  have hh' := renameInto hh j Theta hj
  simp only [graph1Rename,graph2Rename] at hh'
  exact BoundsPairProof.selfMember n arity H (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (heads.relabel j) bounds q' hh' hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsProof
