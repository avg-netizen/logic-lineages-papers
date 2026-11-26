module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.AtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsPairProof
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
    (seed parameter typ raw context gamma types out heads bounds : OTerm alpha)
    (q : Request n arity H body Delta seed parameter typ raw context gamma types out)
    (hh : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed parameter)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) bounds raw)))
    : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out seed)) := by
  apply OriginalDecodedRank.SupportProof.pairCases bounds _
  intro beta j Theta size labels hj hp
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have q' := RequestRenameProof.rename q j Theta hj
  have hh' := renameInto hh j Theta hj
  simp only [graph1Rename,graph2Rename] at hh'
  have hb' := renameInto hb j Theta hj
  simp only [graph1Rename,graph2Rename] at hb'
  exact AtFieldsProof.selfMember n arity H (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (heads.relabel j) (bounds.relabel j) size labels q' hh' hb' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsPairProof
