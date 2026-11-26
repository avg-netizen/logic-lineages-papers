module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.BoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.HeadsProof
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
    (seed parameter typ raw context gamma types out : OTerm alpha)
    (q : Request n arity H body Delta seed parameter typ raw context gamma types out)
    : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out seed)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalClassCodes.heads n arity) ![seed,parameter] _
  intro beta j Theta heads hj hh
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hv : (fun i => (![seed,parameter] i).relabel j) = ![seed.relabel j,parameter.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hv] at hh
  have q' := RequestRenameProof.rename q j Theta hj
  exact BoundsProof.selfMember n arity H (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) heads q' hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.HeadsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.HeadsProof
