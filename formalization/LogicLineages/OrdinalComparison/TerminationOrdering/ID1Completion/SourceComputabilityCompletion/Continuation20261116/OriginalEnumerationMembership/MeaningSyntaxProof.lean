module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SixArgumentSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc emb zSubst sucSubst)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalApplicationResultStackCompositionSyntaxProof (graph1Subst)
open Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
variable {alpha : Type}
attribute [local irreducible] programGraph

open Continuation20261115
theorem meaningSubst {beta : Type} (n : Nat) (raw bound fuel types heads labels tupleBound : OTerm alpha) (ts : alpha → OTerm beta) :
    (Meaning.holds n raw bound fuel types heads labels tupleBound).subst (fun a => emb (ts a)) =
      Meaning.holds n (raw.subst ts) (bound.subst ts) (fuel.subst ts) (types.subst ts)
        (heads.subst ts) (labels.subst ts) (tupleBound.subst ts) := by
  unfold Meaning.holds OriginalEnumerationFields.Targets.accepted
  rw [conjunctionSubst, SixArgumentSubstitutionProof.acceptedSubst,
    DepthSyntaxProof.boundSubst]

@[simp] theorem meaningRename {beta : Type} (n : Nat) (raw bound fuel types heads labels tupleBound : OTerm alpha) (j : alpha → beta) :
    (Meaning.holds n raw bound fuel types heads labels tupleBound).relabel j =
      Meaning.holds n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
        (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Meaning.holds n raw bound fuel types heads labels tupleBound).subst (fun a => emb (.var (j a))) = _
  rw [meaningSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
