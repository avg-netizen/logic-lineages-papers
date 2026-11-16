module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthSyntaxProof
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
def depthMatrix (n : Nat) (raw fuel : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  graph1 (OriginalEnumerationDepth.depth n) (.var (.inr 0)) (raw.relabel Sum.inl) ⊓
    InternalLessThan.strictLess (.var (.inr 0)) (suc (fuel.relabel Sum.inl))

theorem depthWitness (n : Nat) (raw fuel d : OTerm alpha) :
    (depthMatrix n raw fuel).subst (Sum.elim Term.var (fun _ : Fin 1 => emb d)) =
      (graph1 (OriginalEnumerationDepth.depth n) d raw ⊓ InternalLessThan.strictLess d (suc fuel)) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb d)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => d) a)) := by
    funext a
    cases a <;> rfl
  unfold depthMatrix
  rw [he]
  simp only [conjunctionSubst,graph1Subst,InternalLessThan.strictLess,orderSubst,sucSubst,
    witnessLift,Term.subst,Sum.elim_inr]

theorem boundSubst {beta : Type} (n : Nat) (raw fuel : OTerm alpha) (ts : alpha → OTerm beta) :
    (Targets.depthBound n raw fuel).subst (fun a => emb (ts a)) =
      Targets.depthBound n (raw.subst ts) (fuel.subst ts) := by
  change (SourceComputabilityFormulaSupportProof.existsOne (depthMatrix n raw fuel)).subst (fun a => emb (ts a)) =
    SourceComputabilityFormulaSupportProof.existsOne (depthMatrix n (raw.subst ts) (fuel.subst ts))
  rw [existsSubst,liftedEmbedding]
  simp only [depthMatrix,conjunctionSubst,graph1Subst,InternalLessThan.strictLess,orderSubst,sucSubst,
    liftSubst,Term.subst,Sum.elim_inr]

theorem boundRename {beta : Type} (n : Nat) (raw fuel : OTerm alpha) (j : alpha → beta) :
    (Targets.depthBound n raw fuel).relabel j = Targets.depthBound n (raw.relabel j) (fuel.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.depthBound n raw fuel).subst (fun a => emb (.var (j a))) = _
  rw [boundSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthSyntaxProof
