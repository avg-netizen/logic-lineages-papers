module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedSyntaxProof
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
open OriginalContextInsertionSyntaxProof (lengthSubst)
open Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
variable {alpha : Type}
attribute [local irreducible] programGraph

def lengthMatrix (types bound : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  OriginalContextInsertion.lengthGraph (.var (.inr 0)) (types.relabel Sum.inl) ⊓
    InternalLessThan.strictLess (.var (.inr 0)) (suc (bound.relabel Sum.inl))

theorem lengthWitness (types bound len : OTerm alpha) :
    (lengthMatrix types bound).subst (Sum.elim Term.var (fun _ : Fin 1 => emb len)) =
      (OriginalContextInsertion.lengthGraph len types ⊓ InternalLessThan.strictLess len (suc bound)) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb len)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => len) a)) := by
    funext a
    cases a <;> rfl
  unfold lengthMatrix
  rw [he]
  simp only [conjunctionSubst,lengthSubst,InternalLessThan.strictLess,orderSubst,sucSubst,
    witnessLift,Term.subst,Sum.elim_inr]

theorem allowedSubst {beta : Type} (types allowed bound : OTerm alpha) (ts : alpha → OTerm beta) :
    (Targets.typesAllowed types allowed bound).subst (fun a => emb (ts a)) =
      Targets.typesAllowed (types.subst ts) (allowed.subst ts) (bound.subst ts) := by
  unfold Targets.typesAllowed
  rw [conjunctionSubst,membersSubst]
  change ((SourceComputabilityFormulaSupportProof.existsOne (lengthMatrix types bound)).subst (fun a => emb (ts a)) ⊓
    Continuation20261115.OriginalTypeListsMembership.Targets.allMembers (types.subst ts) (allowed.subst ts)) =
    (SourceComputabilityFormulaSupportProof.existsOne (lengthMatrix (types.subst ts) (bound.subst ts)) ⊓
    Continuation20261115.OriginalTypeListsMembership.Targets.allMembers (types.subst ts) (allowed.subst ts))
  rw [existsSubst,liftedEmbedding]
  simp only [lengthMatrix,conjunctionSubst,lengthSubst,InternalLessThan.strictLess,orderSubst,sucSubst,
    liftSubst,Term.subst,Sum.elim_inr]

theorem allowedRename {beta : Type} (types allowed bound : OTerm alpha) (j : alpha → beta) :
    (Targets.typesAllowed types allowed bound).relabel j =
      Targets.typesAllowed (types.relabel j) (allowed.relabel j) (bound.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.typesAllowed types allowed bound).subst (fun a => emb (.var (j a))) = _
  rw [allowedSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedSyntaxProof
