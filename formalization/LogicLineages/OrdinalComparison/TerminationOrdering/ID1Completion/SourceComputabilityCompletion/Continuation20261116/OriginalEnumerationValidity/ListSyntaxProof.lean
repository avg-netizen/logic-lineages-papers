module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnSubst zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof InternalStrongInductionSyntaxProof
open InternalApplicationResultStackCompositionSyntaxProof (graph1Subst)
open InternalApplicationValidityStackAppendSyntaxProof (graph2Subst)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115 Lists
variable {alpha : Type}
theorem allSubst {beta : Type} (n : Nat) (list : OTerm alpha) (ts : alpha → OTerm beta) :
    (AllValid n list).subst (fun a => emb (ts a)) = AllValid n (list.subst ts) := by
  unfold AllValid matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1Subst,graph2Subst,numeral,zSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem allRename {beta : Type} (n : Nat) (list : OTerm alpha) (j : alpha → beta) :
    (AllValid n list).relabel j = AllValid n (list.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AllValid n list).subst (fun a => emb (.var (j a))) = _
  rw [allSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (list raw : OTerm alpha) :
    (matrix n list).subst (Sum.elim Term.var (fun _ : Fin 1 => emb raw)) =
      (graph2 contains (numeral 1) list raw).imp
        (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb raw)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => raw) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,graph1Subst,graph2Subst,numeral,zSubst,sucSubst,witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListSyntaxProof
