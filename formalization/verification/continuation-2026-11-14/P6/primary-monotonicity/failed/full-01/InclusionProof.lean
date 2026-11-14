module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem includedSubst {alpha beta : Type} (left right : OrdinaryArithmetic.Term alpha)
    (ts : alpha → OrdinaryArithmetic.Term beta) :
    (included left right).subst (fun a => emb (ts a)) = included (left.subst ts) (right.subst ts) := by
  unfold included
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph2,programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem includedRename {alpha beta : Type} (left right : OrdinaryArithmetic.Term alpha)
    (j : alpha → beta) :
    (included left right).relabel j = included (left.relabel j) (right.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (included left right).subst (fun a => emb (.var (j a))) = _
  rw [includedSubst]
  simp only [← termRelabelAsSubst]

theorem eliminate {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (left right candidate : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) left candidate))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) right candidate)) := by
  obtain ⟨h⟩ := elimination body alpha 1 Delta _ (fun _ => emb candidate) hi
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb candidate)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => candidate) a)) := by
    funext a
    cases a <;> rfl
  rw [he] at h
  simp only [impSubst,graph2,programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr] at h
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h hm⟩

theorem introduce {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (left right : OrdinaryArithmetic.Term alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (candidate : OrdinaryArithmetic.Term beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 contains (numeral 1) (left.relabel j) candidate)) →
      Nonempty (Derivation body Theta (graph2 contains (numeral 1) (right.relabel j) candidate))) :
    Nonempty (Derivation body Delta (included left right)) := by
  apply introduction body alpha 1 Delta
  let candidate : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := graph2 contains (numeral 1) (left.relabel Sum.inl) candidate
  obtain ⟨h⟩ := next (alpha ⊕ Fin 1) Sum.inl
    (A :: Delta.map (fun q => q.relabel Sum.inl)) candidate
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
