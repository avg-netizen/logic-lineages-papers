module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalRawListRecursion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (graph2 InternalListCodec.consCode (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    graph2 drop (.var (.inr 3)) (count.relabel Sum.inl) (.var (.inr 2))).imp
      (graph2 drop (.var (.inr 3)) (suc (count.relabel Sum.inl)) (.var (.inr 0)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)

theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody graph2
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [programSubst,orderSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst,
    sucSubst,zSubst]

theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowBodyWitness (count gamma head tail out : OTerm alpha) :
    (rowBody count).subst
      (Sum.elim Term.var (fun i => emb (![gamma,head,tail,out] i))) =
      (graph2 InternalListCodec.consCode gamma head tail ⊓ graph2 drop out count tail).imp
        (graph2 drop out (suc count) gamma) := by
  have he : (Sum.elim Term.var (fun i => emb (![gamma,head,tail,out] i))) =
      (fun a => emb (Sum.elim Term.var ![gamma,head,tail,out] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody graph2
  rw [he,impSubst,conjunctionSubst]
  simp only [programSubst,orderSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst,
    sucSubst,zSubst]
  rfl

theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

theorem rowApply (count gamma head tail out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 drop out count tail))) :
    Nonempty (Derivation body Delta (graph2 drop out (suc count) gamma)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody count)
    (fun i => emb (![gamma,head,tail,out] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hc⟩ := hc
  obtain ⟨hd⟩ := hd
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hc hd)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropSyntaxProof
