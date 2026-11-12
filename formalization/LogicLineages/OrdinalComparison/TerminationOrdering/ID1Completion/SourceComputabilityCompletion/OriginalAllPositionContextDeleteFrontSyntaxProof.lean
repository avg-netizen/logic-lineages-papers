module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontSyntaxProof
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
open OriginalClassContextAllPositionObserver
open InternalListCodecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rowBody (count : InternalGraphComposition.OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (graph2 front (.var (.inr 3)) (count.relabel Sum.inl) (.var (.inr 2)) ⊓
     consGraph (.var (.inr 4)) (.var (.inr 1)) (.var (.inr 3)))).imp
    (graph2 front (.var (.inr 4)) (suc (count.relabel Sum.inl)) (.var (.inr 0)))
def row (count : InternalGraphComposition.OTerm alpha) : Formula alpha := allBlock (rowBody count)

theorem rowSubst {beta : Type} (count : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody graph2 consGraph
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [conjunctionSubst,programSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst,sucSubst]

theorem rowRename {beta : Type} (count : InternalGraphComposition.OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowBodyWitness (count gamma head tail previous out : InternalGraphComposition.OTerm alpha) :
    (rowBody count).subst
      (Sum.elim Term.var (fun i => emb (![gamma,head,tail,previous,out] i))) =
      (consGraph gamma head tail ⊓
        (graph2 front previous count tail ⊓ consGraph out head previous)).imp
        (graph2 front out (suc count) gamma) := by
  have he : (Sum.elim Term.var (fun i => emb (![gamma,head,tail,previous,out] i))) =
      (fun a => emb (Sum.elim Term.var ![gamma,head,tail,previous,out] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody graph2 consGraph
  rw [he,impSubst]
  simp only [conjunctionSubst,programSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst,sucSubst]
  rfl

theorem rowInstantiate (count : InternalGraphComposition.OTerm (alpha ⊕ Fin 1)) (t : InternalGraphComposition.OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : InternalGraphComposition.OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

theorem rowApply (count gamma head tail previous out : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front previous count tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head previous))) :
    Nonempty (Derivation body Delta (graph2 front out (suc count) gamma)) := by
  have h := actualFiniteUniversalElimination body alpha 5 Delta (rowBody count)
    (fun i => emb (![gamma,head,tail,previous,out] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hc⟩ := hc
  obtain ⟨hp⟩ := hp
  obtain ⟨ho⟩ := ho
  exact ⟨Derivation.implicationElimination h
    (Derivation.conjunctionIntroduction hc (Derivation.conjunctionIntroduction hp ho))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontSyntaxProof
