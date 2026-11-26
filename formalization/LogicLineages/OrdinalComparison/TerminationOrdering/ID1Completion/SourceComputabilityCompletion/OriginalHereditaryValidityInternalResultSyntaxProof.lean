module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)

open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidity

def resultFields {alpha : Type} (state out parameter rest fn arg : InternalGraphComposition.OTerm alpha) : Formula alpha :=
  graph1 currentFunction fn state ⊓
    (graph1 currentArgument arg state ⊓ PushedApplication out fn arg parameter rest)

def resultMatrix {alpha : Type} (state out parameter rest : InternalGraphComposition.OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  resultFields (state.relabel Sum.inl) (out.relabel Sum.inl) (parameter.relabel Sum.inl)
    (rest.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))

theorem resultFieldsSubst {alpha beta : Type}
    (state out parameter rest fn arg : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (resultFields state out parameter rest fn arg).subst (fun a => emb (ts a)) =
      resultFields (state.subst ts) (out.subst ts) (parameter.subst ts)
        (rest.subst ts) (fn.subst ts) (arg.subst ts) := by
  simp only [resultFields,conjunctionSubst,graph1,programSubst,consTermSubst,emptySubst,
    pushedApplicationSubst]

theorem resultMatrixWitness {alpha : Type}
    (state out parameter rest fn arg : InternalGraphComposition.OTerm alpha) :
    (resultMatrix state out parameter rest).subst
      (Sum.elim Term.var (fun i => emb (![fn,arg] i))) =
      resultFields state out parameter rest fn arg := by
  unfold resultMatrix
  rw [witnessEmbedding,resultFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applicationResultIntro {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (state out parameter rest fn arg : InternalGraphComposition.OTerm alpha)
    (h : Nonempty (Derivation body Delta (resultFields state out parameter rest fn arg))) :
    Nonempty (Derivation body Delta (ApplicationResult state out parameter rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta (resultMatrix state out parameter rest)
    (fun i => emb (![fn,arg] i))
  rw [resultMatrixWitness]
  exact h

theorem applicationResultCases {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (state out parameter rest : InternalGraphComposition.OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (ApplicationResult state out parameter rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (fn arg : InternalGraphComposition.OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (resultFields (state.relabel j) (out.relabel j)
        (parameter.relabel j) (rest.relabel j) fn arg)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (resultMatrix state out parameter rest) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (resultMatrix state out parameter rest :: Delta.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem applicationResultSubst {alpha beta : Type}
    (state out parameter rest : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (ApplicationResult state out parameter rest).subst (fun a => emb (ts a)) =
      ApplicationResult (state.subst ts) (out.subst ts) (parameter.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (resultMatrix state out parameter rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold resultMatrix
  simp only [resultFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem applicationResultRename {alpha beta : Type}
    (state out parameter rest : InternalGraphComposition.OTerm alpha) (j : alpha → beta) :
    (ApplicationResult state out parameter rest).relabel j =
      ApplicationResult (state.relabel j) (out.relabel j) (parameter.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ApplicationResult state out parameter rest).subst (fun a => emb (.var (j a))) = _
  rw [applicationResultSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultSyntaxProof
