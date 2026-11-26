module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaSyntaxProof
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
open OriginalHereditaryValidityInternalExtensionProof

def lambdaFields {alpha : Type} (state out raw parameter rest child childParameterCode : InternalGraphComposition.OTerm alpha) : Formula alpha :=
  graph1 currentBody child state ⊓
    (ExtendedParameter raw parameter childParameterCode ⊓
      (graph1 childParameter childParameterCode state ⊓ PushedFrame out child childParameterCode rest))

def lambdaMatrix {alpha : Type} (state out raw parameter rest : InternalGraphComposition.OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  lambdaFields (state.relabel Sum.inl) (out.relabel Sum.inl) (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
    (rest.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))

theorem lambdaFieldsSubst {alpha beta : Type}
    (state out raw parameter rest child childParameterCode : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (lambdaFields state out raw parameter rest child childParameterCode).subst (fun a => emb (ts a)) =
      lambdaFields (state.subst ts) (out.subst ts) (raw.subst ts) (parameter.subst ts)
        (rest.subst ts) (child.subst ts) (childParameterCode.subst ts) := by
  simp only [lambdaFields,conjunctionSubst,graph1,programSubst,consTermSubst,emptySubst,
    pushedFrameSubst,extendedParameterSubst]

theorem lambdaMatrixWitness {alpha : Type}
    (state out raw parameter rest child childParameterCode : InternalGraphComposition.OTerm alpha) :
    (lambdaMatrix state out raw parameter rest).subst
      (Sum.elim Term.var (fun i => emb (![child,childParameterCode] i))) =
      lambdaFields state out raw parameter rest child childParameterCode := by
  unfold lambdaMatrix
  rw [witnessEmbedding,lambdaFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem lambdaResultIntro {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (state out raw parameter rest child childParameterCode : InternalGraphComposition.OTerm alpha)
    (h : Nonempty (Derivation body Delta (lambdaFields state out raw parameter rest child childParameterCode))) :
    Nonempty (Derivation body Delta (LambdaResult state out raw parameter rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta (lambdaMatrix state out raw parameter rest)
    (fun i => emb (![child,childParameterCode] i))
  rw [lambdaMatrixWitness]
  exact h

theorem lambdaResultCases {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (state out raw parameter rest : InternalGraphComposition.OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (LambdaResult state out raw parameter rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (child childParameterCode : InternalGraphComposition.OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (lambdaFields (state.relabel j) (out.relabel j) (raw.relabel j)
        (parameter.relabel j) (rest.relabel j) child childParameterCode)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (lambdaMatrix state out raw parameter rest) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (lambdaMatrix state out raw parameter rest :: Delta.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem lambdaResultSubst {alpha beta : Type}
    (state out raw parameter rest : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (LambdaResult state out raw parameter rest).subst (fun a => emb (ts a)) =
      LambdaResult (state.subst ts) (out.subst ts) (raw.subst ts) (parameter.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (lambdaMatrix state out raw parameter rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold lambdaMatrix
  simp only [lambdaFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem lambdaResultRename {alpha beta : Type}
    (state out raw parameter rest : InternalGraphComposition.OTerm alpha) (j : alpha → beta) :
    (LambdaResult state out raw parameter rest).relabel j =
      LambdaResult (state.relabel j) (out.relabel j) (raw.relabel j) (parameter.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (LambdaResult state out raw parameter rest).subst (fun a => emb (.var (j a))) = _
  rw [lambdaResultSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaSyntaxProof
