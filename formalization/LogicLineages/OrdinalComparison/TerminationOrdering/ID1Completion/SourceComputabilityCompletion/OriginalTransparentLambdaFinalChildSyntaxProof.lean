module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb sucSubst zSubst)
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalTransparentLambdaFinal
open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidityInternalExtensionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def childFields {alpha : Type} (valid : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha) : Formula alpha :=
  graph2 initial state raw parameter ⊓
    ((graph1 currentBody child state ⊓ ExtendedParameter raw parameter childParameterCode) ⊓
      (graph1 childParameter childParameterCode state ⊓
        graph2 valid (numeral 1) child childParameterCode))

def childMatrix {alpha : Type} (valid : Program 2)
    (raw parameter : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  childFields valid (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem childFieldsSubst {alpha beta : Type} (valid : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (childFields valid raw parameter state child childParameterCode).subst (fun a => emb (ts a)) =
      childFields valid (raw.subst ts) (parameter.subst ts) (state.subst ts)
        (child.subst ts) (childParameterCode.subst ts) := by
  simp only [childFields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,
    emptySubst,extendedParameterSubst,numeral,sucSubst,zSubst]

theorem childMatrixWitness {alpha : Type} (valid : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha) :
    (childMatrix valid raw parameter).subst
      (Sum.elim Term.var (fun i => emb (![state,child,childParameterCode] i))) =
      childFields valid raw parameter state child childParameterCode := by
  unfold childMatrix
  rw [witnessEmbedding,childFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem finalChildSubst {alpha beta : Type} (valid : Program 2)
    (raw parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (FinalLambdaChild valid raw parameter).subst (fun a => emb (ts a)) =
      FinalLambdaChild valid (raw.subst ts) (parameter.subst ts) := by
  change (InternalFiniteBlocks.block (childMatrix valid raw parameter)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold childMatrix
  simp only [childFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem finalChildRename {alpha beta : Type} (valid : Program 2)
    (raw parameter : OTerm alpha) (j : alpha → beta) :
    (FinalLambdaChild valid raw parameter).relabel j =
      FinalLambdaChild valid (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (FinalLambdaChild valid raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [finalChildSubst]
  simp only [← termRelabelAsSubst]

theorem finalChildIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (valid : Program 2) (raw parameter state child childParameterCode : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (childFields valid raw parameter state child childParameterCode))) :
    Nonempty (Derivation body Gamma (FinalLambdaChild valid raw parameter)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 3 Gamma (childMatrix valid raw parameter)
    (fun i => emb (![state,child,childParameterCode] i))
  rw [childMatrixWitness]
  exact h

theorem finalChildCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (valid : Program 2) (raw parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (FinalLambdaChild valid raw parameter)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (state child childParameterCode : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (childFields valid (raw.relabel j) (parameter.relabel j)
        state child childParameterCode)) → Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Gamma (childMatrix valid raw parameter) psi h
  apply step (alpha ⊕ Fin 3) Sum.inl
    (childMatrix valid raw parameter :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSyntaxProof
