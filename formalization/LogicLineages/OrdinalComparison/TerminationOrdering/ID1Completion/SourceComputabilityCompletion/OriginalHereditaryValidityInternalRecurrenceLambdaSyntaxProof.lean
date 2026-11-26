module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
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
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidityInternalExtensionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def lambdaFields {alpha : Type} (s t m : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha) : Formula alpha :=
  graph2 initial state raw parameter ⊓
    ((graph1 currentBody child state ⊓ ExtendedParameter raw parameter childParameterCode) ⊓
      (graph1 childParameter childParameterCode state ⊓
        graph2 (validator s t m) (numeral 1) child childParameterCode))

def lambdaMatrix {alpha : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  lambdaFields s t m (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem lambdaFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (lambdaFields s t m raw parameter state child childParameterCode).subst (fun a => emb (ts a)) =
      lambdaFields s t m (raw.subst ts) (parameter.subst ts) (state.subst ts)
        (child.subst ts) (childParameterCode.subst ts) := by
  simp only [lambdaFields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,
    emptySubst,extendedParameterSubst,numeral,sucSubst,zSubst]

theorem lambdaMatrixWitness {alpha : Type} (s t m : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha) :
    (lambdaMatrix s t m raw parameter).subst
      (Sum.elim Term.var (fun i => emb (![state,child,childParameterCode] i))) =
      lambdaFields s t m raw parameter state child childParameterCode := by
  unfold lambdaMatrix
  rw [witnessEmbedding,lambdaFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rootLambdaSubst {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (RootLambdaChild s t m raw parameter).subst (fun a => emb (ts a)) =
      RootLambdaChild s t m (raw.subst ts) (parameter.subst ts) := by
  change (InternalFiniteBlocks.block (lambdaMatrix s t m raw parameter)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold lambdaMatrix
  simp only [lambdaFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem rootLambdaRename {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (j : alpha → beta) :
    (RootLambdaChild s t m raw parameter).relabel j =
      RootLambdaChild s t m (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (RootLambdaChild s t m raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [rootLambdaSubst]
  simp only [← termRelabelAsSubst]

theorem rootLambdaIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (s t m : Program 2) (raw parameter state child childParameterCode : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (lambdaFields s t m raw parameter state child childParameterCode))) :
    Nonempty (Derivation body Gamma (RootLambdaChild s t m raw parameter)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 3 Gamma (lambdaMatrix s t m raw parameter)
    (fun i => emb (![state,child,childParameterCode] i))
  rw [lambdaMatrixWitness]
  exact h

theorem rootLambdaCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (s t m : Program 2) (raw parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (RootLambdaChild s t m raw parameter)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (state child childParameterCode : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (lambdaFields s t m (raw.relabel j) (parameter.relabel j)
        state child childParameterCode)) → Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Gamma (lambdaMatrix s t m raw parameter) psi h
  apply step (alpha ⊕ Fin 3) Sum.inl
    (lambdaMatrix s t m raw parameter :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
