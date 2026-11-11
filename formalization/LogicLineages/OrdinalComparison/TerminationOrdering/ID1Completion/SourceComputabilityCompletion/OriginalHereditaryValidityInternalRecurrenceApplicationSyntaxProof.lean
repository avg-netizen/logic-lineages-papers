module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
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

def applicationFields {alpha : Type} (s t m : Program 2)
    (raw parameter state fn arg : OTerm alpha) : Formula alpha :=
  graph2 initial state raw parameter ⊓
    (graph1 currentFunction fn state ⊓
      ((graph1 currentArgument arg state ⊓ graph2 (validator s t m) (numeral 1) fn parameter) ⊓
        graph2 (validator s t m) (numeral 1) arg parameter))

def applicationMatrix {alpha : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  applicationFields s t m (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem applicationFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (raw parameter state fn arg : OTerm alpha) (ts : alpha → OTerm beta) :
    (applicationFields s t m raw parameter state fn arg).subst (fun a => emb (ts a)) =
      applicationFields s t m (raw.subst ts) (parameter.subst ts) (state.subst ts)
        (fn.subst ts) (arg.subst ts) := by
  simp only [applicationFields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,
    emptySubst,extendedParameterSubst,numeral,sucSubst,zSubst]

theorem applicationMatrixWitness {alpha : Type} (s t m : Program 2)
    (raw parameter state fn arg : OTerm alpha) :
    (applicationMatrix s t m raw parameter).subst
      (Sum.elim Term.var (fun i => emb (![state,fn,arg] i))) =
      applicationFields s t m raw parameter state fn arg := by
  unfold applicationMatrix
  rw [witnessEmbedding,applicationFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rootApplicationSubst {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (RootApplicationChildren s t m raw parameter).subst (fun a => emb (ts a)) =
      RootApplicationChildren s t m (raw.subst ts) (parameter.subst ts) := by
  change (InternalFiniteBlocks.block (applicationMatrix s t m raw parameter)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold applicationMatrix
  simp only [applicationFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem rootApplicationRename {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (j : alpha → beta) :
    (RootApplicationChildren s t m raw parameter).relabel j =
      RootApplicationChildren s t m (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (RootApplicationChildren s t m raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [rootApplicationSubst]
  simp only [← termRelabelAsSubst]

theorem rootApplicationIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (s t m : Program 2) (raw parameter state fn arg : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (applicationFields s t m raw parameter state fn arg))) :
    Nonempty (Derivation body Gamma (RootApplicationChildren s t m raw parameter)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 3 Gamma (applicationMatrix s t m raw parameter)
    (fun i => emb (![state,fn,arg] i))
  rw [applicationMatrixWitness]
  exact h

theorem rootApplicationCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (s t m : Program 2) (raw parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (RootApplicationChildren s t m raw parameter)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (state fn arg : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (applicationFields s t m (raw.relabel j) (parameter.relabel j)
        state fn arg)) → Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Gamma (applicationMatrix s t m raw parameter) psi h
  apply step (alpha ⊕ Fin 3) Sum.inl
    (applicationMatrix s t m raw parameter :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
