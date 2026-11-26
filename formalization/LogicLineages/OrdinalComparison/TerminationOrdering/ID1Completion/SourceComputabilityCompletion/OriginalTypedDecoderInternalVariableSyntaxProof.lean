module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalOriginalOrderSyntaxProof (notSubst)
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def stepVariableFields (out gamma typ index rest value : OTerm alpha) : Formula alpha :=
  OriginalVariableDecoder.graph value typ index gamma ⊓
    ((equal value (numeral 1) ⊓ StepLive out rest) ⊔
      ((equal value (numeral 1)).not ⊓ equal out (numeral 0)))

def stepVariableMatrix (out gamma typ index rest : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  stepVariableFields (out.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl)
    (index.relabel Sum.inl) (rest.relabel Sum.inl) (.var (.inr 0))

theorem stepVariableFieldsSubst {beta : Type}
    (out gamma typ index rest value : OTerm alpha) (ts : alpha → OTerm beta) :
    (stepVariableFields out gamma typ index rest value).subst (fun a => emb (ts a)) =
      stepVariableFields (out.subst ts) (gamma.subst ts) (typ.subst ts)
        (index.subst ts) (rest.subst ts) (value.subst ts) := by
  simp only [stepVariableFields,OriginalVariableDecoder.graph,programSubst,consTermSubst,
    emptySubst,conjunctionSubst,orSubst,notSubst,equalSubst,numeralSubst,stepLiveSubst]

theorem stepVariableSubst {beta : Type}
    (out gamma typ index rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepVariable out gamma typ index rest).subst (fun a => emb (ts a)) =
      StepVariable (out.subst ts) (gamma.subst ts) (typ.subst ts) (index.subst ts) (rest.subst ts) := by
  change (existsOne (stepVariableMatrix out gamma typ index rest)).subst _ = _
  rw [existsSubst,liftedEmbedding]
  unfold stepVariableMatrix
  simp only [stepVariableFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepVariableRename {beta : Type}
    (out gamma typ index rest : OTerm alpha) (j : alpha → beta) :
    (StepVariable out gamma typ index rest).relabel j =
      StepVariable (out.relabel j) (gamma.relabel j) (typ.relabel j) (index.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepVariable out gamma typ index rest).subst (fun a => emb (.var (j a))) = _
  rw [stepVariableSubst]
  simp only [← termRelabelAsSubst]

theorem stepVariableInstantiate (out gamma typ index rest value : OTerm alpha) :
    instantiate (stepVariableMatrix out gamma typ index rest) (emb value) =
      stepVariableFields out gamma typ index rest value := by
  rw [instantiate,bindEmbedding]
  unfold stepVariableMatrix
  rw [stepVariableFieldsSubst]
  simp only [varBind,liftBind]

theorem stepVariableIntro (out gamma typ index rest value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepVariableFields out gamma typ index rest value))) :
    Nonempty (Derivation body Delta (StepVariable out gamma typ index rest)) := by
  change Nonempty (Derivation body Delta (existsOne (stepVariableMatrix out gamma typ index rest)))
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb value)
  rw [stepVariableInstantiate]
  exact h

theorem stepVariableCases (out gamma typ index rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepVariable out gamma typ index rest)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (value : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (stepVariableFields (out.relabel j) (gamma.relabel j) (typ.relabel j)
          (index.relabel j) (rest.relabel j) value)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  let P := stepVariableMatrix out gamma typ index rest
  let Theta := P :: Delta.map weaken
  obtain ⟨d⟩ := k (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
