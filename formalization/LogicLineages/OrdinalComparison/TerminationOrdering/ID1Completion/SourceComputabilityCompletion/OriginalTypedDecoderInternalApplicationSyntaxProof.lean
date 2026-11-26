module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalBinarySyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open InternalOriginalOrderSyntaxProof (notSubst)


def stepApplicationFields ( out gamma typ payload rest : OTerm alpha) (ys : Fin 4 → OTerm alpha) : Formula alpha :=
  StepBinaryPayload payload (ys 0) (ys 1) (ys 2) ⊓
    (StepCons (ys 3) (ys 0) typ ⊓
      StepPushTwo out (numeral 0) gamma (ys 3) (ys 1)
        (numeral 0) gamma (ys 0) (ys 2) rest)

def stepApplicationMatrix (out gamma typ payload rest : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  stepApplicationFields (out.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (payload.relabel Sum.inl) (rest.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepApplicationFieldsSubst {beta : Type} (out gamma typ payload rest : OTerm alpha)
    (ys : Fin 4 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepApplicationFields out gamma typ payload rest ys).subst (fun a => emb (ts a)) =
      stepApplicationFields (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepApplicationFields,conjunctionSubst,stepPairSubst,stepArrowFieldsSubst,stepConsSubst,stepPushOneSubst,stepPushTwoSubst,stepBinaryPayloadSubst,orSubst,notSubst,equalSubst,numeralSubst]

theorem stepApplicationMatrixWitness (out gamma typ payload rest : OTerm alpha) (ys : Fin 4 → OTerm alpha) :
    (stepApplicationMatrix out gamma typ payload rest).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepApplicationFields out gamma typ payload rest ys := by
  unfold stepApplicationMatrix
  rw [witnessEmbedding,stepApplicationFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepApplicationIntro (out gamma typ payload rest : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepApplicationFields out gamma typ payload rest ys))) :
    Nonempty (Derivation body Delta (StepApplication out gamma typ payload rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 4 Delta
    (stepApplicationMatrix out gamma typ payload rest) (fun i => emb (ys i))
  rw [stepApplicationMatrixWitness]
  exact h

theorem stepApplicationCases (out gamma typ payload rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepApplication out gamma typ payload rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 4 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepApplicationFields (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 4 Delta (stepApplicationMatrix out gamma typ payload rest) psi h
  apply step (alpha ⊕ Fin 4) Sum.inl
    (stepApplicationMatrix out gamma typ payload rest :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepApplicationSubst {beta : Type} (out gamma typ payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepApplication out gamma typ payload rest).subst (fun a => emb (ts a)) = StepApplication (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (stepApplicationMatrix out gamma typ payload rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepApplicationMatrix
  simp only [stepApplicationFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepApplicationRename {beta : Type} (out gamma typ payload rest : OTerm alpha) (j : alpha → beta) :
    (StepApplication out gamma typ payload rest).relabel j = StepApplication (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepApplication out gamma typ payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepApplicationSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationSyntaxProof
