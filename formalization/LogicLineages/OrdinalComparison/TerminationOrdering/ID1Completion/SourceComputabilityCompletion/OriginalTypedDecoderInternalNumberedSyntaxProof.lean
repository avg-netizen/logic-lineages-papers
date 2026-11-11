module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
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


def stepNumberedFields (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ys : Fin 9 → OTerm alpha) : Formula alpha :=
  StepNumberedPayload payload (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) ⊓
    (programGraph H (ys 6) ![ys 1] ⊓
      (StepArrowFields (ys 6) (ys 7) (ys 8) ⊓
        (((equal (ys 6) (numeral 0)).not ⊓
            (equal (ys 2) typ ⊓
              StepPushTwo out (numeral 1) gamma (ys 8) (ys 3)
                (numeral 1) gamma (ys 4) (ys 5) rest)) ⊔
          ((equal (ys 6) (numeral 0) ⊔ (equal (ys 2) typ).not) ⊓ equal out (numeral 0)))))

def stepNumberedMatrix (H : Program 1) (out gamma typ payload rest : OTerm alpha) : Formula (alpha ⊕ Fin 9) :=
  stepNumberedFields H (out.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (payload.relabel Sum.inl) (rest.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepNumberedFieldsSubst {beta : Type} (H : Program 1) (out gamma typ payload rest : OTerm alpha)
    (ys : Fin 9 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepNumberedFields H out gamma typ payload rest ys).subst (fun a => emb (ts a)) =
      stepNumberedFields H (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepNumberedFields,conjunctionSubst,stepPairSubst,stepArrowFieldsSubst,stepConsSubst,stepPushOneSubst,stepPushTwoSubst,stepBinaryPayloadSubst,stepNumberedPayloadSubst,programSubst,Matrix.vecCons,Matrix.vecEmpty,consTermSubst,emptySubst,orSubst,notSubst,equalSubst,numeralSubst]

theorem stepNumberedMatrixWitness (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ys : Fin 9 → OTerm alpha) :
    (stepNumberedMatrix H out gamma typ payload rest).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepNumberedFields H out gamma typ payload rest ys := by
  unfold stepNumberedMatrix
  rw [witnessEmbedding,stepNumberedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepNumberedIntro (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ys : Fin 9 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepNumberedFields H out gamma typ payload rest ys))) :
    Nonempty (Derivation body Delta (StepNumbered H out gamma typ payload rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 9 Delta
    (stepNumberedMatrix H out gamma typ payload rest) (fun i => emb (ys i))
  rw [stepNumberedMatrixWitness]
  exact h

theorem stepNumberedCases (H : Program 1) (out gamma typ payload rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepNumbered H out gamma typ payload rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 9 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepNumberedFields H (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 9 Delta (stepNumberedMatrix H out gamma typ payload rest) psi h
  apply step (alpha ⊕ Fin 9) Sum.inl
    (stepNumberedMatrix H out gamma typ payload rest :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepNumberedSubst {beta : Type} (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepNumbered H out gamma typ payload rest).subst (fun a => emb (ts a)) = StepNumbered H (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (stepNumberedMatrix H out gamma typ payload rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepNumberedMatrix
  simp only [stepNumberedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepNumberedRename {beta : Type} (H : Program 1) (out gamma typ payload rest : OTerm alpha) (j : alpha → beta) :
    (StepNumbered H out gamma typ payload rest).relabel j = StepNumbered H (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepNumbered H out gamma typ payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepNumberedSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
