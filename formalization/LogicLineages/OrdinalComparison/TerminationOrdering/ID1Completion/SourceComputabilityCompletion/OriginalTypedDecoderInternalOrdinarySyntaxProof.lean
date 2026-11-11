module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinarySyntaxProof
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


def stepOrdinaryFields (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ys : Fin 5 → OTerm alpha) : Formula alpha :=
  StepPair payload (ys 0) (ys 1) ⊓
    (programGraph H (ys 2) ![ys 0] ⊓
      (StepArrowFields (ys 2) (ys 3) (ys 4) ⊓
        (((equal (ys 2) (numeral 0)).not ⊓
            (equal (ys 3) typ ⊓ StepPushOne out (numeral 1) gamma (ys 4) (ys 1) rest)) ⊔
          ((equal (ys 2) (numeral 0) ⊔ (equal (ys 3) typ).not) ⊓ equal out (numeral 0)))))

def stepOrdinaryMatrix (H : Program 1) (out gamma typ payload rest : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  stepOrdinaryFields H (out.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (payload.relabel Sum.inl) (rest.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepOrdinaryFieldsSubst {beta : Type} (H : Program 1) (out gamma typ payload rest : OTerm alpha)
    (ys : Fin 5 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepOrdinaryFields H out gamma typ payload rest ys).subst (fun a => emb (ts a)) =
      stepOrdinaryFields H (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepOrdinaryFields,conjunctionSubst,stepPairSubst,stepArrowFieldsSubst,stepConsSubst,stepPushOneSubst,stepPushTwoSubst,stepBinaryPayloadSubst,stepNumberedPayloadSubst,programSubst,Matrix.vecCons,Matrix.vecEmpty,consTermSubst,emptySubst,orSubst,notSubst,equalSubst,numeralSubst]

theorem stepOrdinaryMatrixWitness (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ys : Fin 5 → OTerm alpha) :
    (stepOrdinaryMatrix H out gamma typ payload rest).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepOrdinaryFields H out gamma typ payload rest ys := by
  unfold stepOrdinaryMatrix
  rw [witnessEmbedding,stepOrdinaryFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepOrdinaryIntro (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepOrdinaryFields H out gamma typ payload rest ys))) :
    Nonempty (Derivation body Delta (StepOrdinary H out gamma typ payload rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 5 Delta
    (stepOrdinaryMatrix H out gamma typ payload rest) (fun i => emb (ys i))
  rw [stepOrdinaryMatrixWitness]
  exact h

theorem stepOrdinaryCases (H : Program 1) (out gamma typ payload rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepOrdinary H out gamma typ payload rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 5 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepOrdinaryFields H (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 5 Delta (stepOrdinaryMatrix H out gamma typ payload rest) psi h
  apply step (alpha ⊕ Fin 5) Sum.inl
    (stepOrdinaryMatrix H out gamma typ payload rest :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepOrdinarySubst {beta : Type} (H : Program 1) (out gamma typ payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepOrdinary H out gamma typ payload rest).subst (fun a => emb (ts a)) = StepOrdinary H (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (stepOrdinaryMatrix H out gamma typ payload rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepOrdinaryMatrix
  simp only [stepOrdinaryFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepOrdinaryRename {beta : Type} (H : Program 1) (out gamma typ payload rest : OTerm alpha) (j : alpha → beta) :
    (StepOrdinary H out gamma typ payload rest).relabel j = StepOrdinary H (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepOrdinary H out gamma typ payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepOrdinarySubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinarySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinarySyntaxProof
