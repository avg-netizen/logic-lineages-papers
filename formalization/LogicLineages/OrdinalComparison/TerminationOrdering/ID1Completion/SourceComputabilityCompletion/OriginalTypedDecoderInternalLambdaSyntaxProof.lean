module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaSyntaxProof
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


def stepLambdaFields ( out gamma typ payload rest : OTerm alpha) (ys : Fin 5 → OTerm alpha) : Formula alpha :=
  StepPair payload (ys 0) (ys 1) ⊓
    (StepArrowFields typ (ys 2) (ys 3) ⊓
      (StepCons (ys 4) (ys 0) gamma ⊓
        (((equal typ (numeral 0)).not ⊓
            (equal (ys 2) (ys 0) ⊓ StepPushOne out (numeral 0) (ys 4) (ys 3) (ys 1) rest)) ⊔
          ((equal typ (numeral 0) ⊔ (equal (ys 2) (ys 0)).not) ⊓ equal out (numeral 0)))))

def stepLambdaMatrix (out gamma typ payload rest : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  stepLambdaFields (out.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (payload.relabel Sum.inl) (rest.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepLambdaFieldsSubst {beta : Type} (out gamma typ payload rest : OTerm alpha)
    (ys : Fin 5 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepLambdaFields out gamma typ payload rest ys).subst (fun a => emb (ts a)) =
      stepLambdaFields (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepLambdaFields,conjunctionSubst,stepPairSubst,stepArrowFieldsSubst,stepConsSubst,stepPushOneSubst,stepPushTwoSubst,stepBinaryPayloadSubst,orSubst,notSubst,equalSubst,numeralSubst]

theorem stepLambdaMatrixWitness (out gamma typ payload rest : OTerm alpha) (ys : Fin 5 → OTerm alpha) :
    (stepLambdaMatrix out gamma typ payload rest).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepLambdaFields out gamma typ payload rest ys := by
  unfold stepLambdaMatrix
  rw [witnessEmbedding,stepLambdaFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepLambdaIntro (out gamma typ payload rest : OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepLambdaFields out gamma typ payload rest ys))) :
    Nonempty (Derivation body Delta (StepLambda out gamma typ payload rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 5 Delta
    (stepLambdaMatrix out gamma typ payload rest) (fun i => emb (ys i))
  rw [stepLambdaMatrixWitness]
  exact h

theorem stepLambdaCases (out gamma typ payload rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepLambda out gamma typ payload rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 5 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepLambdaFields (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 5 Delta (stepLambdaMatrix out gamma typ payload rest) psi h
  apply step (alpha ⊕ Fin 5) Sum.inl
    (stepLambdaMatrix out gamma typ payload rest :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepLambdaSubst {beta : Type} (out gamma typ payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepLambda out gamma typ payload rest).subst (fun a => emb (ts a)) = StepLambda (out.subst ts) (gamma.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (stepLambdaMatrix out gamma typ payload rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepLambdaMatrix
  simp only [stepLambdaFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepLambdaRename {beta : Type} (out gamma typ payload rest : OTerm alpha) (j : alpha → beta) :
    (StepLambda out gamma typ payload rest).relabel j = StepLambda (out.relabel j) (gamma.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepLambda out gamma typ payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepLambdaSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaSyntaxProof
