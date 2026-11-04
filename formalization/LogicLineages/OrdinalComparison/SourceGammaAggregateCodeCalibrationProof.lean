module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodeSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode.Proof
open SourceCollisionCompletion SourceAggregateCompletion

theorem eraser_correct {Γ} (p q : OriginalTerm Γ .ground) :
    eraserCode (SyntaxCode.encodeTerm p) (SyntaxCode.encodeTerm q)=SyntaxCode.encodeTerm (eraser p q) := by
  have h := ContextInsertionCode.Proof.exactSourceInsertion [] [.ground] Γ .ground p
  change ContextInsertionCode.sourceCode 0 1 (SyntaxCode.encodeTerm p)=
    SyntaxCode.encodeTerm (p.rename (Renaming.weaken Γ .ground)) at h
  unfold eraserCode
  rw [h]
  rfl

theorem exactLiteralCodes : Targets.ExactLiteralCodes := by
  intro Γ p q
  refine ⟨eraser_correct p q,?_,?_⟩
  · unfold leftCode
    rw [eraser_correct,eraser_correct,eraser_correct]
    rfl
  · unfold rightCode
    rw [eraser_correct,eraser_correct,eraser_correct]
    rfl

theorem exactAggregateCode : Targets.ExactAggregateCode := by
  intro Γ es
  induction es with
  | nil => rfl
  | cons e es ih =>
    change step (pairCode e) (aggregateCode (es.map pairCode))=pairCode (aggregate (e::es))
    rw [ih]
    simp only [step,pairCode,aggregate]
    rw [(exactLiteralCodes Γ e.1 e.2).2.1,(exactLiteralCodes Γ e.1 e.2).2.2,
      eraser_correct,eraser_correct]
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode.Proof
