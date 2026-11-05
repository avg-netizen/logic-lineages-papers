module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceExtractionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceProof
open LiteralFiniteSource Source Source.ForwardTranslation

private theorem compiled_scalar {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c) :
    compileScalar (v 0) = some c.scalar := by
  obtain ⟨s, hs, p, hp, he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, AdmissibleAssignment.collect n (fun j => extractPositive (v j.succ)) = some p ∧
        CompiledVector.mk s p = c := by
    simpa only [compileVector, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] using hc
  subst c
  exact hs

theorem canonicalSourceCorrespondence : LiteralFiniteSourceTargets.CanonicalSourceCorrespondence := by
  intro Γ hΓ τ e
  constructor
  · rintro ⟨v, hv, hf⟩ w hw s hs
    have heq : w = v := Option.some.inj (hw.symm.trans hv)
    subst w
    exact (literalScalarCorrespondence Γ (v 0) s hs).mp hf
  · intro hf
    obtain ⟨v, hv, c, hc, _⟩ :=
      actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy e
    have hs := compiled_scalar v c hc
    exact ⟨v, hv, (literalScalarCorrespondence Γ (v 0) c.scalar hs).mpr
      (hf v hv c.scalar hs)⟩

theorem exactSourceTest : LiteralFiniteSourceTargets.ExactSourceTest := by
  intro Γ hΓ τ e
  obtain ⟨v, hv, c, hc, _⟩ :=
    actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy e
  have hs := compiled_scalar v c hc
  have hsource : finiteSource e ↔ finiteCollapseCoefficients (v 0) := by
    constructor
    · rintro ⟨w, hw, hf⟩
      have heq : w = v := Option.some.inj (hw.symm.trans hv)
      subst w
      exact hf
    · exact fun hf => ⟨v, hv, hf⟩
  rw [hsource, literalScalarCorrespondence Γ (v 0) c.scalar hs]
  unfold LiteralFiniteSource.Code.acceptsSource
  rw [GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ e v c hv hc]
  simp only [Option.bind_some]
  change (SemanticFiniteScalar.Code.compile
    (scalarSyntaxCode FiniteCoefficientBase.rawIndex c.scalar)).isSome = true ↔ _
  rw [SemanticFiniteScalarProof.literalNumericCalibration, Option.isSome_map]
  simpa only [Option.isSome_iff_exists] using
    SemanticFiniteScalarProof.exactSuccessClass (OrdinalComponent Γ)
      FiniteCoefficientBase.rawIndex c.scalar

theorem actualSourceDecision : LiteralFiniteSourceTargets.ActualSourceDecision := by
  intro Γ hΓ τ a b ha hb mode
  exact SemanticFiniteVectorProof.actualSourceDecision Γ hΓ τ a b
    ((canonicalSourceCorrespondence Γ hΓ τ a).mp ha)
    ((canonicalSourceCorrespondence Γ hΓ τ b).mp hb) mode

theorem recursorFreePasses : LiteralFiniteSourceTargets.RecursorFreePasses := by
  intro Γ hΓ τ e he
  have hf : finiteSource e := (canonicalSourceCorrespondence Γ hΓ τ e).mpr
    (SemanticFiniteVectorProof.recursorFreePasses Γ hΓ τ e he)
  exact ⟨hf, (exactSourceTest Γ hΓ τ e).mpr hf⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceProof
