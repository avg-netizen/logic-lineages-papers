module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWFiniteEnvelope
public import LogicLineages.ComputabilityKnowledge.FiniteDepthControlProof
public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeEffectivityProof

@[expose] public section

/-! Literal finite-name envelope transport after exact target freeze. The
existing source envelope and its actual uniform code program are unchanged. -/
namespace LogicLineages.ComputabilityKnowledge.WWFiniteEnvelopeProof

open PositiveExpression CircuitReduction WWFiniteEnvelope

theorem literalNarrowing : Comparators.WWFiniteEnvelope.LiteralNarrowing := by
  intro d e
  induction e with
  | one => intro h; rfl
  | var i => intro h; rfl
  | add a b ha hb => intro h; simp only [narrow, Expr.rename, ha h.1, hb h.2]
  | emul a b ha hb => intro h; simp only [narrow, Expr.rename, ha h.1, hb h.2]

theorem literalEnvelope : Comparators.WWFiniteEnvelope.LiteralEnvelope := by
  intro d e
  have h : (envelope d e).rename Fin.val = FiniteDepthEnvelope.envelope (e.rename Fin.val) :=
    literalNarrowing d _ _
  refine ⟨h, ?_⟩
  have hd := congrArg Expr.depth h
  rw [depth_rename] at hd
  exact hd.trans (FiniteDepthEnvelopeProof.literalAffineConstruction _).2.2.2.2.2.1

theorem sharedPositiveControl : Comparators.WWFiniteEnvelope.SharedPositiveControl := by
  intro d e he ρ
  let ρ' : Nat → PosNat := fun i => if hi : i < d then ρ ⟨i, hi⟩ else ⟨1, by decide⟩
  have hρ : ρ' ∘ Fin.val = ρ := by
    funext i
    simp only [Function.comp_apply, ρ', i.isLt, ↓reduceDIte]
  have hh := (FiniteDepthControlProof.finiteDepthControl (e.rename Fin.val)
    (by simpa only [depth_rename] using he)).2.2 ρ'
  have hg : (FiniteDepthEnvelope.envelope (e.rename Fin.val)).eval ρ' = (envelope d e).eval ρ := by
    rw [← (literalEnvelope d e).1, eval_rename, hρ]
  simpa only [eval_rename, hρ, hg] using hh

theorem actualEncodedConstruction : Comparators.WWFiniteEnvelope.ActualEncodedConstruction := by
  refine ⟨FiniteDepthEnvelopeEffectivityProof.finiteDepthEnvelopeEffectivity.1, ?_,
    FiniteDepthEnvelopeEffectivityProof.finiteDepthEnvelopeEffectivity.2.2.1⟩
  intro d e
  rw [(literalEnvelope d e).1]
  exact FiniteDepthEnvelopeEffectivityProof.finiteDepthEnvelopeEffectivity.2.1 d _
    (ExponentialNormalizerProgramSemantics.finite_rename_bounded d e)

theorem wwFiniteEnvelope : Comparators.WWFiniteEnvelope.Target :=
  ⟨literalNarrowing, literalEnvelope, sharedPositiveControl, actualEncodedConstruction⟩

end LogicLineages.ComputabilityKnowledge.WWFiniteEnvelopeProof
