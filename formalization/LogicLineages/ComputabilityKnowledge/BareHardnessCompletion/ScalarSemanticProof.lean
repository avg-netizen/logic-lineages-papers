module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
import LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparisonProof
import LogicLineages.ComputabilityKnowledge.WWGroundClassesProof
import LogicLineages.ComputabilityKnowledge.PositiveExpressionProperties
import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ScalarSemanticProof
open PositiveExpression CircuitReduction WWOrdinalTermSemantics WWGroundAdmissibility
open WWGroundClasses

theorem finite_rename_bounded (d : Nat) (a : Expr (Fin d)) :
    Bounded d (a.rename Fin.val) := by
  induction a with
  | one => trivial
  | var i => exact i.isLt
  | add a b ha hb => exact ⟨ha, hb⟩
  | emul a b ha hb => exact ⟨ha, hb⟩

theorem bounded_finite (d : Nat) (a : Expr Nat) (ha : Bounded d a) :
    ∃ b : Expr (Fin d), b.rename Fin.val = a := by
  induction a with
  | one => exact ⟨.one, rfl⟩
  | var i => exact ⟨.var ⟨i, ha⟩, rfl⟩
  | add a b ia ib =>
      obtain ⟨a', rfl⟩ := ia ha.1
      obtain ⟨b', rfl⟩ := ib ha.2
      exact ⟨.add a' b', rfl⟩
  | emul a b ia ib =>
      obtain ⟨a', rfl⟩ := ia ha.1
      obtain ⟨b', rfl⟩ := ib ha.2
      exact ⟨.emul a' b', rfl⟩

theorem rename_fin_injective (d : Nat) :
    Function.Injective (fun a : Expr (Fin d) => a.rename Fin.val) := by
  intro a
  induction a with
  | one =>
      intro b h
      cases b <;> simp_all [Expr.rename]
  | var i =>
      intro b h
      cases b with
      | one => cases h
      | var j => exact congrArg Expr.var (Fin.ext (Expr.var.inj h))
      | add a b => cases h
      | emul a b => cases h
  | add a b ha hb =>
      intro c h
      cases c with
      | one => cases h
      | var i => cases h
      | add c e =>
          have hh := Expr.add.inj h
          exact congrArg₂ Expr.add (ha hh.1) (hb hh.2)
      | emul c e => cases h
  | emul a b ha hb =>
      intro c h
      cases c with
      | one => cases h
      | var i => cases h
      | add c e => cases h
      | emul c e =>
          have hh := Expr.emul.inj h
          exact congrArg₂ Expr.emul (ha hh.1) (hb hh.2)

theorem typed_expression_code_injective {d : Nat} :
    Function.Injective (fun a : Expr (Fin d) => encodeExpr (a.rename Fin.val)) := by
  intro a b h
  change encodeExpr (a.rename Fin.val) = encodeExpr (b.rename Fin.val) at h
  have ha := (FiniteComparisonEnumerationProof.expressionDecoderExact d
    (encodeExpr (a.rename Fin.val)) (a.rename Fin.val)).mpr
      ⟨rfl, finite_rename_bounded d a⟩
  have hb := (FiniteComparisonEnumerationProof.expressionDecoderExact d
    (encodeExpr (b.rename Fin.val)) (b.rename Fin.val)).mpr
      ⟨rfl, finite_rename_bounded d b⟩
  rw [h] at ha
  exact rename_fin_injective d (Option.some.inj (ha.symm.trans hb))

theorem eval_finite_rename {d : Nat} (a : Expr (Fin d)) (ρ : Fin d → PosNat) :
    (a.rename Fin.val).eval (CircuitComparison.finiteVal ρ) = a.eval ρ := by
  rw [eval_rename]
  congr 1
  funext i
  simp [CircuitComparison.finiteVal, Function.comp_def, i.isLt]

theorem sourceOrder_iff {d : Nat} (norm weak : Bool) (a b : Expr (Fin d)) :
    SourceOrder norm weak a b ↔
      ∀ ρ : Fin d → PosNat, if weak then a.eval ρ ≤ b.eval ρ else a.eval ρ < b.eval ρ := by
  cases norm with
  | false => exact WWGroundAdmissibilityProof.sourceComparisons d a b weak
  | true => exact WWGroundAdmissibilityProof.sourceNormComparisons d a b weak

theorem scalarDomain_expressionCode {d : Nat} (a b : Expr (Fin d))
    (ha : a.depth ≤ 2) (hb : b.depth ≤ 2) : ScalarDomain (expressionCode a b) :=
  ⟨a, b, rfl, rfl, ha, hb⟩

theorem scalarComparison_expressionCode {d : Nat} (norm weak : Bool)
    (a b : Expr (Fin d)) (ha : a.depth ≤ 2) (hb : b.depth ≤ 2) :
    ScalarComparison norm weak (expressionCode a b) ↔ SourceOrder norm weak a b := by
  constructor
  · rintro ⟨a', b', hea, heb, _, _, horder⟩
    have ea : a = a' := typed_expression_code_injective hea
    have eb : b = b' := typed_expression_code_injective heb
    subst a'
    subst b'
    exact horder
  · intro horder
    exact ⟨a, b, rfl, rfl, ha, hb, horder⟩

theorem scalarDomain_bounded (d : Nat) (a b : Expr Nat)
    (ha : Bounded d a) (hb : Bounded d b) (hda : a.depth ≤ 2) (hdb : b.depth ≤ 2) :
    ScalarDomain (d, encodeExpr a, encodeExpr b) := by
  obtain ⟨a', hea⟩ := bounded_finite d a ha
  obtain ⟨b', heb⟩ := bounded_finite d b hb
  have ha' : a'.depth ≤ 2 := by simpa only [← hea, depth_rename] using hda
  have hb' : b'.depth ≤ 2 := by simpa only [← heb, depth_rename] using hdb
  exact ⟨a', b', congrArg encodeExpr hea.symm, congrArg encodeExpr heb.symm, ha', hb'⟩

theorem scalarComparison_bounded (d : Nat) (norm weak : Bool) (a b : Expr Nat)
    (ha : Bounded d a) (hb : Bounded d b) (hda : a.depth ≤ 2) (hdb : b.depth ≤ 2) :
    ScalarComparison norm weak (d, encodeExpr a, encodeExpr b) ↔
      ∀ ρ : Fin d → PosNat,
        if weak then a.eval (CircuitComparison.finiteVal ρ) ≤ b.eval (CircuitComparison.finiteVal ρ)
        else a.eval (CircuitComparison.finiteVal ρ) < b.eval (CircuitComparison.finiteVal ρ) := by
  obtain ⟨a', hea⟩ := bounded_finite d a ha
  obtain ⟨b', heb⟩ := bounded_finite d b hb
  have ha' : a'.depth ≤ 2 := by simpa only [← hea, depth_rename] using hda
  have hb' : b'.depth ≤ 2 := by simpa only [← heb, depth_rename] using hdb
  have hcode : (d, encodeExpr a, encodeExpr b) = expressionCode a' b' := by
    simp only [expressionCode, hea, heb]
  rw [hcode, scalarComparison_expressionCode norm weak a' b' ha' hb', sourceOrder_iff]
  constructor <;> intro h ρ <;>
    simpa only [← hea, ← heb, eval_finite_rename] using h ρ

theorem polynomialSourceBridge : Targets.PolynomialSourceBridge := by
  intro p hp weak
  have hbound := NonnegativePolynomialComparisonProof.variablesBounded p hp
  have hdepth := NonnegativePolynomialComparisonProof.depthBound p hp
  cases weak with
  | false =>
      refine ⟨scalarDomain_bounded _ _ _ hbound.2.1 hbound.1 hdepth.2.1 hdepth.1, ?_⟩
      intro norm
      exact (NonnegativePolynomialComparisonProof.strictReduction p hp).trans
        (scalarComparison_bounded _ norm false _ _ hbound.2.1 hbound.1 hdepth.2.1 hdepth.1).symm
  | true =>
      refine ⟨scalarDomain_bounded _ _ _ hbound.2.2 hbound.1 hdepth.2.2 hdepth.1, ?_⟩
      intro norm
      exact (NonnegativePolynomialComparisonProof.weakReduction p hp).trans
        (scalarComparison_bounded _ norm true _ _ hbound.2.2 hbound.1 hdepth.2.2 hdepth.1).symm

theorem positiveSourceFacts : Targets.PositiveSourceFacts := by
  intro d a
  refine ⟨fun i hi => WWGroundClassesProof.exponentialFragmentMembership d a i hi, ?_⟩
  intro χ hχ
  obtain ⟨ρ, hρ⟩ := WWGroundAdmissibilityProof.exactPositiveTuples.1 d
    (support (embed a)) χ hχ
  have hv : WWClosedAssignment.closedValue (substitute χ (embed a)) =
      (a.eval ρ : Ordinal.{0}) := by
    unfold WWClosedAssignment.closedValue
    rw [WWOrdinalTermSemanticsProof.structuralSubstitution]
    exact (WWGroundAdmissibilityProof.originalLocality d (embed a) _ _ hρ).trans
      (WWOrdinalTermSemanticsProof.literalEmbedding d a ρ).1
  refine ⟨a.eval ρ, PositiveExpressionProperties.eval_positive ρ a, hv, ?_⟩
  rw [hv]
  exact (WWOrdinalTermSemanticsProof.finiteNorm _).2

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ScalarSemanticProof
