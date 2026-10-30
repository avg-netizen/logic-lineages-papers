module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalTermSemantics
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
public import LogicLineages.OrdinalComparison.FiniteCollapse

@[expose] public section

/-! External source-embedding supplier after independent target freeze.
No decision procedure for general finite-valued collapse terms is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

open PositiveExpression
open LogicLineages.OrdinalComparison
open WWOrdinalTermSemantics

private theorem finite_coeff (n : Nat) :
    Ordinal.CNF.coeff Ordinal.omega0 (n : Ordinal.{0}) = Finsupp.single 0 (n : Ordinal) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Ordinal.CNF.coeff_zero_right, Finsupp.single_zero]
  · have hne : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn
    simpa only [Ordinal.opow_zero, one_mul, add_zero, Ordinal.CNF.coeff_zero_right] using
      Ordinal.CNF.coeff_opow_mul_add (e := 0) (y := 0) Ordinal.one_lt_omega0 hne
        (Ordinal.natCast_lt_omega0 n) (by simp)

theorem naturalSum_finite (a b : Nat) :
    ordinalNaturalSum (a : Ordinal) (b : Ordinal) = ((a + b : Nat) : Ordinal) := by
  unfold ordinalNaturalSum
  rw [finite_coeff, finite_coeff, ← Finsupp.single_add, Ordinal.CNF.eval_single]
  simp only [Ordinal.opow_zero, one_mul, Nat.cast_add]

theorem naturalProduct_finite (a b : Nat) :
    ordinalNaturalProduct (a : Ordinal) (b : Ordinal) = ((a * b : Nat) : Ordinal) := by
  by_cases ha : a = 0
  · subst a
    simp [ordinalNaturalProduct, Ordinal.CNF.zero_right, Ordinal.CNF.eval_zero_right]
  · by_cases hb : b = 0
    · subst b
      simp [ordinalNaturalProduct, Ordinal.CNF.zero_right, Ordinal.CNF.eval_zero_right]
    · have ha' : (a : Ordinal.{0}) ≠ 0 := by exact_mod_cast ha
      have hb' : (b : Ordinal.{0}) ≠ 0 := by exact_mod_cast hb
      have hca := Ordinal.CNF.of_lt ha' (Ordinal.natCast_lt_omega0 a)
      have hcb := Ordinal.CNF.of_lt hb' (Ordinal.natCast_lt_omega0 b)
      simp only [ordinalNaturalProduct, hca, hcb, List.foldr_cons, List.foldr_nil,
        add_zero]
      have hzero : ordinalNaturalSum 0 0 = 0 := by simpa using naturalSum_finite 0 0
      rw [hzero, Ordinal.CNF.eval_single]
      simp only [Ordinal.opow_zero, one_mul, Ordinal.natCast_mul]

theorem finiteArithmetic : Comparators.WWOrdinalTermSemantics.FiniteArithmetic := by
  intro a b
  refine ⟨naturalSum_finite a b, naturalProduct_finite a b, ?_⟩
  simpa only [Ordinal.opow_natCast, Nat.cast_ofNat] using (Ordinal.natCast_pow 2 a).symm

theorem finiteNorm : Comparators.WWOrdinalTermSemantics.FiniteNorm := by
  intro n
  have hs := normalRepresentationSound (NONote.ofNat n)
  have hn := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
  rw [norm_ofNat] at hn
  change (ONote.ofNat n).repr < epsilonZero at hs
  change actualOrdinalNorm (ONote.ofNat n).repr = n at hn
  rw [ONote.repr_ofNat] at hs hn
  exact ⟨hs, hn⟩

private theorem embed_value {ι : Type} (e : Expr ι) (ρ : ι → PosNat) :
    denote (fun i => ((ρ i : Nat) : Ordinal)) (embed e) = (e.eval ρ : Ordinal) := by
  induction e with
  | one => simp [embed, denote]
  | var i => rfl
  | add a b ha hb =>
      simp only [embed, denote, eval_add, ha, hb]
      exact naturalSum_finite _ _
  | emul a b ha hb =>
      simp only [embed, denote, eval_emul, ha, hb]
      rw [(finiteArithmetic _ 0).2.2]
      exact naturalProduct_finite _ _

theorem literalEmbedding : Comparators.WWOrdinalTermSemantics.LiteralEmbedding := by
  intro d e ρ
  have h := embed_value e ρ
  exact ⟨h, by rw [h]; exact (finiteNorm _).2⟩

theorem structuralSubstitution : Comparators.WWOrdinalTermSemantics.StructuralSubstitution := by
  intro ι κ σ ρ t
  induction t <;> simp_all [substitute, denote]

theorem injectiveEmbedding : Comparators.WWOrdinalTermSemantics.InjectiveEmbedding := by
  intro ι a
  induction a with
  | one => intro b h; cases b <;> simp_all [embed]
  | var i => intro b h; cases b <;> simp_all [embed]
  | add a b ha hb =>
      intro c h
      cases c with
      | one => cases h
      | var i => cases h
      | emul c d => cases h
      | add c d =>
          have hh := Term.add.inj h
          exact congrArg₂ Expr.add (ha hh.1) (hb hh.2)
  | emul a b ha hb =>
      intro c h
      cases c with
      | one => cases h
      | var i => cases h
      | add c d => cases h
      | emul c d =>
          have hh := Term.emul.inj h
          exact congrArg₂ Expr.emul (ha hh.1) (hb hh.2)

theorem wwOrdinalTermSemantics : Comparators.WWOrdinalTermSemantics.Target :=
  ⟨finiteArithmetic, finiteNorm, literalEmbedding, structuralSubstitution, injectiveEmbedding⟩

end LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
