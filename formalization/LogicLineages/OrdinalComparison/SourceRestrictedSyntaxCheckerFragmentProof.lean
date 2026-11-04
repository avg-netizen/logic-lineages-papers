module
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Proof

theorem malformedCases : Targets.MalformedCases := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have h0 : n % 8 ≠ 0 := by omega
    have h12 : ¬ (n = 1 ∨ n = 2) := by omega
    have h56 : ¬ (n % 8 = 5 ∨ n % 8 = 6) := by omega
    rw [fragmentCode]
    simp [h0, h12, h56]
  · intro n hn hp
    have h0 : n % 8 ≠ 0 := by omega
    have h12 : ¬ (n = 1 ∨ n = 2) := by omega
    have h56 : ¬ (n % 8 = 5 ∨ n % 8 = 6) := by omega
    rw [fragmentCode]
    simp [h0, h12, h56]
  · intro c hc
    simp only [restrictedCode, hc]

private theorem fragment_app (a b : Nat) :
    fragmentCode (8 * Nat.pair a b + 5) = (fragmentCode a && fragmentCode b) := by
  have hm : (8 * Nat.pair a b + 5) % 8 = 5 := by omega
  have hd : (8 * Nat.pair a b + 5) / 8 = Nat.pair a b := by omega
  have h12 : ¬ (8 * Nat.pair a b + 5 = 1 ∨ 8 * Nat.pair a b + 5 = 2) := by omega
  rw [fragmentCode]
  simp [hm, hd, h12, Nat.unpair_pair]

private theorem fragment_lam (σ b : Nat) :
    fragmentCode (8 * Nat.pair σ b + 6) =
      (decide (σ = SyntaxCode.typeCode Ty.ground) && fragmentCode b) := by
  have hm : (8 * Nat.pair σ b + 6) % 8 = 6 := by omega
  have hd : (8 * Nat.pair σ b + 6) / 8 = Nat.pair σ b := by omega
  have h12 : ¬ (8 * Nat.pair σ b + 6 = 1 ∨ 8 * Nat.pair σ b + 6 = 2) := by omega
  rw [fragmentCode]
  simp [hm, hd, h12, Nat.unpair_pair]

private theorem ground_type_code (σ : Ty) :
    SyntaxCode.typeCode σ = SyntaxCode.typeCode Ty.ground ↔ σ = Ty.ground := by
  cases σ <;> simp [SyntaxCode.typeCode, SyntaxCode.arrowCode]

theorem fragmentCalibration : Targets.FragmentCalibration := by
  intro Γ τ t
  induction t with
  | var x =>
      simp only [SyntaxCode.encodeTerm, SyntaxCode.erase, SyntaxCode.code,
        SourceGroundBinderFragment.Fragment]
      rw [fragmentCode]
      simp
  | zeroC =>
      simp [SyntaxCode.encodeTerm, SyntaxCode.erase, SyntaxCode.code, fragmentCode,
        SourceGroundBinderFragment.Fragment]
  | succC =>
      simp [SyntaxCode.encodeTerm, SyntaxCode.erase, SyntaxCode.code, fragmentCode,
        SourceGroundBinderFragment.Fragment]
  | caseC σ =>
      have h := malformedCases.1 (8 * SyntaxCode.typeCode σ + 3) (Or.inl (by omega))
      simpa only [SyntaxCode.encodeTerm, SyntaxCode.erase, SyntaxCode.code,
        SourceGroundBinderFragment.Fragment, h, Bool.false_eq_true, iff_self]
  | recC σ =>
      have h := malformedCases.1 (8 * SyntaxCode.typeCode σ + 4) (Or.inr (Or.inl (by omega)))
      simpa only [SyntaxCode.encodeTerm, SyntaxCode.erase, SyntaxCode.code,
        SourceGroundBinderFragment.Fragment, h, Bool.false_eq_true, iff_self]
  | app f a ihf iha =>
      change fragmentCode (8 * Nat.pair (SyntaxCode.encodeTerm f) (SyntaxCode.encodeTerm a) + 5)
        = true ↔ SourceGroundBinderFragment.Fragment f ∧ SourceGroundBinderFragment.Fragment a
      rw [fragment_app, Bool.and_eq_true, ihf, iha]
  | @lam Γ σ τ body ih =>
      change fragmentCode (8 * Nat.pair (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm body) + 6)
        = true ↔ σ = Ty.ground ∧ SourceGroundBinderFragment.Fragment body
      rw [fragment_lam, Bool.and_eq_true, decide_eq_true_eq, ground_type_code, ih]
  | ranked s _ _ => nomatch s

end LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Proof
