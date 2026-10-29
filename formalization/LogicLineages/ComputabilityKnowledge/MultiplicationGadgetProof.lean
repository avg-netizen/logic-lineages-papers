module

public import LogicLineages.ComputabilityKnowledge.Comparators.MultiplicationGadget
public import LogicLineages.ComputabilityKnowledge.RestrictedProductProof

@[expose] public section

/-!
# Proof of paper 02's seven-equation multiplication gadget (`lem:seven-equations`)

Proves the frozen `Comparators.MultiplicationGadget.Target`: the numerical
equivalence, the literal source-expression correspondence and the depth-one
bound. The numerical part follows the paper: with `a = x+y+1`, `b = a+x`, the
bounds `y < 2^a - 1`, `y < 2^b - 1` are automatic, the positive slacks make the
restricted-product upper bounds strict, the accepted bounded lemma is applied
twice, and `t = s + w` cancels the common `a*y`.
-/

namespace LogicLineages.ComputabilityKnowledge.MultiplicationGadgetProof

open LogicLineages.ComputabilityKnowledge.PositiveExpression
open LogicLineages.ComputabilityKnowledge.Comparators.MultiplicationGadget

theorem lt_two_pow_self' (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- The accepted bounded multiplication lemma, restated over plain naturals. -/
theorem rpNat (A Y S : Nat) (hA : 0 < A) (hY : 0 < Y) (hS : 0 < S)
    (hy : Y < 2 ^ A - 1) (hs : S < A * (2 ^ A - 1)) :
    S = A * Y ↔ ∃ U Q : Nat, 0 < U ∧ 0 < Q ∧
      2 ^ A * U + 1 = U + 2 ^ S ∧ 2 ^ A * Q + Y + 1 = U + Q + 2 ^ A := by
  have hRP := LogicLineages.ComputabilityKnowledge.RestrictedProductProof.boundedMultiplication
  unfold LogicLineages.ComputabilityKnowledge.Comparators.RestrictedProduct.Target at hRP
  have hiff := hRP ⟨A, hA⟩ ⟨Y, hY⟩ ⟨S, hS⟩ hy hs
  constructor
  · intro h
    obtain ⟨⟨U, hU⟩, ⟨Q, hQ⟩, e1, e2⟩ := hiff.mp h
    exact ⟨U, Q, hU, hQ, e1, e2⟩
  · rintro ⟨U, Q, hU, hQ, e1, e2⟩
    exact hiff.mpr ⟨⟨U, hU⟩, ⟨Q, hQ⟩, e1, e2⟩

/-- The numerical gadget over plain naturals, with affine `A`, `B`. -/
theorem numericCore (X Y W A B : Nat) (hX : 0 < X) (hY : 0 < Y)
    (hA : A = X + Y + 1) (hB : B = A + X) :
    W = X * Y ↔ ∃ S T U V Q R H K : Nat,
      0 < S ∧ 0 < T ∧ 0 < U ∧ 0 < V ∧ 0 < Q ∧ 0 < R ∧ 0 < H ∧ 0 < K ∧
      2 ^ A * U + 1 = U + 2 ^ S ∧ 2 ^ B * V + 1 = V + 2 ^ T ∧
      2 ^ A * Q + Y + 1 = U + Q + 2 ^ A ∧ 2 ^ B * R + Y + 1 = V + R + 2 ^ B ∧
      S + A + H = 2 ^ A * A ∧ T + B + K = 2 ^ B * B ∧ T = S + W := by
  have hAp : 0 < A := by omega
  have hBp : 0 < B := by omega
  have pA := lt_two_pow_self' A
  have pB := lt_two_pow_self' B
  obtain ⟨DA, hDA⟩ : ∃ D, 2 ^ A = D + 1 := ⟨2 ^ A - 1, by omega⟩
  obtain ⟨DB, hDB⟩ : ∃ D, 2 ^ B = D + 1 := ⟨2 ^ B - 1, by omega⟩
  have hYA : Y + 1 < DA := by omega
  have hYB : Y + 1 < DB := by omega
  have hsubA : 2 ^ A - 1 = DA := by omega
  have hsubB : 2 ^ B - 1 = DB := by omega
  have hPA : 2 ^ A * A = A * DA + A := by
    rw [hDA, Nat.add_mul, Nat.one_mul, Nat.mul_comm DA A]
  have hPB : 2 ^ B * B = B * DB + B := by
    rw [hDB, Nat.add_mul, Nat.one_mul, Nat.mul_comm DB B]
  have hAY : A * (Y + 1) ≤ A * DA := Nat.mul_le_mul (Nat.le_refl A) (Nat.le_of_lt hYA)
  have hBY : B * (Y + 1) ≤ B * DB := Nat.mul_le_mul (Nat.le_refl B) (Nat.le_of_lt hYB)
  have eAY : A * (Y + 1) = A * Y + A := by rw [Nat.mul_add, Nat.mul_one]
  have eBY : B * (Y + 1) = B * Y + B := by rw [Nat.mul_add, Nat.mul_one]
  have hBXY : B * Y = A * Y + X * Y := by rw [hB, Nat.add_mul]
  have hyA : Y < 2 ^ A - 1 := by omega
  have hyB : Y < 2 ^ B - 1 := by omega
  constructor
  · intro hW
    have hSpos : 0 < A * Y := by
      have := Nat.mul_le_mul (show 1 ≤ A by omega) (show 1 ≤ Y by omega)
      omega
    have hTpos : 0 < B * Y := by
      have := Nat.mul_le_mul (show 1 ≤ B by omega) (show 1 ≤ Y by omega)
      omega
    have hsA : A * Y < A * (2 ^ A - 1) := by rw [hsubA]; omega
    have hsB : B * Y < B * (2 ^ B - 1) := by rw [hsubB]; omega
    obtain ⟨U, Q, hU, hQ, e1, e3⟩ := (rpNat A Y (A * Y) hAp hY hSpos hyA hsA).mp rfl
    obtain ⟨V, R, hV, hR, e2, e4⟩ := (rpNat B Y (B * Y) hBp hY hTpos hyB hsB).mp rfl
    exact ⟨A * Y, B * Y, U, V, Q, R, A * DA - A * Y, B * DB - B * Y,
      hSpos, hTpos, hU, hV, hQ, hR, by omega, by omega,
      e1, e2, e3, e4, by omega, by omega, by omega⟩
  · rintro ⟨S, T, U, V, Q, R, H, K, hS, hT, hU, hV, hQ, hR, hH, hK,
      e1, e2, e3, e4, e5, e6, e7⟩
    have hsA : S < A * (2 ^ A - 1) := by rw [hsubA]; omega
    have hsB : T < B * (2 ^ B - 1) := by rw [hsubB]; omega
    have hSA := (rpNat A Y S hAp hY hS hyA hsA).mpr ⟨U, Q, hU, hQ, e1, e3⟩
    have hTB := (rpNat B Y T hBp hY hT hyB hsB).mpr ⟨V, R, hV, hR, e2, e4⟩
    omega

theorem numerical : NumericalTarget := by
  unfold NumericalTarget
  rintro ⟨X, hX⟩ ⟨Y, hY⟩ ⟨W, hW⟩
  have core := numericCore X Y W (X + Y + 1) (X + Y + 1 + X) hX hY rfl rfl
  constructor
  · intro hw
    obtain ⟨S, T, U, V, Q, R, H, K, hS, hT, hU, hV, hQ, hR, hH, hK,
      e1, e2, e3, e4, e5, e6, e7⟩ := core.mp hw
    refine ⟨⟨S, hS⟩, ⟨T, hT⟩, ⟨U, hU⟩, ⟨V, hV⟩, ⟨Q, hQ⟩, ⟨R, hR⟩, ⟨H, hH⟩, ⟨K, hK⟩, ?_⟩
    show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    exact ⟨e1, e2, e3, e4, e5, e6, e7⟩
  · rintro ⟨⟨S, hS⟩, ⟨T, hT⟩, ⟨U, hU⟩, ⟨V, hV⟩, ⟨Q, hQ⟩, ⟨R, hR⟩, ⟨H, hH⟩, ⟨K, hK⟩, e⟩
    have e' : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := e
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e'
    exact core.mpr ⟨S, T, U, V, Q, R, H, K, hS, hT, hU, hV, hQ, hR, hH, hK,
      e1, e2, e3, e4, e5, e6, e7⟩

theorem sourceCorr : SourceCorrespondence := by
  unfold SourceCorrespondence
  intro x y w s t u v q r h k
  constructor
  · intro hsrc
    unfold SourceEquations at hsrc
    have h1 := hsrc _ (List.Mem.head _)
    have h2 := hsrc _ (List.Mem.tail _ (List.Mem.head _))
    have h3 := hsrc _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have h4 := hsrc _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have h5 := hsrc _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))
    have h6 := hsrc _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))
    have h7 := hsrc _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
    simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
      valuation] at h1 h2 h3 h4 h5 h6 h7
    show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · intro e
    have e' : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := e
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e'
    unfold SourceEquations
    intro pair hp
    unfold equations at hp
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e1
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e2
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e3
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e4
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e5
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e6
    rcases hp with _ | ⟨_, hp⟩
    · simp only [eval_add, eval_emul, eval_var, eval_one, Nat.mul_one, aTerm, bTerm,
        valuation]
      exact e7
    cases hp

theorem sourceDepth : SourceDepth := by
  unfold SourceDepth
  intro pair hp
  unfold equations at hp
  rcases hp with _ | ⟨_, hp⟩
  · decide
  rcases hp with _ | ⟨_, hp⟩
  · decide
  rcases hp with _ | ⟨_, hp⟩
  · decide
  rcases hp with _ | ⟨_, hp⟩
  · decide
  rcases hp with _ | ⟨_, hp⟩
  · decide
  rcases hp with _ | ⟨_, hp⟩
  · decide
  rcases hp with _ | ⟨_, hp⟩
  · decide
  cases hp

theorem sevenEquationMultiplication :
    LogicLineages.ComputabilityKnowledge.Comparators.MultiplicationGadget.Target := by
  show NumericalTarget ∧ SourceCorrespondence ∧ SourceDepth
  exact ⟨numerical, sourceCorr, sourceDepth⟩

end LogicLineages.ComputabilityKnowledge.MultiplicationGadgetProof
