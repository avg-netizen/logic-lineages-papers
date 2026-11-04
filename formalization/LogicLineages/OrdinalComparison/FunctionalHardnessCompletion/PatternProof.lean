module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.Targets
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Proof
open SourcePolynomialRealization SourceFiniteExponentProjection

private theorem pairList_length {A B : Type*} (l : List A) (f g : A → B) :
    (l.flatMap fun a => [f a, g a]).length = 2*l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

theorem completePatterns : Targets.CompletePatterns := by
  intro n
  induction n with
  | zero =>
      constructor
      · rfl
      · intro z
        have hz : z = (fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
        simp [masks, hz]
  | succ n ih =>
      constructor
      · rw [masks, pairList_length, ih.1, pow_succ]
        omega
      · intro z
        apply List.mem_flatMap.mpr
        refine ⟨(fun i => z i.succ), ih.2 _, ?_⟩
        have he : z = Fin.cases (z 0) (fun i => z i.succ) := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        cases h : z 0 with
        | false =>
            apply List.mem_cons.mpr
            exact Or.inl (by simpa only [h] using he)
        | true =>
            apply List.mem_cons_of_mem
            apply List.mem_cons.mpr
            exact Or.inl (by simpa only [h] using he)

theorem ordinalRestriction {n : Nat} (z : Mask n) (x : Fin n → Ordinal)
    (d : SignedPair.Expression n) :
    SignedPair.meaning x (restrict z d) = SignedPair.meaning (zeroExtend z x) d := by
  have hz : SignedPair.signedCNF (0 : Ordinal) = 0 := by
    simpa using SignedPair.Proof.cnf_nat 0
  induction d with
  | unit => rfl
  | var i =>
      cases h : z i <;>
        simp [restrict, h, zeroExtend, SignedPair.zeroExpression, SignedPair.meaning, hz]
  | add a b iha ihb => simp only [restrict, SignedPair.meaning, iha, ihb]
  | neg a ih => simp only [restrict, SignedPair.meaning, ih]
  | shift a ih => simp only [restrict, SignedPair.meaning, ih]

theorem polynomialRestriction {n : Nat} (z : Mask n) (x : Fin n → PolynomialGroup)
    (d : SignedPair.Expression n) :
    polynomialMeaning x (restrict z d) = polynomialMeaning (zeroExtend z x) d := by
  induction d with
  | unit => rfl
  | var i =>
      cases h : z i <;>
        simp [restrict, h, zeroExtend, SignedPair.zeroExpression, polynomialMeaning]
  | add a b iha ihb => simp only [restrict, polynomialMeaning, iha, ihb]
  | neg a ih => simp only [restrict, polynomialMeaning, ih]
  | shift a ih => simp only [restrict, polynomialMeaning, ih]

theorem exactRestriction : Targets.ExactRestriction := by
  intro n z
  exact ⟨ordinalRestriction z, polynomialRestriction z⟩

private theorem signed_zero : signedCoefficients 0 = 0 := by
  ext k
  simp [signedCoefficients]

theorem signed_zeroExtend {n : Nat} (z : Mask n) (p : Fin n → NonnegativePolynomial) :
    (fun i => signedCoefficients (zeroExtend z p i)) =
      zeroExtend z (fun i => signedCoefficients (p i)) := by
  funext i
  cases h : z i <;> simp [zeroExtend, h, signed_zero]

theorem restrictSystem_solves {n : Nat} (z : Mask n) (s : System n)
    (p : Fin n → NonnegativePolynomial) :
    PolynomialSolves (restrictSystem z s) p ↔ PolynomialSolves s (zeroExtend z p) := by
  constructor
  · intro h d hd
    have he := h (restrict z d) (List.mem_map.mpr ⟨d, hd, rfl⟩)
    rw [polynomialRestriction, ← signed_zeroExtend] at he
    exact he
  · intro h d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    rw [polynomialRestriction, ← signed_zeroExtend]
    exact h e he

theorem simultaneousPolynomialPatterns : Targets.SimultaneousPolynomialPatterns := by
  intro n s
  constructor
  · rintro ⟨p, hp⟩
    let z : Mask n := fun i => decide (p i ≠ 0)
    let q : Fin n → NonnegativePolynomial := fun i =>
      if p i = 0 then Finsupp.single 0 1 else p i
    have hq : ∀ i, q i ≠ 0 := by
      intro i
      dsimp [q]
      split_ifs with h
      · intro he
        have he0 := congrArg (fun f : NonnegativePolynomial => f 0) he
        simpa using he0
      · exact h
    have hext : zeroExtend z q = p := by
      funext i
      by_cases h : p i = 0 <;> simp [zeroExtend, z, q, h]
    refine ⟨z, (completePatterns n).2 z, q, hq, ?_⟩
    apply (restrictSystem_solves z s q).mpr
    simpa only [hext] using hp
  · rintro ⟨z, hz, p, hp, hs⟩
    exact ⟨zeroExtend z p, (restrictSystem_solves z s p).mp hs⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Proof
