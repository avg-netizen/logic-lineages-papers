module
public import LogicLineages.OrdinalComparison.HeadWindowNextProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualDifferentHeadStrictWindow : Targets.ActualDifferentHeadStrictWindow := by
  intro lam mu hlam hmu hlamlim hmulim hmulam t u htlam htmu humu hut
  have hn := actualNextLimitHeadFacts mu hmu hmulim
  have hbetween : mu + Ordinal.omega0 ≤ lam := actualLeastNextLimit mu lam hlamlim hmulam
  have hcommon := actualCommonNormHeadOrder (mu + Ordinal.omega0) lam hn.1 hlam hn.2.1
    hlamlim hbetween t (by rw [hn.2.2.1]; exact htmu) htlam
  have hPhi : actualOrdinalNorm mu ≤ Phi t := by have h := self_lt_Phi t; omega
  have hsame := actualFixedHeadValueEndpointOrder mu hmu hmulim u (Phi t) humu hPhi hut
  have hdelete := hn.2.2.2 t htmu
  constructor
  · have hstep := hdelete.2.2.2
    have hle := hcommon.2.2
    omega
  · have hstep := hdelete.2.1
    have hle := hcommon.2.1
    omega

private theorem head_key_trichotomy (a b : Ordinal) (t u : Nat) :
    actualHeadKeyLess a t b u ∨ (a = b ∧ t = u) ∨ actualHeadKeyLess b u a t := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy t u with h | rfl | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem actualFiniteHeadWindowLexicographic : Targets.ActualFiniteHeadWindowLexicographic := by
  intro N lam t hheads s hinputs
  have hstrict : ∀ i j : Fin N, actualHeadKeyLess (lam i) (t i) (lam j) (t j) →
      actualHeadValue (lam i) (t i) < actualHeadValue (lam j) (t j) ∧
      actualHeadEndpoint (lam i) (t i) < actualHeadEndpoint (lam j) (t j) := by
    intro i j hkey
    have hni := hinputs i
    have hnj := hinputs j
    have hdi : actualOrdinalNorm (lam i) ≤ t i := by omega
    have hdj : actualOrdinalNorm (lam j) ≤ t j := by omega
    rcases hkey with hhead | ⟨heq, hinput⟩
    · exact actualDifferentHeadStrictWindow (lam j) (lam i) (hheads j).1 (hheads i).1
        (hheads j).2 (hheads i).2 hhead (t j) (t i) hdj (by omega) hdi
        (hni.2.2.trans_le (Phi_strictMono.monotone hnj.2.1))
    · rw [heq] at hdi ⊢
      exact actualFixedHeadValueEndpointOrder (lam j) (hheads j).1 (hheads j).2
        (t i) (t j) hdi hdj hinput
  intro i j
  have hkeys := head_key_trichotomy (lam i) (lam j) (t i) (t j)
  constructor
  · constructor
    · intro hval
      rcases hkeys with h | ⟨heq, hinput⟩ | h
      · exact h
      · rw [heq, hinput] at hval
        exact False.elim (Nat.lt_irrefl _ hval)
      · exact False.elim (Nat.lt_asymm hval (hstrict j i h).1)
    · intro h
      exact (hstrict i j h).1
  · constructor
    · constructor
      · intro hval
        rcases hkeys with h | heq | h
        · exact False.elim ((Nat.ne_of_lt (hstrict i j h).1) hval)
        · exact heq
        · exact False.elim ((Nat.ne_of_lt (hstrict j i h).1) hval.symm)
      · rintro ⟨heq, hinput⟩
        rw [heq, hinput]
    · constructor
      · intro hval
        rcases hkeys with h | heq | h
        · exact False.elim ((Nat.ne_of_lt (hstrict i j h).2) hval)
        · exact heq
        · exact False.elim ((Nat.ne_of_lt (hstrict j i h).2) hval.symm)
      · rintro ⟨heq, hinput⟩
        rw [heq, hinput]

theorem fullActualDifferentHeadWindow : Targets.FullActualDifferentHeadWindow :=
  ⟨actualLeastNextLimit, actualNextLimitHeadFacts, actualCommonNormHeadOrder,
    actualDifferentHeadStrictWindow, actualFiniteHeadWindowLexicographic⟩

end LogicLineages.OrdinalComparison
