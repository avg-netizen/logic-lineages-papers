module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.GuardAlgebraProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerComparisonProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.GuardProof
open PolynomialGraphCompletion WordLinearDecisionCompletion FullWordGuardCompletion

theorem renamePairRow_value (left right : Nat) (r : Row) (ν : Nat → Nat)
    (hr : ∀ a ∈ r.2, a.2.1 ≤ 1) :
    RowValue (renamePairRow left right r) ν =
      RowValue r (pairEnv (ν left) (ν right)) := by
  simp only [RowValue,renamePairRow,List.map_map,Function.comp_def]
  apply congrArg (fun xs : List Int => r.1+xs.sum)
  apply List.map_congr_left
  intro a ha
  have hname : ν (if a.2.1 = 0 then left else right) =
      pairEnv (ν left) (ν right) a.2.1 := by
    by_cases h0 : a.2.1 = 0
    · simp [h0,pairEnv]
    · have h1 : a.2.1 = 1 := by have h := hr a ha; omega
      simp [h1,pairEnv]
  rw [hname]

theorem renamePairRow_safe (D maximum right : Nat) (r : Row) (ν : Nat → Nat)
    (hne : right ≠ maximum) (ha : RowAllowed D r)
    (hd : RowDomain r (pairEnv (ν maximum) (ν right))) (hl : LinearInMaximum r) :
    ∀ a ∈ (renamePairRow maximum right r).2, SafeToken D maximum ν a.2 := by
  intro b hb
  obtain ⟨a,ha',rfl⟩ := List.mem_map.mp hb
  have hi := hl a ha'
  have hname : ν (if a.2.1 = 0 then maximum else right) =
      pairEnv (ν maximum) (ν right) a.2.1 := by
    by_cases h0 : a.2.1 = 0
    · simp [h0,pairEnv]
    · have h1 : a.2.1 = 1 := by omega
      simp [h1,pairEnv]
  refine ⟨ha a ha',?_,?_⟩
  · rw [hname]
    exact hd a ha'
  · intro hx
    by_cases h0 : a.2.1 = 0
    · exact hi.2 h0
    · have hx' : right = maximum := by simpa [h0] using hx
      exact False.elim (hne hx')

theorem orderedGuard_correct (D : Nat) (u v : Token) (desired : Nat) (ν : Nat → Nat)
    (hname : ∀ a ∈ (packageRow (FullWordGuardCompletion.compile D (u.2,v.2))).2,
      a.2.1 ≤ 1) :
    Formula.eval ν (orderedGuard D u v desired) ↔
      GuardHolds (guardAt (packageGuards (FullWordGuardCompletion.compile D (u.2,v.2))) desired)
        (packageRow (FullWordGuardCompletion.compile D (u.2,v.2)))
        (pairEnv (ν u.1) (ν v.1)) := by
  let out := FullWordGuardCompletion.compile D (u.2,v.2)
  let named := renamePairRow u.1 v.1 (packageRow out)
  have hval := renamePairRow_value u.1 v.1 (packageRow out) ν hname
  change Formula.eval ν (disjoin ((guardAt (packageGuards out) desired).map
    (fun sign => RankedWordDecisionCompletion.signFormula sign named))) ↔ _
  rw [disjoin_correct]
  constructor
  · rintro ⟨p,hp,hpval⟩
    obtain ⟨sign,hsign,rfl⟩ := List.mem_map.mp hp
    have hs := (signFormula_correct sign named ν).mp hpval
    rw [hval] at hs
    exact ⟨sign,hsign,hs⟩
  · rintro ⟨sign,hsign,hs⟩
    refine ⟨RankedWordDecisionCompletion.signFormula sign named,
      List.mem_map.mpr ⟨sign,hsign,rfl⟩,?_⟩
    apply (signFormula_correct sign named ν).mpr
    rwa [hval]

theorem orderedGuard_safe (D maximum right desired : Nat) (A B : Word)
    (ν : Nat → Nat) (hne : right ≠ maximum)
    (ha : RowAllowed D (packageRow (FullWordGuardCompletion.compile D (A,B))))
    (hd : RowDomain (packageRow (FullWordGuardCompletion.compile D (A,B)))
      (pairEnv (ν maximum) (ν right)))
    (hl : LinearInMaximum (packageRow (FullWordGuardCompletion.compile D (A,B)))) :
    SafeFormula D maximum ν (orderedGuard D (maximum,A) (right,B) desired) := by
  apply disjoin_safe
  intro p hp
  obtain ⟨sign,_,rfl⟩ := List.mem_map.mp hp
  exact signFormula_safe D maximum ν sign _
    (renamePairRow_safe D maximum right _ ν hne ha hd hl)

theorem guardHolds_order (D : Nat) (u v : Token) (desired : Nat) (ν : Nat → Nat)
    (hD : 3 ≤ D) (hu : WordAllowed D u.2) (hv : WordAllowed D v.2)
    (hdesired : desired ≤ 2)
    (htu : packageTail (FullWordGuardCompletion.compile D (u.2,v.2)) ≤ ν u.1)
    (htv : packageTail (FullWordGuardCompletion.compile D (u.2,v.2)) ≤ ν v.1)
    (hvu : ν v.1 ≤ ν u.1) :
    GuardHolds (guardAt (packageGuards (FullWordGuardCompletion.compile D (u.2,v.2))) desired)
      (packageRow (FullWordGuardCompletion.compile D (u.2,v.2)))
      (pairEnv (ν u.1) (ν v.1)) ↔
        orderNat (wordValue u.2 (ν u.1)) (wordValue v.2 (ν v.1)) = desired := by
  have had := (RunnerProof.admissionCorrect D (u.2,v.2)).mpr ⟨hu,hv⟩
  have hc := FullWordGuardCompletion.Proof.compiledThreeWay D (u.2,v.2) hD had
    (ν u.1) (ν v.1) htu htv hvu
  have hcases : desired = 0 ∨ desired = 1 ∨ desired = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact hc.1.symm.trans (ComparisonProof.orderNat_eq_zero _ _).symm
  · exact hc.2.1.symm.trans (ComparisonProof.orderNat_eq_one _ _).symm
  · exact hc.2.2.symm.trans (ComparisonProof.orderNat_eq_two _ _).symm

/-- Concrete ordered comparison at the original selected maximum name. -/
theorem namedOrderedComparison (D maximum right desired : Nat) (A B : Word)
    (ν : Nat → Nat) (hD : 3 ≤ D) (hA : WordAllowed D A) (hB : WordAllowed D B)
    (hne : right ≠ maximum) (hdesired : desired ≤ 2)
    (htx : pairCutoff D (maximum,A) (right,B) ≤ ν maximum)
    (hty : pairCutoff D (maximum,A) (right,B) ≤ ν right)
    (hyx : ν right ≤ ν maximum) :
    WordDomain A (ν maximum) ∧ WordDomain B (ν right) ∧
    SafeFormula D maximum ν (orderedGuard D (maximum,A) (right,B) desired) ∧
    (Formula.eval ν (orderedGuard D (maximum,A) (right,B) desired) ↔
      orderNat (wordValue A (ν maximum)) (wordValue B (ν right)) = desired) := by
  have had := (RunnerProof.admissionCorrect D (A,B)).mpr ⟨hA,hB⟩
  have hx : packageTail (FullWordGuardCompletion.compile D (A,B)) ≤ ν maximum :=
    (Nat.le_max_left _ _).trans htx
  have hy : packageTail (FullWordGuardCompletion.compile D (A,B)) ≤ ν right :=
    (Nat.le_max_left _ _).trans hty
  have hdomains := FullWordGuardCompletion.Proof.compiledDomains D (A,B) hD had
    (ν maximum) (ν right) hx hy
  have hsyntax := FullWordGuardCompletion.Proof.compiledSyntax D (A,B) hD had
  have hs := orderedGuard_safe D maximum right desired A B ν hne
    hsyntax.1 hdomains.2.2.1 hsyntax.2.1
  refine ⟨hdomains.1,hdomains.2.1,hs,?_⟩
  exact (orderedGuard_correct D (maximum,A) (right,B) desired ν
    (fun a ha => (hsyntax.2.1 a ha).1)).trans
      (guardHolds_order D (maximum,A) (right,B) desired ν hD hA hB hdesired hx hy hyx)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.GuardProof
