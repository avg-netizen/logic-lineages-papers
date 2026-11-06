module
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.GapProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof

theorem shiftedQuadraticOrder : Targets.ShiftedQuadraticOrder := by
  intro j k a b t u ht hu
  have hL := quantitativeQuadraticGap j k (a.natAbs+b.natAbs) t u ht hu
  have hR := quantitativeQuadraticGap k j (a.natAbs+b.natAbs) u t
    (by unfold scalarTail at *; omega) (by unfold scalarTail at *; omega)
  have ha : -(a.natAbs : Int) ≤ a := by omega
  have hb : -(b.natAbs : Int) ≤ b := by omega
  have ha' : a ≤ (a.natAbs : Int) := Int.le_natAbs
  have hb' : b ≤ (b.natAbs : Int) := Int.le_natAbs
  have hpL : 0 < (rawQuadraticShift j t : Int)+a := by unfold scalarTail at ht; omega
  have hpR : 0 < (rawQuadraticShift k u : Int)+b := by unfold scalarTail at hu; omega
  have hlo (h : CoreLexLT j k t u) :
      (rawQuadraticShift j t : Int)+a < (rawQuadraticShift k u : Int)+b := by
    have hh := hL.2.2.2.2 h
    omega
  have hhi (h : CoreLexLT k j u t) :
      (rawQuadraticShift k u : Int)+b < (rawQuadraticShift j t : Int)+a := by
    have hh := hR.2.2.2.2 h
    omega
  refine ⟨hpL,hpR,?_⟩
  rcases lt_trichotomy t u with htu | rfl | hut
  · have hh := hlo (Or.inl htu)
    dsimp [ShiftLexLT]
    omega
  · rcases lt_trichotomy j k with hjk | rfl | hkj
    · have hh := hlo (Or.inr ⟨rfl,hjk⟩)
      dsimp [ShiftLexLT]
      omega
    · dsimp [ShiftLexLT]
      omega
    · have hh := hhi (Or.inr ⟨rfl,hkj⟩)
      dsimp [ShiftLexLT]
      omega
  · have hh := hhi (Or.inl hut)
    dsimp [ShiftLexLT]
    omega

end LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
