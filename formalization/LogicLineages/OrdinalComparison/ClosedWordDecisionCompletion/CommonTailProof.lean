module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmItemProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion

theorem floor_le_commonTail (D floor : Nat) (p : Formula) :
    floor ≤ commonTail D floor p := Nat.le_max_left _ _

theorem original_le_commonTail (D floor : Nat) (p : Formula) :
    OutcomeTransport.originalTail p ≤ commonTail D floor p :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem residue_le_commonTail (D floor : Nat) (p : Formula) :
    residueTail p ≤ commonTail D floor p :=
  (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

theorem matrix_le_commonTail (D floor : Nat) (p : Formula) (maximum : Nat)
    (hmaximum : maximum ∈ names p) :
    (matrix D maximum p).tail ≤ commonTail D floor p := by
  have h : (matrix D maximum p).tail ≤
      Algorithm.foldMax ((names p).map (fun x => (matrix D x p).tail)) :=
    AlgorithmProof.member_le_foldMax _ _ (List.mem_map.mpr ⟨maximum,hmaximum,rfl⟩)
  exact h.trans ((Nat.le_max_right _ _).trans
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

#print axioms floor_le_commonTail
#print axioms original_le_commonTail
#print axioms residue_le_commonTail
#print axioms matrix_le_commonTail

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
