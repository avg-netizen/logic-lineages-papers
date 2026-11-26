import LogicLineages.PersistentMarking.DecisionInventoryTargets
namespace LogicLineages.PersistentMarking.DecisionDepthProof
open Spine NameBridge TypeSupport DecisionInventory
mutual
 theorem bound (q : Expr) (n : Nat) (h : LambdaPath q n) : n ≤ lambdaDepth q := by
  cases q with
  | free σ x => cases h; exact Nat.zero_le _
  | bound σ i => cases h; exact Nat.zero_le _
  | lam σ q =>
    cases h with
    | root => exact Nat.zero_le _
    | lam h => have ih := bound q _ h; simp only [lambdaDepth]; omega
  | head f bs =>
    cases h with
    | root => exact Nat.zero_le _
    | head h => exact boundArgs bs n h
  | marked f τ bs es =>
    cases h with
    | root => exact Nat.zero_le _
    | markedBase h => exact Nat.le_trans (boundArgs bs n h) (Nat.le_max_left _ _)
    | markedExtra h => exact Nat.le_trans (boundArgs es n h) (Nat.le_max_right _ _)
 termination_by sizeOf q
 theorem boundArgs (qs : Args) (n : Nat) (h : LambdaPathArgs qs n) : n ≤ lambdaDepthArgs qs := by
  cases qs with
  | nil => cases h
  | cons q qs =>
    cases h with
    | here h => exact Nat.le_trans (bound q n h) (Nat.le_max_left _ _)
    | there h => exact Nat.le_trans (boundArgs qs n h) (Nat.le_max_right _ _)
 termination_by sizeOf qs
end
mutual
 theorem attained (q : Expr) : LambdaPath q (lambdaDepth q) := by
  cases q with
  | free σ x => exact .root
  | bound σ i => exact .root
  | lam σ q => simpa only [lambdaDepth,Nat.add_comm] using LambdaPath.lam (σ := σ) (attained q)
  | head f bs =>
    by_cases hz : lambdaDepthArgs bs = 0
    · simpa only [lambdaDepth,hz] using (LambdaPath.root (q := Expr.head f bs))
    · exact .head (attainedArgs bs (by omega))
  | marked f τ bs es =>
    by_cases hle : lambdaDepthArgs bs ≤ lambdaDepthArgs es
    · by_cases hz : lambdaDepthArgs es = 0
      · have hb : lambdaDepthArgs bs = 0 := by omega
        simpa only [lambdaDepth,hz,hb,Nat.max_self] using (LambdaPath.root (q := Expr.marked f τ bs es))
      · simpa only [lambdaDepth,Nat.max_eq_right hle] using (LambdaPath.markedExtra (f := f) (τ := τ) (bs := bs) (attainedArgs es (by omega)))
    · have he : lambdaDepthArgs es ≤ lambdaDepthArgs bs := by omega
      simpa only [lambdaDepth,Nat.max_eq_left he] using (LambdaPath.markedBase (f := f) (τ := τ) (es := es) (attainedArgs bs (by omega)))
 termination_by sizeOf q
 theorem attainedArgs (qs : Args) (hpos : 0 < lambdaDepthArgs qs) : LambdaPathArgs qs (lambdaDepthArgs qs) := by
  cases qs with
  | nil => simp only [lambdaDepthArgs] at hpos; omega
  | cons q qs =>
    by_cases hle : lambdaDepth q ≤ lambdaDepthArgs qs
    · have hp : 0 < lambdaDepthArgs qs := by simpa only [lambdaDepthArgs,Nat.max_eq_right hle] using hpos
      simpa only [lambdaDepthArgs,Nat.max_eq_right hle] using LambdaPathArgs.there (q := q) (attainedArgs qs hp)
    · have he : lambdaDepthArgs qs ≤ lambdaDepth q := by omega
      simpa only [lambdaDepthArgs,Nat.max_eq_left he] using LambdaPathArgs.here (qs := qs) (attained q)
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.DecisionDepthProof
