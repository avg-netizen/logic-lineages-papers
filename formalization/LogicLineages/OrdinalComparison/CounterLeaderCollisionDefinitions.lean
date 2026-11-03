module
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderCollision
open CounterLeaderExpansion

/-- k actual upper cuts, from rank m+k+3 down to rank m+3. -/
noncomputable def alignedInput : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, t => t
  | k+1, m, c, t => alignedInput k m c (kernel (m+k+4) (c+m+k+4) t)
noncomputable def upperEntries : Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _ => []
  | k+1, m, c, t => (m+k+4,t) :: upperEntries k m c (kernel (m+k+4) (c+m+k+4) t)
noncomputable def upperResiduals (k m c t : Nat) : List Nat :=
  (upperEntries k m c t).map (fun p => count p.1 (c+p.1) p.2)

end LogicLineages.OrdinalComparison.CounterLeaderCollision
