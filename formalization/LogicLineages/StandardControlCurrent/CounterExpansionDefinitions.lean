module
public import LogicLineages.StandardControlCurrent.NumericalKernelDefinitions
public import LogicLineages.OrdinalComparison.CounterSourceTheoremDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CounterExpansion
open OrdinalComparison NumericalKernel
noncomputable def entries : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, t => [(3,t)]
  | n+1,c,t => (n+4,t)::entries n c (value (n+4) (c+n+4) t)
noncomputable def bottomInput : Nat → Nat → Nat → Nat
  | 0,_,t => t
  | n+1,c,t => bottomInput n c (value (n+4) (c+n+4) t)
noncomputable def leaderPreimage (n c t : Nat) : Nat := value 3 (c+3) (bottomInput n c t)
noncomputable def leader (n c t : Nat) : Nat := Phi (leaderPreimage n c t)
noncomputable def residuals (n c t : Nat) : List Nat :=
  (entries n c t).map (fun p => count p.1 (c+p.1) p.2)
noncomputable def alignedInput : Nat → Nat → Nat → Nat → Nat
  | 0,_,_,t => t
  | k+1,m,c,t => alignedInput k m c (value (m+k+4) (c+m+k+4) t)
noncomputable def upperEntries : Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_,_ => []
  | k+1,m,c,t => (m+k+4,t)::upperEntries k m c (value (m+k+4) (c+m+k+4) t)
noncomputable def upperResiduals (k m c t : Nat) : List Nat :=
  (upperEntries k m c t).map (fun p => count p.1 (c+p.1) p.2)
end LogicLineages.StandardControlCurrent.CounterExpansion
