module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderExpansion

noncomputable def count (h c t : Nat) : Nat :=
  actualSuffixKernelCount (Ordinal.omega0 ^ (h : Ordinal)) c t
noncomputable def kernel (h c t : Nat) : Nat :=
  actualSuffixKernel (Ordinal.omega0 ^ (h : Ordinal)) c t

/-- n encodes rank r=n+3. The list retains the original descending rank order. -/
noncomputable def entries : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, t => [(3, t)]
  | n+1, c, t => (n+4, t) :: entries n c (kernel (n+4) (c+n+4) t)
noncomputable def bottomInput : Nat → Nat → Nat → Nat
  | 0, _, t => t
  | n+1, c, t => bottomInput n c (kernel (n+4) (c+n+4) t)
noncomputable def leaderPreimage (n c t : Nat) : Nat :=
  kernel 3 (c+3) (bottomInput n c t)
noncomputable def leader (n c t : Nat) : Nat := Phi (leaderPreimage n c t)
noncomputable def residuals (n c t : Nat) : List Nat :=
  (entries n c t).map (fun p => count p.1 (c+p.1) p.2)

/-- Explicit sufficient original-source tail for every unsigned block cut. -/
def threshold (n c : Nat) : Nat := c + 2*(n+3) + 1

end LogicLineages.OrdinalComparison.CounterLeaderExpansion
