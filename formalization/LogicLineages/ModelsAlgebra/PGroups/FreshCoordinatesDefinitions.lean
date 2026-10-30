module
public import Mathlib.Data.Nat.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

def reserveEven (M n : ℕ) : ℕ := if n < M then n else M + 2 * (n-M)
def reserveOdd (M n : ℕ) : ℕ := M + 2*n + 1

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
