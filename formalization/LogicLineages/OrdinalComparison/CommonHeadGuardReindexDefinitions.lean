module
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsDefinitions
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadGuardReindex
open CommonHeadLargeGuards

def rename (σ : Nat → Nat) : Formula → Formula
  | .truth => .truth | .falsity => .falsity
  | .eq i j => .eq (σ i) (σ j) | .lt i j => .lt (σ i) (σ j)
  | .bound c i => .bound c (σ i)
  | .conj p q => .conj (rename σ p) (rename σ q)
  | .disj p q => .disj (rename σ p) (rename σ q)
  | .neg p => .neg (rename σ p)

/-- Reinsert the deleted original occurrence index; all other labels retain identity. -/
def skip (i j : Nat) : Nat := if j < i then j else j+1

def equalConstant (i c : Nat) : Formula :=
  .conj (.bound c i) (.neg (.bound (c+1) i))

def guarded (i c : Nat) (p : Formula) : Formula :=
  .conj (equalConstant i c) (rename (skip i) p)
end LogicLineages.OrdinalComparison.CommonHeadGuardReindex
