module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchTargets
open PolynomialGraphCompletion CanonicalGuardSelector GuardChildMeasureCompletion

/-- Semantic correctness of the actual selected child for arbitrary admitted
words. All original, prepared and generated domains are conclusions. There
is no comparison oracle, supplied semantic case, or ordered-raw-input premise. -/
def DispatchCorrect : Prop := ∀ (D : Nat) (A B : Word) (q : Choice),
  WordAllowed D A → WordAllowed D B → selectWords A B = some q →
  ∀ x y : Nat, dispatchTail A B ≤ x → dispatchTail A B ≤ y →
    WordDomain A x ∧ WordDomain B y ∧
    WordDomain (preparedWord A) x ∧ WordDomain (preparedWord B) y ∧
    WordDomain q.2.2.1 x ∧ WordDomain q.2.2.2 y ∧
    orderNat (wordValue A x) (wordValue B y) =
      liftTie (dispatchTie A B) (orderNat (wordValue q.2.2.1 x) (wordValue q.2.2.2 y))

/-- The same literal selector supplies the admitted child and actual
histogram decrease against the original, unprepared word pair. -/
def DispatchChild : Prop := ∀ (D : Nat) (A B : Word) (q : Choice),
  WordAllowed D A → WordAllowed D B → selectWords A B = some q →
    GuardCase D q.1 q.2.1 q.2.2 (preparedWord A,preparedWord B) ∧
    ChildDecrease D q.2.2 (A,B) ∧
    WordAllowed D q.2.2.1 ∧ WordAllowed D q.2.2.2

/-- Every total numeric tie output is one of LT=0, EQ=1, GT=2, including
the unclaimed malformed-input branches. -/
def DispatchTieBound : Prop := ∀ A B : Word, dispatchTie A B ≤ 2

/-- Primitive recursiveness of the literal finite dispatcher, before the
later unbounded but terminating recursive comparison compilation. -/
def DispatchPrograms : Prop :=
  Primrec (fun p : Word × Word => dispatchTail p.1 p.2) ∧
  Primrec (fun p : Word × Word => dispatchTie p.1 p.2)

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchTargets
