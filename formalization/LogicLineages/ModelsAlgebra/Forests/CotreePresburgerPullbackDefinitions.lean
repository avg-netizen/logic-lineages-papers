module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjectionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback
open FirstOrder Language CotreePresburger

/-- Canonical occurrence counts use explicit decidable equality, independently
of any separately installed concrete `BEq` instance on a product state type. -/
def wordCounts {A : Type} [DecidableEq A] (xs : List A) (a : A) : Nat :=
  xs.countP (fun x => decide (x = a))

/-- Linear projection of a finite count vector along a finite state map. -/
def pushCounts {Q R : Type} [DecidableEq Q] [Fintype R]
    (f : R → Q) (counts : R → Nat) (q : Q) : Nat :=
  ∑ r, if f r = q then counts r else 0

/-- Actual finite linear term, not an opaque semantic substitution. -/
def pullTerm {Q R : Type} [DecidableEq Q] [Fintype R] [LinearOrder R]
    (f : R → Q) (q : Q) : PTerm R :=
  sumAll (fun r : R => if f r = q then .var r else 0)

/-- Actual Presburger syntax for projecting enriched/product-state counts.
All enumeration and term substitution are executable. -/
def pullFormula {Q R : Type} [DecidableEq Q] [Fintype R] [LinearOrder R]
    (f : R → Q) (φ : PFormula Q) : PFormula R :=
  φ.subst (pullTerm f)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback
