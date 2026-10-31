module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback.Targets
open CotreePresburger

def WordCountsEqCount : Prop :=
  ∀ (A : Type) [DecidableEq A] [BEq A] [LawfulBEq A] (xs : List A) a,
    wordCounts xs a = xs.count a

def PushWordCountsExact : Prop :=
  ∀ (Q R : Type) [DecidableEq Q] [Fintype R] [DecidableEq R]
    (f : R → Q) (xs : List R) q,
    pushCounts f (wordCounts xs) q = wordCounts (xs.map f) q

def PullFormulaExact : Prop :=
  ∀ (Q R : Type) [DecidableEq Q] [Fintype R] [LinearOrder R]
    (f : R → Q) (φ : PFormula Q) (counts : R → Nat),
    (pullFormula f φ).Realize counts ↔ φ.Realize (pushCounts f counts)

def PullWordExact : Prop :=
  ∀ (Q R : Type) [DecidableEq Q] [Fintype R] [LinearOrder R]
    (f : R → Q) (φ : PFormula Q) (xs : List R),
    (pullFormula f φ).Realize (wordCounts xs) ↔ φ.Realize (wordCounts (xs.map f))

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback.Targets
