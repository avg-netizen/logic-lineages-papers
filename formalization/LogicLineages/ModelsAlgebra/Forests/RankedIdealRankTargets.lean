module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRankDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRank.Targets
open ProfileAutomatonEncoding RankedIdealFinite RankedIdealComponents RankedIdealCompletion
 def ReachReflexive : Prop := ∀ (M : Machine) [DecidableEq M.State] q, q ∈ close M {q}
 def ReachTransitive : Prop := ∀ (M : Machine) [DecidableEq M.State] p q r,
   q ∈ close M {p} → r ∈ close M {q} → r ∈ close M {p}
 def ComponentRank : Prop := ∀ (M : Machine) [DecidableEq M.State] p q,
   SameComponent M p q → rank M p = rank M q
 def LowerRank : Prop := ∀ (M : Machine) [DecidableEq M.State] p q,
   Lower M p q → rank M p < rank M q
 def PredecessorCases : Prop := ∀ (M : Machine) [DecidableEq M.State] p q,
   q ∈ close M {p} → SameComponent M p q ∨ Lower M p q
 def LinearChildren : Prop := ∀ (M : Machine) [DecidableEq M.State] q o x y,
   ¬NonlinearAt M q → x ∈ productive M → y ∈ productive M →
   SameComponent M q (M.node o x y) →
   (Lower M x q ∧ Lower M y q) ∨
   (SameComponent M q x ∧ Lower M y q) ∨
   (Lower M x q ∧ SameComponent M q y)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRank.Targets
