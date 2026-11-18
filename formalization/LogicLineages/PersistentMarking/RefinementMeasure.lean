import LogicLineages.PersistentMarking.Refinement
namespace LogicLineages.PersistentMarking.RefinementMeasure
open Spine

/- Constructor count of actual finite witnesses. Every base, extra list and
whole-owner premise contributes; endpoint annotations and names do not. -/
mutual
 def treeSize {S q s} : RefinementTree S q s → Nat
   | .var => 1
   | .abs _ _ _ _ h => 1 + treeSize h
   | .head _ _ h => 1 + basesSize h
   | .marked _ _ hb he => 1 + basesSize hb + extrasSize he
 def basesSize {S qs ss} : RefinementBasesTree S qs ss → Nat
   | .nil => 1
   | .cons h hs => 1 + treeSize h + basesSize hs
 def extraSize {S f base extras q} : RefinementExtraTree S f base extras q → Nat
   | .existing _ h => 1 + treeSize h
   | .owner h => 1 + treeSize h
 def extrasSize {S f base extras qs} : RefinementExtrasTree S f base extras qs → Nat
   | .nil => 1
   | .cons h hs => 1 + extraSize h + extrasSize hs
end

end LogicLineages.PersistentMarking.RefinementMeasure
