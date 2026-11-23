module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedComparison

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedMeasure
open Spine

/- Count every actual recursive comparison/list witness. Propositional typing,
occurrence, permutation and prefix premises are retained in the constructors;
only the finite judgment-tree nodes form this induction measure. -/
def treeSize {S j} : ExtendedTree S j → Nat
  | .var => 1
  | .abs _ _ _ _ h => 1 + treeSize h
  | .funHead _ _ _ _ h => 1 + treeSize h
  | .put _ _ h => 1 + treeSize h
  | .select _ _ _ _ _ h => 1 + treeSize h
  | .fabs _ _ _ _ h => 1 + treeSize h
  | .copy _ _ _ h => 1 + treeSize h
  | .stat _ _ _ hm hw => 1 + treeSize hm + treeSize hw
  | .inHead _ _ _ hm ho => 1 + treeSize hm + treeSize ho
  | .marked1 _ _ _ hb he => 1 + treeSize hb + treeSize he
  | .marked2 _ _ _ hm hb he => 1 + treeSize hm + treeSize hb + treeSize he
  | .drop _ _ h => 1 + treeSize h
  | .perm _ _ _ h => 1 + treeSize h
  | .copies _ _ _ h => 1 + treeSize h
  | .pselect _ _ _ _ _ _ h => 1 + treeSize h
  | .strictIntro _ _ _ h => 1 + treeSize h
  | .matchingNil => 1
  | .matchingCons _ h hs => 1 + treeSize h + treeSize hs
  | .multisetReplace _ _ _ hm hc => 1 + treeSize hm + treeSize hc
  | .coverageNil => 1
  | .coverageCons _ h hs => 1 + treeSize h + treeSize hs
  | .wholeNil => 1
  | .wholeCons h hs => 1 + treeSize h + treeSize hs
  | .orderedNil => 1
  | .orderedCons h hs => 1 + treeSize h + treeSize hs
end LogicLineages.PersistentMarking.ExtendedMeasure
