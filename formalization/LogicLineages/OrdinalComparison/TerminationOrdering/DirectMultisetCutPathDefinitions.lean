module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationProof
public import Mathlib.Logic.Hydra
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPath

/-- Forward source-to-target path; each library edge takes target before source. -/
inductive CutPath {α : Type} (R : α → α → Prop) : Nat → Multiset α → Multiset α → Prop where
  | refl (source : Multiset α) : CutPath R 0 source source
  | cons {k : Nat} {source middle target : Multiset α} :
      Relation.CutExpand (fun successor source => R source successor) middle source →
      CutPath R k middle target → CutPath R (k+1) source target

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPath
