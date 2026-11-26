import LogicLineages.PersistentMarking.RankedRestrictionSyntaxProof
import LogicLineages.PersistentMarking.RankedRestrictionMatchingProof

namespace LogicLineages.PersistentMarking.RankedRestrictionForwardTargets
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof RankedRestrictionMatchingProof

def OrdinaryMotive (S : Signature) (q t : Expr) : Prop :=
  RankedTerm S q → RankedTerm S t → RPO S q t ∨ Equal q t

def MarkedMotive (S : Signature) (q t : Expr) : Prop :=
  ∀ f bs, q = .marked f .ground bs .nil → RankedTerm S (.head f bs) → RankedTerm S t → RPO S (.head f bs) t

def WeakMotive (S : Signature) (q t : Expr) : Prop :=
  OrdinaryMotive S q t ∧ MarkedMotive S q t

def StrictMotive (S : Signature) (q t : Expr) : Prop := RankedTerm S q → RankedTerm S t → RPO S q t

def MatchingMotive (S : Signature) (qs ts : Args) : Prop :=
  ArgsTerm S qs → ArgsTerm S ts → WeakMatch S qs ts

def MultisetMotive (S : Signature) (qs ts : Args) : Prop :=
  ArgsTerm S qs → ArgsTerm S ts → Replacement S qs ts

def CoverageMotive (S : Signature) (qs ts : Args) : Prop :=
  ArgsTerm S qs → ArgsTerm S ts → RPOCoverage S qs ts

def WholeMotive (S : Signature) (f : Head) (bs es ts : Args) : Prop :=
  es = .nil → RankedTerm S (.head f bs) → ArgsTerm S ts → Dominates S (.head f bs) ts

end LogicLineages.PersistentMarking.RankedRestrictionForwardTargets
