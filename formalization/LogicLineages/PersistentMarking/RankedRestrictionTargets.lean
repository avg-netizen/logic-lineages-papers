import LogicLineages.PersistentMarking.Comparison
import LogicLineages.PersistentMarking.ConfinedPair

namespace LogicLineages.PersistentMarking.RankedRestrictionTargets
open Spine

def RankedHead : Head → Prop
  | .ranked _ _ => True
  | _ => False

mutual
def Ranked : Expr → Prop
  | .free .ground _ => True
  | .head f bs => RankedHead f ∧ RankedArgs bs
  | _ => False

def RankedArgs : Args → Prop
  | .nil => True
  | .cons q qs => Ranked q ∧ RankedArgs qs
end

def Term (S : Signature) (q : Expr) : Prop := PaperTerm S q .ground ∧ Ranked q

mutual
inductive Equal : Expr → Expr → Prop where
  | var : Equal (.free .ground x) (.free .ground x)
  | head : EqMatch bs ts → Equal (.head f bs) (.head f ts)

inductive EqMatch : Args → Args → Prop where
  | nil : EqMatch .nil .nil
  | cons : Remove ts t rest → Equal q t → EqMatch qs rest → EqMatch (.cons q qs) ts
end

/- Multiset recursive path ordering, with the explicit domination
requirements on target arguments and recursive multiset equality
on the retained occurrences. -/
mutual
inductive RPO (S : Signature) : Expr → Expr → Prop where
  | subtermEq : At bs i u → Equal u t → RPO S (.head f bs) t
  | subtermStrict : At bs i u → RPO S u t → RPO S (.head f bs) t
  | precedence : Precedes S f g → Dominates S (.head f bs) ts → RPO S (.head f bs) (.head g ts)
  | multiset : Split bs kept removed → Split ts matched added → Nonempty removed →
      EqMatch kept matched → RPOCoverage S removed added → Dominates S (.head f bs) ts →
      RPO S (.head f bs) (.head f ts)

inductive RPOCoverage (S : Signature) : Args → Args → Prop where
  | nil : RPOCoverage S removed .nil
  | cons : At removed i q → RPO S q t → RPOCoverage S removed ts → RPOCoverage S removed (.cons t ts)

inductive Dominates (S : Signature) : Expr → Args → Prop where
  | nil : Dominates S q .nil
  | cons : RPO S q t → Dominates S q ts → Dominates S q (.cons t ts)
end

def ExactRankedRestriction : Prop := ∀ S s t, Term S s → Term S t →
  (ConfinedPair.Strict S s t ↔ RPO S s t) ∧
  (ConfinedPair.Weak S s t ↔ RPO S s t ∨ Equal s t)

end LogicLineages.PersistentMarking.RankedRestrictionTargets
