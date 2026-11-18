import LogicLineages.PersistentMarking.Syntax

namespace LogicLineages.PersistentMarking.MarkingTargets
open Term

def Persistent : Prop := ∀ s t : Term, mark s = some t → mark t = some t
def TotalIdempotent : Prop := ∀ s : Term, headmark (headmark s) = headmark s
def SuccessAgrees : Prop := ∀ s t : Term, mark s = some t → headmark s = t
def FailureExact : Prop := ∀ s : Term, mark s = none ↔ variableSpine s = true
def TypePreserved : Prop := ∀ s t : Term, mark s = some t → type t = type s
def TotalTypePreserved : Prop := ∀ s : Term, type (headmark s) = type s
end LogicLineages.PersistentMarking.MarkingTargets
