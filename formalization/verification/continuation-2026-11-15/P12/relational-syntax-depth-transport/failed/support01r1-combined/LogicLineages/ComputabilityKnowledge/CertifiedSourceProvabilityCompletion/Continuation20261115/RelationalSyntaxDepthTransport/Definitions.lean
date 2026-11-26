module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport
open GorbowSyntax GorbowPRDefiningEquations SixSol20261113 SixSol20261112.Fuel List.Vector
/-- Same original task kind, with an internally witnessed increase in its bound. -/
def taskRelation {ctx : Nat} (leftTag rightTag : Nat) (a b : Term ctx) : Formula ctx :=
 .conj (.equal (call leftTag (a ::ᵥ nil)) (call leftTag (b ::ᵥ nil)))
  (HistoryBounds.weakBound (call rightTag (a ::ᵥ nil)) (call rightTag (b ::ᵥ nil)))
/-- Aligned actual SOME lookup entries; no native list image is assumed. -/
def entryRelation {ctx : Nat} (lookupTag leftTag rightTag : Nat)
 (a b index : Term ctx) : Formula ctx :=
 .all (.imp (.equal (HistoryLookup.lookupCall lookupTag (liftTerm index) (liftTerm a)) (.succ (.var 0)))
  (.ex (.conj
   (.equal (HistoryLookup.lookupCall lookupTag (liftTerm (liftTerm index)) (liftTerm (liftTerm b))) (.succ (.var 0)))
   (taskRelation leftTag rightTag (.var 1) (.var 0)))))
/-- Equal actual lengths and pointwise related task entries. All function calls
refer to original installed scanner/list primitives, never a new stack-map AST. -/
def stackRelation {ctx : Nat} (lengthTag lookupTag leftTag rightTag : Nat) (a b : Term ctx) : Formula ctx :=
 .conj (.equal (HistoryLengthOffset.lengthCall lengthTag a) (HistoryLengthOffset.lengthCall lengthTag b))
  (.all (entryRelation lookupTag leftTag rightTag (liftTerm a) (liftTerm b) (.var 0)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport
