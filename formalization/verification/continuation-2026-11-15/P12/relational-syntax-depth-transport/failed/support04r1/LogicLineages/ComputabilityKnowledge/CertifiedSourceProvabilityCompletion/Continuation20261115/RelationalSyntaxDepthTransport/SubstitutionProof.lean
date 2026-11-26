module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.SubstitutionProof
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution GorbowPRDefiningEquations SixSol20261113 SixSol20261112.Fuel List.Vector

theorem substTask {m n : Nat} (s : Fin m → Term n) leftTag rightTag (a b : Term m) :
 substituteFormula s (taskRelation leftTag rightTag a b) =
 taskRelation leftTag rightTag (substitute s a) (substitute s b) := by
 simp only [taskRelation,substituteFormula,HistoryBounds.SupportProof.substWeak,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem substEntry {m n : Nat} (s : Fin m → Term n) lookupTag leftTag rightTag (a b i : Term m) :
 substituteFormula s (entryRelation lookupTag leftTag rightTag a b i) =
 entryRelation lookupTag leftTag rightTag (substitute s a) (substitute s b) (substitute s i) := by
 simp only [entryRelation,substituteFormula,HistoryLookup.lookupCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  HistoryOrder.SupportProof.substituteLift,substTask,substitute,liftSubstitute,Fin.cases_zero,Fin.cases_succ]
 rfl

theorem substStack {m n : Nat} (s : Fin m → Term n) lengthTag lookupTag leftTag rightTag (a b : Term m) :
 substituteFormula s (stackRelation lengthTag lookupTag leftTag rightTag a b) =
 stackRelation lengthTag lookupTag leftTag rightTag (substitute s a) (substitute s b) := by
 simp only [stackRelation,substituteFormula,HistoryLengthOffset.lengthCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substEntry,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.SubstitutionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.SubstitutionProof
