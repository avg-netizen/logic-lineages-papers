module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.SubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelationLogicProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open SubstitutionProof

def witnessBody {ctx : Nat} (lookupTag leftTag rightTag : Nat) (b i t : Term ctx) : Formula (ctx+1) :=
 .conj (.equal (HistoryLookup.lookupCall lookupTag (liftTerm i) (liftTerm b)) (.succ (.var 0)))
  (taskRelation leftTag rightTag (liftTerm t) (.var 0))
def witness {ctx : Nat} (lookupTag leftTag rightTag : Nat) (b i t : Term ctx) : Formula ctx :=
 .ex (witnessBody lookupTag leftTag rightTag b i t)
def entryBody {ctx : Nat} (lookupTag leftTag rightTag : Nat) (a b i t : Term ctx) : Formula ctx :=
 .imp (.equal (HistoryLookup.lookupCall lookupTag i a) (.succ t))
  (witness lookupTag leftTag rightTag b i t)
theorem substWitness {m n : Nat} (s : Fin m → Term n) q l r (b i t : Term m) :
 substituteFormula s (witness q l r b i t) = witness q l r (substitute s b) (substitute s i) (substitute s t) := by
 simp only [witness,witnessBody,substituteFormula,HistoryLookup.lookupCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,HistoryOrder.SupportProof.substituteLift,substTask,
  substitute,liftSubstitute,Fin.cases_zero]
theorem substBody {m n : Nat} (s : Fin m → Term n) q l r (a b i t : Term m) :
 substituteFormula s (entryBody q l r a b i t) =
 entryBody q l r (substitute s a) (substitute s b) (substitute s i) (substitute s t) := by
 simp only [entryBody,substituteFormula,substWitness,HistoryLookup.lookupCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
noncomputable def taskRight {T : Sentence → Prop} {ctx : Nat} l r (t a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (taskRelation l r t a) (taskRelation l r t b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (taskRelation l r (liftTerm t) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substTask,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} len q l r (a b i t : Term ctx) :
 Derivation T (.imp (stackRelation len q l r a b) (entryBody q l r a b i t)) := by
 have h1 := Derivation.logical (A := T) (.allInstantiate
  (entryRelation q l r (liftTerm a) (liftTerm b) (.var 0)) i)
 have h1' : Derivation T (.imp (.all (entryRelation q l r (liftTerm a) (liftTerm b) (.var 0)))
  (entryRelation q l r a b i)) := by
  simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substEntry,
   substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h1
 have h2 := Derivation.logical (A := T) (.allInstantiate
  (entryBody q l r (liftTerm a) (liftTerm b) (liftTerm i) (.var 0)) t)
 have h2' : Derivation T (.imp (entryRelation q l r a b i) (entryBody q l r a b i t)) := by
  simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substBody,
   substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h2
 exact Hilbert.compose h2' (Hilbert.compose h1' (.logical (.andRight _ _)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelationLogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.RelationLogicProof
