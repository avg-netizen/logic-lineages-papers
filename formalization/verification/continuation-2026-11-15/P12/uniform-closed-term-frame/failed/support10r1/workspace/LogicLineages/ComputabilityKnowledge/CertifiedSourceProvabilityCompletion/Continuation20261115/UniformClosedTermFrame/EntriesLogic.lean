module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesLogic
open GorbowSyntax GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Original option-coded lookup is NONE or exactly the specified task. The
all-index quantifier includes out-of-range positions; no native list domain. -/
def entry {ctx : Nat} (q : Nat) (value tasks index : Term ctx) : Formula ctx :=
 .disj (.equal (HistoryLookup.lookupCall q index tasks) .zero)
  (.equal (HistoryLookup.lookupCall q index tasks) (.succ value))
def entries {ctx : Nat} (q : Nat) (value tasks : Term ctx) : Formula ctx :=
 .all (entry q (liftTerm value) (liftTerm tasks) (.var 0))
theorem substEntry {m n : Nat} (s : Fin m → Term n) q (value tasks index : Term m) :
 substituteFormula s (entry q value tasks index) =
 entry q (substitute s value) (substitute s tasks) (substitute s index) := by
 simp only [entry,substituteFormula,HistoryLookup.lookupCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem substEntries {m n : Nat} (s : Fin m → Term n) q (value tasks : Term m) :
 substituteFormula s (entries q value tasks) = entries q (substitute s value) (substitute s tasks) := by
 simp only [entries,substituteFormula,substEntry,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem instanceEntry {ctx : Nat} q (value tasks index : Term ctx) :
 GorbowStandardInstances.instantiate (entry q (liftTerm value) (liftTerm tasks) (.var 0)) index = entry q value tasks index := by
 simp only [GorbowStandardInstances.instantiate,substEntry,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def eliminate {T : Sentence → Prop} {ctx : Nat} q (value tasks index : Term ctx) :
 Derivation T (.imp (entries q value tasks) (entry q value tasks index)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (entry q (liftTerm value) (liftTerm tasks) (.var 0)) index)
 simpa only [GorbowPACore.logicalFormula,entries,instanceEntry] using h
noncomputable def transportIndex {T : Sentence → Prop} {ctx : Nat} q (value tasks a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (entry q value tasks a) (entry q value tasks b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (entry q (liftTerm value) (liftTerm tasks) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,instanceEntry] using h
noncomputable def transportTasks {T : Sentence → Prop} {ctx : Nat} q (value a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (entries q value a) (entries q value b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (entries q (liftTerm value) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substEntries,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
/-- Congruence on actual option-coded lookup results, not a list cast. -/
noncomputable def optionTransport {T : Sentence → Prop} {ctx : Nat} (value a b : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (.disj (.equal a .zero) (.equal a (.succ value)))
   (.disj (.equal b .zero) (.equal b (.succ value))))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (.disj (.equal (.var 0) .zero) (.equal (.var 0) (.succ (liftTerm value)))) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesLogic
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesLogic
