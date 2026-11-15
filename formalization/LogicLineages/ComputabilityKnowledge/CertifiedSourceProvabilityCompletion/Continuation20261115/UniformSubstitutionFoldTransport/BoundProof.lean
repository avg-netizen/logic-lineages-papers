module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.BoundProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph InvariantProof

def allResults {ctx : Nat} (ftag vtag stag ptag len q l r : Nat) (tokens start raw oldTasks current out : Term ctx) : Formula ctx :=
 .all (property ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (liftTerm current) (liftTerm out) (.var 0))
theorem substAllResults {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag len q l r (tokens start raw oldTasks current out : Term m) :
 substituteFormula s (allResults ftag vtag stag ptag len q l r tokens start raw oldTasks current out) = allResults ftag vtag stag ptag len q l r (substitute s tokens) (substitute s start) (substitute s raw) (substitute s oldTasks) (substitute s current) (substitute s out) := by
 simp only [allResults,substituteFormula,substProperty,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allResultsInstance {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r (tokens start raw oldTasks current out oldResult : Term ctx) :
 Derivation T (.imp (allResults ftag vtag stag ptag len q l r tokens start raw oldTasks current out) (property ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (property ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (liftTerm current) (liftTerm out) (.var 0)) oldResult)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allResults] using h

def allOutputs {ctx : Nat} (ftag vtag stag ptag len q l r : Nat) (tokens start raw oldTasks current : Term ctx) : Formula ctx :=
 .all (allResults ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (liftTerm current) (.var 0))
theorem substAllOutputs {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag len q l r (tokens start raw oldTasks current : Term m) :
 substituteFormula s (allOutputs ftag vtag stag ptag len q l r tokens start raw oldTasks current) = allOutputs ftag vtag stag ptag len q l r (substitute s tokens) (substitute s start) (substitute s raw) (substitute s oldTasks) (substitute s current) := by
 simp only [allOutputs,substituteFormula,substAllResults,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allOutputsInstance {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r (tokens start raw oldTasks current out : Term ctx) :
 Derivation T (.imp (allOutputs ftag vtag stag ptag len q l r tokens start raw oldTasks current) (allResults ftag vtag stag ptag len q l r tokens start raw oldTasks current out)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allResults ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (liftTerm current) (.var 0)) out)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllResults,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allOutputs] using h

def allCurrent {ctx : Nat} (ftag vtag stag ptag len q l r : Nat) (tokens start raw oldTasks : Term ctx) : Formula ctx :=
 .all (allOutputs ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (.var 0))
theorem substAllCurrent {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag len q l r (tokens start raw oldTasks : Term m) :
 substituteFormula s (allCurrent ftag vtag stag ptag len q l r tokens start raw oldTasks) = allCurrent ftag vtag stag ptag len q l r (substitute s tokens) (substitute s start) (substitute s raw) (substitute s oldTasks) := by
 simp only [allCurrent,substituteFormula,substAllOutputs,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allCurrentInstance {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r (tokens start raw oldTasks current : Term ctx) :
 Derivation T (.imp (allCurrent ftag vtag stag ptag len q l r tokens start raw oldTasks) (allOutputs ftag vtag stag ptag len q l r tokens start raw oldTasks current)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allOutputs ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (liftTerm oldTasks) (.var 0)) current)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllOutputs,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allCurrent] using h

def allStates {ctx : Nat} (ftag vtag stag ptag len q l r : Nat) (tokens start raw : Term ctx) : Formula ctx :=
 .all (allCurrent ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (.var 0))
theorem substAllStates {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag len q l r (tokens start raw : Term m) :
 substituteFormula s (allStates ftag vtag stag ptag len q l r tokens start raw) = allStates ftag vtag stag ptag len q l r (substitute s tokens) (substitute s start) (substitute s raw) := by
 simp only [allStates,substituteFormula,substAllCurrent,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allStatesInstance {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r (tokens start raw oldTasks : Term ctx) :
 Derivation T (.imp (allStates ftag vtag stag ptag len q l r tokens start raw) (allCurrent ftag vtag stag ptag len q l r tokens start raw oldTasks)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allCurrent ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw) (.var 0)) oldTasks)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllCurrent,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allStates] using h

def bounded {ctx : Nat} (ftag vtag stag ptag len q l r : Nat) (bound start raw : Term ctx) : Formula ctx :=
 .all (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
  (allStates ftag vtag stag ptag len q l r (.var 0) (liftTerm start) (liftTerm raw)))
theorem substBounded {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag len q l r (bound start raw : Term m) :
 substituteFormula s (bounded ftag vtag stag ptag len q l r bound start raw) =
 bounded ftag vtag stag ptag len q l r (substitute s bound) (substitute s start) (substitute s raw) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substAllStates,
  HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r
 (tokens start raw oldTasks current out oldResult : Term ctx) :
 Derivation T (.imp (allStates ftag vtag stag ptag len q l r tokens start raw)
  (property ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult)) :=
 Hilbert.compose (allResultsInstance ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult)
  (Hilbert.compose (allOutputsInstance ftag vtag stag ptag len q l r tokens start raw oldTasks current out)
   (Hilbert.compose (allCurrentInstance ftag vtag stag ptag len q l r tokens start raw oldTasks current)
    (allStatesInstance ftag vtag stag ptag len q l r tokens start raw oldTasks)))
noncomputable def boundedInstance {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r (bound tokens start raw : Term ctx) :
 Derivation T (.imp (bounded ftag vtag stag ptag len q l r bound start raw)
  (.imp (HistoryBounds.weakBound tokens bound) (allStates ftag vtag stag ptag len q l r tokens start raw))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
   (allStates ftag vtag stag ptag len q l r (.var 0) (liftTerm start) (liftTerm raw))) tokens)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substAllStates,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,bounded] using h
noncomputable def transportAll {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r (a b start raw : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (allStates ftag vtag stag ptag len q l r a start raw) (allStates ftag vtag stag ptag len q l r b start raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (allStates ftag vtag stag ptag len q l r (.var 0) (liftTerm start) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllStates,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.BoundProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.BoundProof
