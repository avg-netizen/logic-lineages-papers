module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.BoundProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph InvariantProof

def allOutputs {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat) (tokens raw oldTasks newTasks rest : Term ctx) : Formula ctx :=
 .all (property ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (liftTerm newTasks) (liftTerm rest) (.var 0))
theorem substAllOutputs {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r (tokens raw oldTasks newTasks rest : Term m) :
 substituteFormula s (allOutputs ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest) = allOutputs ftag stag ptag ctag atag len q l r (substitute s tokens) (substitute s raw) (substitute s oldTasks) (substitute s newTasks) (substitute s rest) := by
 simp only [allOutputs,substituteFormula,substProperty,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allOutputsInstance {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r (tokens raw oldTasks newTasks rest out : Term ctx) :
 Derivation T (.imp (allOutputs ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest) (property ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (property ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (liftTerm newTasks) (liftTerm rest) (.var 0)) out)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allOutputs] using h

def allRests {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat) (tokens raw oldTasks newTasks : Term ctx) : Formula ctx :=
 .all (allOutputs ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (liftTerm newTasks) (.var 0))
theorem substAllRests {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r (tokens raw oldTasks newTasks : Term m) :
 substituteFormula s (allRests ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks) = allRests ftag stag ptag ctag atag len q l r (substitute s tokens) (substitute s raw) (substitute s oldTasks) (substitute s newTasks) := by
 simp only [allRests,substituteFormula,substAllOutputs,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allRestsInstance {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r (tokens raw oldTasks newTasks rest : Term ctx) :
 Derivation T (.imp (allRests ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks) (allOutputs ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allOutputs ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (liftTerm newTasks) (.var 0)) rest)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllOutputs,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allRests] using h

def allPrefixes {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat) (tokens raw oldTasks : Term ctx) : Formula ctx :=
 .all (allRests ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (.var 0))
theorem substAllPrefixes {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r (tokens raw oldTasks : Term m) :
 substituteFormula s (allPrefixes ftag stag ptag ctag atag len q l r tokens raw oldTasks) = allPrefixes ftag stag ptag ctag atag len q l r (substitute s tokens) (substitute s raw) (substitute s oldTasks) := by
 simp only [allPrefixes,substituteFormula,substAllRests,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allPrefixesInstance {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r (tokens raw oldTasks newTasks : Term ctx) :
 Derivation T (.imp (allPrefixes ftag stag ptag ctag atag len q l r tokens raw oldTasks) (allRests ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allRests ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (liftTerm oldTasks) (.var 0)) newTasks)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllRests,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allPrefixes] using h

def allStates {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat) (tokens raw : Term ctx) : Formula ctx :=
 .all (allPrefixes ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (.var 0))
theorem substAllStates {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r (tokens raw : Term m) :
 substituteFormula s (allStates ftag stag ptag ctag atag len q l r tokens raw) = allStates ftag stag ptag ctag atag len q l r (substitute s tokens) (substitute s raw) := by
 simp only [allStates,substituteFormula,substAllPrefixes,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allStatesInstance {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r (tokens raw oldTasks : Term ctx) :
 Derivation T (.imp (allStates ftag stag ptag ctag atag len q l r tokens raw) (allPrefixes ftag stag ptag ctag atag len q l r tokens raw oldTasks)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allPrefixes ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (.var 0)) oldTasks)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllPrefixes,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allStates] using h

def bounded {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat) (bound raw : Term ctx) : Formula ctx :=
 .all (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
  (allStates ftag stag ptag ctag atag len q l r (.var 0) (liftTerm raw)))
theorem substBounded {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r (bound raw : Term m) :
 substituteFormula s (bounded ftag stag ptag ctag atag len q l r bound raw) =
 bounded ftag stag ptag ctag atag len q l r (substitute s bound) (substitute s raw) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substAllStates,
  HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r
 (tokens raw oldTasks newTasks rest out : Term ctx) :
 Derivation T (.imp (allStates ftag stag ptag ctag atag len q l r tokens raw)
  (property ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out)) :=
 Hilbert.compose (allOutputsInstance ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out)
  (Hilbert.compose (allRestsInstance ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest)
   (Hilbert.compose (allPrefixesInstance ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks)
    (allStatesInstance ftag stag ptag ctag atag len q l r tokens raw oldTasks)))
noncomputable def boundedInstance {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r (bound tokens raw : Term ctx) :
 Derivation T (.imp (bounded ftag stag ptag ctag atag len q l r bound raw)
  (.imp (HistoryBounds.weakBound tokens bound) (allStates ftag stag ptag ctag atag len q l r tokens raw))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
   (allStates ftag stag ptag ctag atag len q l r (.var 0) (liftTerm raw))) tokens)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substAllStates,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,bounded] using h
noncomputable def transportAll {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r (a b raw : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (allStates ftag stag ptag ctag atag len q l r a raw) (allStates ftag stag ptag ctag atag len q l r b raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (allStates ftag stag ptag ctag atag len q l r (.var 0) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllStates,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.BoundProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.BoundProof
