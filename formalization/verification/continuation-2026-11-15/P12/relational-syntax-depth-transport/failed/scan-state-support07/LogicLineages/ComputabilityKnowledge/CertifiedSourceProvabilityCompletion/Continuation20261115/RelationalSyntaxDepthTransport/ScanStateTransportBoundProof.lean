module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportBoundProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph
open ScanStateTransportSupportProof
/-- All changing result and BOTH stack coordinates are quantified internally. -/
def allResults {ctx : Nat} (itag len ptag q l r : Nat) (raw ot nt : Term ctx) : Formula ctx :=
 .all (property itag len ptag q l r (liftTerm raw) (liftTerm ot) (liftTerm nt) (.var 0))
def allNew {ctx : Nat} (itag len ptag q l r : Nat) (raw ot : Term ctx) : Formula ctx :=
 .all (allResults itag len ptag q l r (liftTerm raw) (liftTerm ot) (.var 0))
def allStacks {ctx : Nat} (itag len ptag q l r : Nat) (raw : Term ctx) : Formula ctx :=
 .all (allNew itag len ptag q l r (liftTerm raw) (.var 0))
def bounded {ctx : Nat} (itag len ptag q l r : Nat) (bound : Term ctx) : Formula ctx :=
 .all (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
  (allStacks itag len ptag q l r (.var 0)))
theorem substAllResults {m n : Nat} (s : Fin m → Term n) itag len ptag q l r (raw ot nt : Term m) :
 substituteFormula s (allResults itag len ptag q l r raw ot nt) =
 allResults itag len ptag q l r (substitute s raw) (substitute s ot) (substitute s nt) := by
 simp only [allResults,substituteFormula,substProperty,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
theorem substAllNew {m n : Nat} (s : Fin m → Term n) itag len ptag q l r (raw ot : Term m) :
 substituteFormula s (allNew itag len ptag q l r raw ot) =
 allNew itag len ptag q l r (substitute s raw) (substitute s ot) := by
 simp only [allNew,substituteFormula,substAllResults,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
theorem substAllStacks {m n : Nat} (s : Fin m → Term n) itag len ptag q l r (raw : Term m) :
 substituteFormula s (allStacks itag len ptag q l r raw) =
 allStacks itag len ptag q l r (substitute s raw) := by
 simp only [allStacks,substituteFormula,substAllNew,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
theorem substBounded {m n : Nat} (s : Fin m → Term n) itag len ptag q l r (bound : Term m) :
 substituteFormula s (bounded itag len ptag q l r bound) =
 bounded itag len ptag q l r (substitute s bound) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substAllStacks,
  HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def allResultsInstance {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r (raw ot nt result : Term ctx) :
 Derivation T (.imp (allResults itag len ptag q l r raw ot nt) (property itag len ptag q l r raw ot nt result)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (property itag len ptag q l r (liftTerm raw) (liftTerm ot) (liftTerm nt) (.var 0)) result)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allResults] using h
noncomputable def allNewInstance {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r (raw ot nt : Term ctx) :
 Derivation T (.imp (allNew itag len ptag q l r raw ot) (allResults itag len ptag q l r raw ot nt)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allResults itag len ptag q l r (liftTerm raw) (liftTerm ot) (.var 0)) nt)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllResults,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allNew] using h
noncomputable def allStacksInstance {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r (raw ot : Term ctx) :
 Derivation T (.imp (allStacks itag len ptag q l r raw) (allNew itag len ptag q l r raw ot)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (allNew itag len ptag q l r (liftTerm raw) (.var 0)) ot)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllNew,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,allStacks] using h
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r (raw ot nt result : Term ctx) :
 Derivation T (.imp (allStacks itag len ptag q l r raw) (property itag len ptag q l r raw ot nt result)) :=
 Hilbert.compose (allResultsInstance itag len ptag q l r raw ot nt result)
  (Hilbert.compose (allNewInstance itag len ptag q l r raw ot nt) (allStacksInstance itag len ptag q l r raw ot))
noncomputable def boundedInstance {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r (bound raw : Term ctx) :
 Derivation T (.imp (bounded itag len ptag q l r bound)
  (.imp (HistoryBounds.weakBound raw bound) (allStacks itag len ptag q l r raw))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound)) (allStacks itag len ptag q l r (.var 0))) raw)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substAllStacks,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,bounded] using h
noncomputable def transportAll {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r (a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (allStacks itag len ptag q l r a) (allStacks itag len ptag q l r b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (allStacks itag len ptag q l r (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllStacks,
  substitute,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportBoundProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportBoundProof
