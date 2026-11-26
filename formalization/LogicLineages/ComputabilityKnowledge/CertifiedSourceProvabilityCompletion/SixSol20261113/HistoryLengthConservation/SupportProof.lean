module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice
open HistoryRunSplice.IdleProof (substRun)
open HistoryRunSplice.PrefixSupportProof (substState)
open HistoryLengthOffset.OffsetSupportProof (substLength)

def noneRelation {ctx : Nat} (itag ltag ptag : Nat) (lines out index fuel : Term ctx) : Formula ctx :=
  .neg (.equal (run itag ptag (lengthCall ltag lines) .zero lines index fuel) (state ptag (.succ out) .zero))
def someRelation {ctx : Nat} (itag ltag ptag : Nat) (lines history out index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (run itag ptag (lengthCall ltag lines) (.succ history) lines index fuel) (state ptag (.succ out) .zero))
    (.equal (lengthCall ltag out) (.add (lengthCall ltag history) (lengthCall ltag lines)))
theorem substNone {m n : Nat} (sub : Fin m → Term n) itag ltag ptag (lines out index fuel : Term m) :
    substituteFormula sub (noneRelation itag ltag ptag lines out index fuel)=
      noneRelation itag ltag ptag (substitute sub lines) (substitute sub out) (substitute sub index) (substitute sub fuel) := by
  simp only [noneRelation,substituteFormula,substRun,substState,substLength,substitute]
theorem substSome {m n : Nat} (sub : Fin m → Term n) itag ltag ptag (lines history out index fuel : Term m) :
    substituteFormula sub (someRelation itag ltag ptag lines history out index fuel)=
      someRelation itag ltag ptag (substitute sub lines) (substitute sub history) (substitute sub out) (substitute sub index) (substitute sub fuel) := by
  simp only [someRelation,substituteFormula,substRun,substState,substLength,substitute]
def noneAll {ctx : Nat} (itag ltag ptag : Nat) (lines index fuel : Term ctx) : Formula ctx :=
  .all (noneRelation itag ltag ptag (liftTerm lines) (.var 0) (liftTerm index) (liftTerm fuel))
def someOut {ctx : Nat} (itag ltag ptag : Nat) (lines history index fuel : Term ctx) : Formula ctx :=
  .all (someRelation itag ltag ptag (liftTerm lines) (liftTerm history) (.var 0) (liftTerm index) (liftTerm fuel))
def someAll {ctx : Nat} (itag ltag ptag : Nat) (lines index fuel : Term ctx) : Formula ctx :=
  .all (someOut itag ltag ptag (liftTerm lines) (.var 0) (liftTerm index) (liftTerm fuel))
def property {ctx : Nat} (itag ltag ptag : Nat) (lines index fuel : Term ctx) : Formula ctx :=
  .conj (noneAll itag ltag ptag lines index fuel) (someAll itag ltag ptag lines index fuel)
theorem substNoneAll {m n : Nat} (sub : Fin m → Term n) itag ltag ptag (lines index fuel : Term m) :
    substituteFormula sub (noneAll itag ltag ptag lines index fuel)=
      noneAll itag ltag ptag (substitute sub lines) (substitute sub index) (substitute sub fuel) := by
  simp only [noneAll,substituteFormula,substNone,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substSomeOut {m n : Nat} (sub : Fin m → Term n) itag ltag ptag (lines history index fuel : Term m) :
    substituteFormula sub (someOut itag ltag ptag lines history index fuel)=
      someOut itag ltag ptag (substitute sub lines) (substitute sub history) (substitute sub index) (substitute sub fuel) := by
  simp only [someOut,substituteFormula,substSome,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substSomeAll {m n : Nat} (sub : Fin m → Term n) itag ltag ptag (lines index fuel : Term m) :
    substituteFormula sub (someAll itag ltag ptag lines index fuel)=
      someAll itag ltag ptag (substitute sub lines) (substitute sub index) (substitute sub fuel) := by
  simp only [someAll,substituteFormula,substSomeOut,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substProperty {m n : Nat} (sub : Fin m → Term n) itag ltag ptag (lines index fuel : Term m) :
    substituteFormula sub (property itag ltag ptag lines index fuel)=
      property itag ltag ptag (substitute sub lines) (substitute sub index) (substitute sub fuel) := by
  simp only [property,substituteFormula,substNoneAll,substSomeAll,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def noneElim {T : Sentence → Prop} {ctx : Nat} (itag ltag ptag : Nat) (lines out index fuel : Term ctx) :
    Derivation T (.imp (property itag ltag ptag lines index fuel) (noneRelation itag ltag ptag lines out index fuel)) := by
  have h := Derivation.logical (A := T) (.allInstantiate (noneRelation itag ltag ptag (liftTerm lines) (.var 0) (liftTerm index) (liftTerm fuel)) out)
  simp only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substNone,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at h
  exact Hilbert.compose h (.logical (.andLeft _ _))
noncomputable def someElim {T : Sentence → Prop} {ctx : Nat} (itag ltag ptag : Nat) (lines history out index fuel : Term ctx) :
    Derivation T (.imp (property itag ltag ptag lines index fuel) (someRelation itag ltag ptag lines history out index fuel)) := by
  have h1 := Derivation.logical (A := T) (.allInstantiate (someOut itag ltag ptag (liftTerm lines) (.var 0) (liftTerm index) (liftTerm fuel)) history)
  have h2 := Derivation.logical (A := T) (.allInstantiate (someRelation itag ltag ptag (liftTerm lines) (liftTerm history) (.var 0) (liftTerm index) (liftTerm fuel)) out)
  simp only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substSomeOut,substSome,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at h1 h2
  exact Hilbert.compose h2 (Hilbert.compose h1 (.logical (.andRight _ _)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SupportProof
