module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneInductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Frame
open GorbowSyntax GorbowPRDefiningEquations GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph StateRecursionProof Fusion

def property {ctx : Nat} (itag ltag ptag rtag atag : Nat) (raw tasks out suffix : Term ctx) : Formula ctx :=
 .imp (.equal (scanState itag ltag ptag rtag raw (.succ tasks)) (.succ out))
  (.equal (scanState itag ltag ptag rtag raw (.succ (HistoryAppend.appendCall atag tasks suffix)))
   (.succ (HistoryAppend.appendCall atag out suffix)))
def allTasks {ctx : Nat} (itag ltag ptag rtag atag : Nat) (raw out suffix : Term ctx) : Formula ctx :=
 .all (property itag ltag ptag rtag atag (liftTerm raw) (.var 0) (liftTerm out) (liftTerm suffix))
def bounded {ctx : Nat} (itag ltag ptag rtag atag : Nat) (bound out suffix : Term ctx) : Formula ctx :=
 .all (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
  (allTasks itag ltag ptag rtag atag (.var 0) (liftTerm out) (liftTerm suffix)))
theorem substProperty {m n : Nat} (s : Fin m → Term n) itag ltag ptag rtag atag (raw tasks out suffix : Term m) :
 substituteFormula s (property itag ltag ptag rtag atag raw tasks out suffix) =
 property itag ltag ptag rtag atag (substitute s raw) (substitute s tasks) (substitute s out) (substitute s suffix) := by
 simp only [property,substituteFormula,substScanState,HistoryAppend.PreserveSupportProof.substAppend,substitute]
theorem substAll {m n : Nat} (s : Fin m → Term n) itag ltag ptag rtag atag (raw out suffix : Term m) :
 substituteFormula s (allTasks itag ltag ptag rtag atag raw out suffix) =
 allTasks itag ltag ptag rtag atag (substitute s raw) (substitute s out) (substitute s suffix) := by
 simp only [allTasks,substituteFormula,substProperty,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substBounded {m n : Nat} (s : Fin m → Term n) itag ltag ptag rtag atag (bound out suffix : Term m) :
 substituteFormula s (bounded itag ltag ptag rtag atag bound out suffix) =
 bounded itag ltag ptag rtag atag (substitute s bound) (substitute s out) (substitute s suffix) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substAll,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Frame
