module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.ScanBindingProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Fusion
open GorbowSyntax GorbowPRDefiningEquations GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph StateRecursionProof IterationEquationsProof

def fusion {ctx : Nat} (itag ltag ptag rtag atag : Nat) (left right state : Term ctx) : Formula ctx :=
 .equal (scanState itag ltag ptag rtag (HistoryAppend.appendCall atag left right) state)
  (scanState itag ltag ptag rtag right (scanState itag ltag ptag rtag left state))
def allFusion {ctx : Nat} (itag ltag ptag rtag atag : Nat) (left right : Term ctx) : Formula ctx :=
 .all (fusion itag ltag ptag rtag atag (liftTerm left) (liftTerm right) (.var 0))
def boundedFusion {ctx : Nat} (itag ltag ptag rtag atag : Nat) (bound right : Term ctx) : Formula ctx :=
 .all (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
  (allFusion itag ltag ptag rtag atag (.var 0) (liftTerm right)))

theorem substScanState {m n : Nat} (sub : Fin m → Term n) itag ltag ptag rtag (raw state : Term m) :
 substitute sub (scanState itag ltag ptag rtag raw state) =
 scanState itag ltag ptag rtag (substitute sub raw) (substitute sub state) := by
 simp only [scanState,substRun,HistoryLengthOffset.OffsetSupportProof.substLength,
  HistoryKernel.pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substFusion {m n : Nat} (sub : Fin m → Term n) itag ltag ptag rtag atag (left right state : Term m) :
 substituteFormula sub (fusion itag ltag ptag rtag atag left right state) =
 fusion itag ltag ptag rtag atag (substitute sub left) (substitute sub right) (substitute sub state) := by
 simp only [fusion,substituteFormula,substScanState,HistoryAppend.PreserveSupportProof.substAppend]
theorem substAllFusion {m n : Nat} (sub : Fin m → Term n) itag ltag ptag rtag atag (left right : Term m) :
 substituteFormula sub (allFusion itag ltag ptag rtag atag left right) =
 allFusion itag ltag ptag rtag atag (substitute sub left) (substitute sub right) := by
 simp only [allFusion,substituteFormula,substFusion,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Fusion
