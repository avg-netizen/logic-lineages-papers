module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Iteration
open GorbowSyntax GorbowPRDefiningEquations List.Vector

def runCall {ctx : Nat} (itag : Nat) (count state : Term ctx) : Term ctx :=
 call itag (count ::ᵥ state ::ᵥ nil)
def rightCall {ctx : Nat} (rtag : Nat) (state : Term ctx) : Term ctx :=
 call rtag (state ::ᵥ nil)
/-- Actual encoded prefix splice; arbitrary numeric state, not only successes. -/
def splice {ctx : Nat} (itag ltag atag ptag rtag : Nat)
 (left right state : Term ctx) : Formula ctx :=
 .equal
  (runCall itag (HistoryLengthOffset.lengthCall ltag left)
   (HistoryKernel.pairCall ptag (HistoryAppend.appendCall atag left right) state))
  (HistoryKernel.pairCall ptag right
   (rightCall rtag (runCall itag (HistoryLengthOffset.lengthCall ltag left)
    (HistoryKernel.pairCall ptag left state))))
/-- Bound-based course-of-values invariant. All changing coordinates are
bound internally: left < bound, arbitrary right, arbitrary Option-stack code. -/
def belowSplice {ctx : Nat} (itag ltag atag ptag rtag : Nat) (bound : Term ctx) : Formula ctx :=
 .all (.all (.all (.imp
  (HistoryBounds.strictBound (.var 2) (GorbowFormulaSubstitution.renameTerm (fun i => Fin.succ (Fin.succ (Fin.succ i))) bound))
  (splice itag ltag atag ptag rtag (.var 2) (.var 1) (.var 0)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Iteration
