module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP
open GorbowSyntax SixSol20261112.Fuel
open LiteralRawMP LiteralMPRun LiteralCheckerAcceptance HistoryRunSplice
/-- The old core uses the original full formula code (twice its raw token-list
code), and both runs share the same actual index, fuel and binder context. -/
def inputAcceptance {ctx : Nat} (qtag atag ctag : Nat)
 (context phi psi imp ant index fuel : Term ctx) : Formula ctx :=
 .conj (.equal (coreCall qtag index fuel context
   (.add (implicationRaw atag ctag phi psi) (implicationRaw atag ctag phi psi)) imp) (.succ .zero))
  (.equal (coreCall qtag index fuel context (.add phi phi) ant) (.succ .zero))
/-- Only the real successful history tail is existential. The requested raw
formula is recovered from doubled-code equality, not assumed to be the final
raw witness, and the actual encoded certificate is the iteration bound. -/
def successfulRun {ctx : Nat} (itag ptag ctag : Nat)
 (context raw certificate index fuel : Term ctx) : Formula ctx :=
 .ex (.equal
  (run itag ptag (liftTerm certificate) (.succ .zero) (liftTerm certificate) (liftTerm index) (liftTerm fuel))
  (state ptag (.succ (HistoryLookup.consCall ctag
   (HistoryKernel.pairCall ptag (liftTerm context) (liftTerm raw)) (.var 0))) .zero))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP
