module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector
open SixSol20261113
/-- Actual original dispatcher, arbitrary history and unchanged index/fuel. -/
def InternalDispatcher : Prop := ∀ k (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 n (p : Program n) (I : Installation p t old arithmetic x),
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history (line I.qtag values)) (.succ .zero)))
/-- The singleton certificate code itself is the actual iteration bound;
starting history is genuinely empty and final remaining lines are zero. -/
def InternalSingletonRun : Prop := ∀ k (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 n (p : Program n) (I : Installation p t old arithmetic x),
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel (certificate I.ctag I.qtag values))
   (output I.ptag I.ctag I.etag values)))
/-- Actual unchanged checker/bound/initializer/finalizer and quoted conclusion.
Only AST installation is assumed. No SAME-source selection or HB3 is asserted. -/
def InternalCertificate : Prop := ∀ k (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 n (p : Program n) (I : Installation p t old arithmetic x),
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
   (.add (raw I.etag values) (raw I.etag values)) (certificate I.ctag I.qtag values)) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.Targets
