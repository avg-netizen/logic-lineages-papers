module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Dispatcher.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Dispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual original dispatcher on the canonical runtime rule0/tag13 line.
Both input raw codes and every index/fuel/history term are arbitrary, including
zero. Only original formula1/term0 guards occur; actual line validity, rule0
selection and logical acceptance must be derived internally. -/
def InternalDispatcher : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (formula replacement index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag formula replacement)
   (.equal (HistoryDispatcher.dispatcherCall I.dispatcherTag index fuel history
    (UniformClosedRule13.lineCall I.constructorTag formula replacement)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Dispatcher.Targets
