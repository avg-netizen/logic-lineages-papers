module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Dispatcher.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Dispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual original dispatcher on the canonical runtime rule0/tag12 line.
All three input raw codes and every index/fuel/history term are arbitrary, including
zero. Only original formula1/term0/term0 guards occur; actual line validity, rule0
selection and logical acceptance must be derived internally. -/
def InternalDispatcher : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (formula left right index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula left right)
   (.equal (HistoryDispatcher.dispatcherCall I.dispatcherTag index fuel history
    (UniformClosedRule12.lineCall I.constructorTag formula left right)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Dispatcher.Targets
