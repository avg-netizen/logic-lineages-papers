module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Original arbitrary dispatcher success is preserved by the literal outer
universal replacement leaf. No old/new CORE success or leaf implication is an
additional premise; both literal AST memberships are the only interface. -/
def InternalDispatcherRetention : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨4,original valid old arithmetic x⟩ →
 (nodes p)[newTag]? = some ⟨4,extended valid old arithmetic x⟩ →
 ∀ ctx (index fuel history line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (HistoryDispatcher.dispatcherCall oldTag index fuel history line) (.succ .zero))
       (.equal (HistoryDispatcher.dispatcherCall newTag index fuel history line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.Targets
