module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.LeafDispatcherDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.LeafDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Exact directional internal retention of every accepted original logical line.
No recognizer failure, input validity, or new-leaf success is an added premise. -/
def InternalLeafRetention (test : Program 1) : Prop := ∀ n (p : Program n)
 (old : Program 1) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨1,old⟩ →
 (nodes p)[newTag]? = some ⟨1,extend test old⟩ →
 ∀ ctx (line : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (RawLogicalRetention.leafCall oldTag line) (.succ .zero))
       (.equal (RawLogicalRetention.leafCall newTag line) (.succ .zero))))
/-- Actual arbitrary old dispatcher success is retained at the same symbolic
index, fuel, history and line, including runtime zero. No leaf/run/CORE bridge
is assumed; both literal registry memberships are the entire interface. -/
def InternalDispatcherRetention (test : Program 1) : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨4,original valid old arithmetic x⟩ →
 (nodes p)[newTag]? = some ⟨4,extended test valid old arithmetic x⟩ →
 ∀ ctx (index fuel history line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (HistoryDispatcher.dispatcherCall oldTag index fuel history line) (.succ .zero))
       (.equal (HistoryDispatcher.dispatcherCall newTag index fuel history line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.LeafDispatcher.Targets
