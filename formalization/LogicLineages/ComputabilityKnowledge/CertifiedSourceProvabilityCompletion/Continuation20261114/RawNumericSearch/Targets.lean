module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector
/-- All-input exact execution graph, not a native-to-internal reflection rule. -/
def NativeSearch : Prop := ∀ (test : Program 2) (count line : Nat),
 (evaluate (search test) (count ::ᵥ line ::ᵥ nil)=0 ∨ evaluate (search test) (count ::ᵥ line ::ᵥ nil)=1) ∧
 (evaluate (search test) (count ::ᵥ line ::ᵥ nil)=1 ↔ ∃ i < count, evaluate test (i ::ᵥ line ::ᵥ nil) ≠ 0)
def InternalPersistence : Prop := ∀ n (p : Program n) (test : Program 2)
 (I : Installation p test), ∀ ctx (count line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (searchCall I.searchTag count line) (.succ .zero))
  (.equal (searchCall I.searchTag (.succ count) line) (.succ .zero))))
/-- Genuine internal arbitrary-count coverage; eventual concrete original-code
bounds and full reconstructed schema test success must be proved separately. -/
def InternalWitness : Prop := ∀ n (p : Program n) (test : Program 2)
 (I : Installation p test), ∀ ctx (i j line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (testCall I.testTag i line) (.succ .zero))
  (.equal (searchCall I.searchTag (.succ (.add i j)) line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.Targets
