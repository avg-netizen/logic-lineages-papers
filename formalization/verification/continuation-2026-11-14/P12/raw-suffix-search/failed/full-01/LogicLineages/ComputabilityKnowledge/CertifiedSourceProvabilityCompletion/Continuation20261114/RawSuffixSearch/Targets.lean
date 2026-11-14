module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector SixSol20261113
/-- Exact all-natural execution graph: result is Boolean, and success means
an actual tested original suffix accepted. This is not a native-to-internal rule. -/
def NativeSearch : Prop := ∀ (test : Program 2) (count raw line : Nat),
 (evaluate (search test) (count ::ᵥ raw ::ᵥ line ::ᵥ nil) = 0 ∨
  evaluate (search test) (count ::ᵥ raw ::ᵥ line ::ᵥ nil) = 1) ∧
 (evaluate (search test) (count ::ᵥ raw ::ᵥ line ::ᵥ nil) = 1 ↔
  ∃ i < count, evaluate test (evaluate HistoryLookup.drop (i ::ᵥ raw ::ᵥ nil) ::ᵥ line ::ᵥ nil) ≠ 0)
/-- Genuine internal persistent success of the literal Boolean latch. -/
def InternalPersistence : Prop := ∀ n (p : Program n) (test : Program 2)
 (I : Installation p test), ∀ ctx (count raw line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (searchCall I.searchTag count raw line) (.succ .zero))
   (.equal (searchCall I.searchTag (.succ count) raw line) (.succ .zero))))
/-- An actual tested suffix at i causes success by i+1 and every i+j+1.
The witness test is an INTERNAL formula, not an external success oracle.
Concrete schema work must prove its actual suffix occurrence and provide a
finite search bound of this form; neither is assumed solved by this theorem. -/
def InternalWitness : Prop := ∀ n (p : Program n) (test : Program 2)
 (I : Installation p test), ∀ ctx (i j raw line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (testCall I.testTag (HistoryLookup.DropEquationsProof.dropCall I.dropTag i raw) line) (.succ .zero))
   (.equal (searchCall I.searchTag (.succ (.add i j)) raw line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.Targets
