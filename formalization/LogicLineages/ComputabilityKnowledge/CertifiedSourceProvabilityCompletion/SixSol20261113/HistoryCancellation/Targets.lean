module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.Targets
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry List.Vector

def AddCancelRight : Prop := ∀ (T : Sentence → Prop) ctx (a b c : Term ctx),
  Nonempty (Derivation T (cancelRight a b c))
def AddCancelLeft : Prop := ∀ (T : Sentence → Prop) ctx (a b c : Term ctx),
  Nonempty (Derivation T (cancelLeft a b c))

/-- Fixed upper coordinate in the actual lower half-shell. Internal sector
premises describe inputs; no assumptions about the primitive's output. -/
def PairLowerFixedSecond : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b c : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (HistoryOrder.lower a b) (.imp (HistoryOrder.lower c b)
      (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c b))
        (.equal a c)))))

/-- Fixed upper coordinate in the actual upper half-shell. Cross-shell
separation and full pair injectivity remain separate unpaid obligations. -/
def PairUpperFixedFirst : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b c : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (HistoryOrder.upper a b) (.imp (HistoryOrder.upper a c)
      (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c))
        (.equal b c)))))

/-- Full injectivity of the actual registered literal square-shell codec.
No sector, standard-model, decoder, or arithmetic-bound assumptions. -/
def PairInjective : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a b c d : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c d))
      (.conj (.equal a c) (.equal b d))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.Targets
