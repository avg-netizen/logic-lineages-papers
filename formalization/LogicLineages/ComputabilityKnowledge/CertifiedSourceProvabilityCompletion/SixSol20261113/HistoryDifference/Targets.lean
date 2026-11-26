module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Literal predecessor AST at arbitrary installed address. -/
def PredecessorZero : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,HistoryCodec.predecessor⟩ → ∀ ctx,
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call (ctx := ctx) tag (.zero ::ᵥ nil)) .zero))

def PredecessorSuccessor : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,HistoryCodec.predecessor⟩ → ∀ ctx (a : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tag (.succ a ::ᵥ nil)) a))

/-- Both inputs shift, with no external evaluation or order premise. -/
def DifferenceShift : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (differenceCall tag (.succ a) (.succ b)) (differenceCall tag a b)))

/-- Actual subtraction on an arbitrary additive extension. -/
def DifferenceCancel : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩ → ∀ ctx (a k : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (differenceCall tag a (.add a k)) k))

/-- Saturation at zero beyond the subtracted input, retaining arbitrary excess. -/
def DifferenceSaturate : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩ → ∀ ctx (b k : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (differenceCall tag (.add b k) b) .zero))

/-- The existing actual pair's strict-lower sector, with the difference branch
fully discharged and a genuine arbitrary positive gap. -/
def PairLowerSector : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (a k : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (pairCall tag a (.add a (.succ k)))
      (.add (.mul (.add a (.succ k)) (.add a (.succ k))) a)))

/-- The complementary upper sector, including equality at gap zero. -/
def PairUpperSector : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (b k : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (pairCall tag (.add b k) b)
      (.add (.add (.mul (.add b k) (.add b k)) (.add b k)) b)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.Targets
