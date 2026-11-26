module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ShellProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.MonotonicityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.IntervalProof
open GorbowSyntax GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryBounds.PairProof
open OrderSupportProof TransitivityProof ShellProof MonotonicityProof

theorem lowFloor (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (weakBound (square b) (.add (square b) a))) := by
  obtain ⟨h⟩ := weakAdd T (square b) (square b) a
  exact ⟨.mp h (weakReflexive (square b))⟩

theorem highFloor (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (weakBound (square a) (.add (.add (square a) a) b))) := by
  obtain ⟨h1⟩ := weakAdd T (square a) (square a) a
  obtain ⟨h2⟩ := weakAdd T (square a) (.add (square a) a) b
  exact ⟨.mp h2 (.mp h1 (weakReflexive (square a)))⟩

theorem lowCeiling (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (HistoryOrder.lower a b)
      (weakBound (.add (square b) a) (top b)))) := by
  obtain ⟨hw⟩ := strictToWeak T a b
  obtain ⟨hm⟩ := weakAddLeft T a b (square b)
  obtain ⟨ha⟩ := weakAdd T (.add (square b) a) (.add (square b) b) b
  exact ⟨Hilbert.compose ha (Hilbert.compose hm hw)⟩

theorem highCeiling (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (HistoryOrder.upper a b)
      (weakBound (.add (.add (square a) a) b) (top a)))) :=
  weakAddLeft T b a (.add (square a) a)

theorem pairLowerInterval {n : Nat} (p : GorbowPRProgram.Program n) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.lower a b)
        (.conj (weakBound (square b) (HistoryDifference.pairCall tag a b))
          (weakBound (HistoryDifference.pairCall tag a b) (top b))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := HistoryOrder.lower a b
  obtain ⟨hv⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx a b
  obtain ⟨hf⟩ := lowFloor T a b
  obtain ⟨hc⟩ := lowCeiling T a b
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have he := Hilbert.Local.mp (.base hv) hh
  have hfloor : Hilbert.Local T ctx [H]
      (weakBound (square b) (HistoryDifference.pairCall tag a b)) :=
    .mp (.mp (.base (weakTransport _ _ (.add (square b) a))) he) (.base hf)
  have hceiling : Hilbert.Local T ctx [H]
      (weakBound (HistoryDifference.pairCall tag a b) (top b)) :=
    .mp (.mp (.base (weakChildTransport _ (.add (square b) a) _)) he) (.mp (.base hc) hh)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (.logical (.andIntro _ _))) hfloor) hceiling))⟩

theorem pairUpperInterval {n : Nat} (p : GorbowPRProgram.Program n) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.upper a b)
        (.conj (weakBound (square a) (HistoryDifference.pairCall tag a b))
          (weakBound (HistoryDifference.pairCall tag a b) (top a))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := HistoryOrder.upper a b
  obtain ⟨hv⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a b
  obtain ⟨hf⟩ := highFloor T a b
  obtain ⟨hc⟩ := highCeiling T a b
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have he := Hilbert.Local.mp (.base hv) hh
  have hfloor : Hilbert.Local T ctx [H]
      (weakBound (square a) (HistoryDifference.pairCall tag a b)) :=
    .mp (.mp (.base (weakTransport _ _ (.add (.add (square a) a) b))) he) (.base hf)
  have hceiling : Hilbert.Local T ctx [H]
      (weakBound (HistoryDifference.pairCall tag a b) (top a)) :=
    .mp (.mp (.base (weakChildTransport _ (.add (.add (square a) a) b) _)) he) (.mp (.base hc) hh)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (.logical (.andIntro _ _))) hfloor) hceiling))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.IntervalProof
