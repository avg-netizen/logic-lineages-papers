module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.StepRangeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryBounds HistoryBounds.PairProof

/-- Actual right-coordinate step can return only previous or the enumerated
second coordinate, so its bound follows internally without any match oracle. -/
theorem stepRange {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨5,HistoryDecoder.innerStep true⟩)
    (a b previous code seed bound : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (weakBound previous bound) (.imp (weakBound b bound)
        (weakBound (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)) bound)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let out := call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)
  let P := weakBound previous bound
  let B := weakBound b bound
  let Q := weakBound out bound
  let H := Formula.conj
    (.equal (call (HistoryDecoder.StepNormalProof.stepPairTag true tag) (a ::ᵥ b ::ᵥ nil)) code)
    (.equal out b)
  obtain ⟨hg⟩ := HistoryDecoder.StepGraphProof.stepGraph p tag true ht b previous a code seed
  have hl : Hilbert.Local T ctx [B,P] (.imp (.equal out previous) Q) := by
    have he : Hilbert.Local T ctx [.equal out previous,B,P] (.equal out previous) := .hypothesis List.mem_cons_self
    have hp : Hilbert.Local T ctx [.equal out previous,B,P] P := .hypothesis (by simp)
    exact Hilbert.Local.discharge (.mp (.mp (.base (HistoryCancellation.MonotonicityProof.weakChildTransport _ _ _)) he) hp)
  have hr : Hilbert.Local T ctx [B,P] (.imp H Q) := by
    have h : Hilbert.Local T ctx [H,B,P] H := .hypothesis List.mem_cons_self
    have hb : Hilbert.Local T ctx [H,B,P] B := .hypothesis (by simp)
    have he := Hilbert.Local.mp (.base (.logical (.andRight _ _))) h
    exact Hilbert.Local.discharge (.mp (.mp (.base (HistoryCancellation.MonotonicityProof.weakChildTransport _ _ _)) he) hb)
  have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hl) hr) (.base hg)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.StepRangeProof
