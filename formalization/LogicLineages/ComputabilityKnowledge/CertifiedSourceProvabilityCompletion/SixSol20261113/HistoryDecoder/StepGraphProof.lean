module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepNormalProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.SelectGraphProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof

noncomputable def combine {T : Sentence → Prop} {ctx : Nat}
    (step out inside yes no test1 test2 value code : Term ctx)
    (hn : Derivation T (.equal step out))
    (ho : Derivation T (.disj (.equal out no) (.conj (.equal test1 .zero) (.equal out inside))))
    (hi : Derivation T (.disj (.equal inside no) (.conj (.equal test2 .zero) (.equal inside yes))))
    (ht : Derivation T (.imp (.equal test1 .zero) (.imp (.equal test2 .zero) (.equal value code)))) :
    Derivation T (.disj (.equal step no) (.conj (.equal value code) (.equal step yes))) := by
  let Q := Formula.disj (.equal step no) (.conj (.equal value code) (.equal step yes))
  let A := Formula.conj (.equal test1 .zero) (.equal out inside)
  let B := Formula.conj (.equal test2 .zero) (.equal inside yes)
  have hleft : Derivation T (.imp (.equal out no) Q) := by
    have h : Hilbert.Local T ctx [.equal out no] (.equal out no) := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.base (.logical (.orLeft _ _))) (localTrans _ _ _ (.base hn) h)))
  have hright : Derivation T (.imp A Q) := by
    have hf : Hilbert.Local T ctx [A] (.imp (.equal inside no) Q) := by
      have ha : Hilbert.Local T ctx [.equal inside no,A] A := .hypothesis (by simp)
      have hb : Hilbert.Local T ctx [.equal inside no,A] (.equal inside no) := .hypothesis List.mem_cons_self
      have he := localTrans _ _ _ (.base hn)
        (localTrans _ _ _ (.mp (.base (.logical (.andRight _ _))) ha) hb)
      exact Hilbert.Local.discharge (.mp (.base (.logical (.orLeft _ _))) he)
    have hs : Hilbert.Local T ctx [A] (.imp B Q) := by
      have ha : Hilbert.Local T ctx [B,A] A := .hypothesis (by simp)
      have hb : Hilbert.Local T ctx [B,A] B := .hypothesis List.mem_cons_self
      have hz1 := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ha
      have hz2 := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
      have hm := Hilbert.Local.mp (.mp (.base ht) hz1) hz2
      have he := localTrans _ _ _ (.base hn)
        (localTrans _ _ _ (.mp (.base (.logical (.andRight _ _))) ha)
          (.mp (.base (.logical (.andRight _ _))) hb))
      exact Hilbert.Local.discharge (.mp (.base (.logical (.orRight _ _)))
        (.mp (.mp (.base (.logical (.andIntro _ _))) hm) he))
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hf) hs) (.base hi)))
  exact .mp (.mp (.mp (.logical (.orElim _ _ _)) hleft) hright) ho

/-- Every actual step either preserves its accumulator or found a genuine
pair-code match and returns the requested coordinate. -/
theorem stepGraph {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨5,innerStep right⟩) (b previous a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.disj (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)) previous)
        (.conj (.equal (call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil)) code)
          (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)) (chosen right a b))))) := by
  let value := call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil)
  let test1 := call (forwardTag right tag+1) (value ::ᵥ code ::ᵥ nil)
  let test2 := call (backwardTag right tag+1) (code ::ᵥ value ::ᵥ nil)
  let inside := call (choiceTag right tag+1) (test2 ::ᵥ chosen right a b ::ᵥ previous ::ᵥ nil)
  let out := call (tag+1) (test1 ::ᵥ inside ::ᵥ previous ::ᵥ nil)
  have hso := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select (stepArguments right) ht
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 1
  have hsi := SixSol20261112.Fuel.Equations.functionChild p (choiceTag right tag) HistoryCodec.select (choiceArguments right) hc
  have hf := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 0
  have hdf := SixSol20261112.Fuel.Equations.functionChild p (forwardTag right tag) HistoryCodec.difference forwardArguments hf
  have hb := SixSol20261112.Fuel.Equations.argumentChild p (choiceTag right tag) HistoryCodec.select (choiceArguments right) hc 0
  have hdb := SixSol20261112.Fuel.Equations.functionChild p (backwardTag right tag) HistoryCodec.difference backwardArguments hb
  obtain ⟨hn⟩ := stepEquation p tag right ht b previous a code seed
  obtain ⟨ho⟩ := SelectGraphProof.selectGraph p (tag+1) hso test1 inside previous
  obtain ⟨hi⟩ := SelectGraphProof.selectGraph p (choiceTag right tag+1) hsi test2 (chosen right a b) previous
  obtain ⟨hc⟩ := ComparisonProof.doubleZero p (forwardTag right tag+1) (backwardTag right tag+1) hdf hdb value code
  exact ⟨combine _ out inside _ _ test1 test2 value code hn ho hi hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepGraphProof
