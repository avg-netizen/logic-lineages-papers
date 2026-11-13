module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.RangeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EqualEquationsProof

theorem selectRange {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (test yes no : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.disj (.equal (call tag (test ::ᵥ yes ::ᵥ no ::ᵥ nil)) no)
        (.equal (call tag (test ::ᵥ yes ::ᵥ no ::ᵥ nil)) yes))) := by
  obtain ⟨hg⟩ := HistoryDecoder.SelectGraphProof.selectGraph p tag ht test yes no
  let T := GorbowPRNumeralCalculation.Theory p
  let V := call tag (test ::ᵥ yes ::ᵥ no ::ᵥ nil)
  let H := Formula.conj (.equal test .zero) (.equal V yes)
  let Q := Formula.disj (.equal V no) (.equal V yes)
  have hh : Derivation T (.imp H Q) := by
    have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.base (.logical (.orRight _ _))) (.mp (.base (.logical (.andRight _ _))) h)))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) (.logical (.orLeft _ _))) hh) hg⟩

theorem equalRange {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.disj (.equal (pairCall tag a b) .zero) (.equal (pairCall tag a b) (.succ .zero)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let V := pairCall tag a b
  let I := innerValue tag a b
  let N := normal tag a b
  let Q := Formula.disj (.equal V .zero) (.equal V (.succ .zero))
  obtain ⟨hso,hsi,hf,hb⟩ := nodesInstalled p tag ht
  obtain ⟨he⟩ := equalEquation p tag ht a b
  obtain ⟨ho⟩ := selectRange p (tag+1) hso (pairCall (forwardTag tag) a b) I .zero
  obtain ⟨hi⟩ := selectRange p (insideTag tag+1) hsi (pairCall (backwardTag tag) b a) (.succ .zero) .zero
  have hz : Derivation T (.imp (.equal N .zero) Q) := by
    have h : Hilbert.Local T ctx [.equal N .zero] (.equal N .zero) := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.base (.logical (.orLeft _ _))) (localTrans _ _ _ (.base he) h)))
  let E := Formula.equal N I
  have hh : Derivation T (.imp E Q) := by
    have iz : Hilbert.Local T ctx [E] (.imp (.equal I .zero) Q) := by
      have e : Hilbert.Local T ctx [.equal I .zero,E] E := .hypothesis (by simp)
      have h : Hilbert.Local T ctx [.equal I .zero,E] (.equal I .zero) := .hypothesis List.mem_cons_self
      exact Hilbert.Local.discharge
        (.mp (.base (.logical (.orLeft _ _))) (localTrans _ _ _ (.base he) (localTrans _ _ _ e h)))
    have io : Hilbert.Local T ctx [E] (.imp (.equal I (.succ .zero)) Q) := by
      have e : Hilbert.Local T ctx [.equal I (.succ .zero),E] E := .hypothesis (by simp)
      have h : Hilbert.Local T ctx [.equal I (.succ .zero),E] (.equal I (.succ .zero)) := .hypothesis List.mem_cons_self
      exact Hilbert.Local.discharge
        (.mp (.base (.logical (.orRight _ _))) (localTrans _ _ _ (.base he) (localTrans _ _ _ e h)))
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) iz) io) (.base hi)))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hz) hh) ho⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.RangeProof
