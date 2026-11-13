module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EqualEquationsProof

theorem selectSound {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (test yes : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (call tag (test ::ᵥ yes ::ᵥ .zero ::ᵥ nil)) (.succ .zero))
        (.conj (.equal test .zero) (.equal yes (.succ .zero))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let v := call tag (test ::ᵥ yes ::ᵥ .zero ::ᵥ nil)
  let E := Formula.equal v (.succ .zero)
  let Z := Formula.equal v .zero
  let H := Formula.conj (.equal test .zero) (.equal v yes)
  let Q := Formula.conj (.equal test .zero) (.equal yes (.succ .zero))
  obtain ⟨hg⟩ := HistoryDecoder.SelectGraphProof.selectGraph p tag ht test yes .zero
  have hz : Hilbert.Local T ctx [E] (.imp Z Q) := by
    have e : Hilbert.Local T ctx [Z,E] E := .hypothesis (by simp)
    have z : Hilbert.Local T ctx [Z,E] Z := .hypothesis List.mem_cons_self
    exact Hilbert.Local.discharge (HistoryRuleSuffix.SuffixProof.reject v Q e z)
  have hh : Hilbert.Local T ctx [E] (.imp H Q) := by
    have e : Hilbert.Local T ctx [H,E] E := .hypothesis (by simp)
    have h : Hilbert.Local T ctx [H,E] H := .hypothesis List.mem_cons_self
    have htest := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) h
    have heq := Hilbert.Local.mp (.base (.logical (.andRight _ _))) h
    have hy := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ heq) e
    exact Hilbert.Local.discharge (.mp (.mp (.base (.logical (.andIntro _ _))) htest) hy)
  have out := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z H Q))) hz) hh) (.base hg)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge out)⟩

theorem internalEqualSound : Targets.InternalEqualSound := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (pairCall tag a b) (.succ .zero)
  obtain ⟨hso,hsi,hf,hb⟩ := nodesInstalled p tag ht
  obtain ⟨he⟩ := equalEquation p tag ht a b
  obtain ⟨ho⟩ := selectSound p (tag+1) hso (pairCall (forwardTag tag) a b) (innerValue tag a b)
  obtain ⟨hi⟩ := selectSound p (insideTag tag+1) hsi (pairCall (backwardTag tag) b a) (.succ .zero)
  obtain ⟨hd⟩ := HistoryDecoder.ComparisonProof.doubleZero p (forwardTag tag) (backwardTag tag) hf hb a b
  have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have norm := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) e
  have out := Hilbert.Local.mp (.base ho) norm
  have fzero := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) out
  have ione := Hilbert.Local.mp (.base (.logical (.andRight _ _))) out
  have inner := Hilbert.Local.mp (.base hi) ione
  have bzero := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) inner
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base hd) fzero) bzero))⟩

theorem diagonal {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩)
    (a : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (pairCall tag a a) (.succ .zero))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hso,hsi,hf,hb⟩ := nodesInstalled p tag ht
  obtain ⟨he⟩ := equalEquation p tag ht a a
  obtain ⟨hzf⟩ := HistoryDecoder.StepInvariantProof.differenceDiagonal p (forwardTag tag) hf a
  obtain ⟨hzb⟩ := HistoryDecoder.StepInvariantProof.differenceDiagonal p (backwardTag tag) hb a
  obtain ⟨ho⟩ := HistoryCodec.PairProof.selectZero p (tag+1) hso (innerValue tag a a) (.zero : Term ctx)
  obtain ⟨hi⟩ := HistoryCodec.PairProof.selectZero p (insideTag tag+1) hsi (.succ (.zero : Term ctx)) .zero
  have co := HistoryDecoder.SelectGraphProof.testCongruence (G := []) (tag+1)
    (pairCall (forwardTag tag) a a) .zero (innerValue tag a a) .zero (.base hzf)
  have ci := HistoryDecoder.SelectGraphProof.testCongruence (G := []) (insideTag tag+1)
    (pairCall (backwardTag tag) a a) .zero (.succ .zero) .zero (.base hzb)
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ (Hilbert.Local.finish co)
    (Logic.trans _ _ _ ho (Logic.trans _ _ _ (Hilbert.Local.finish ci) hi)))⟩

theorem internalEqualComplete : Targets.InternalEqualComplete := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal a b
  obtain ⟨hd⟩ := diagonal p tag ht a
  have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hc := localUnary (call tag (liftTerm a ::ᵥ .var 0 ::ᵥ nil)) b a (HistoryOrder.StepProof.localSym _ _ e)
  have hc' : Hilbert.Local T ctx [E] (.equal (pairCall tag a b) (pairCall tag a a)) := by
    simpa only [pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,
      Support.shiftCancel,substitute,Fin.cases_zero] using hc
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hc' (.base hd)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualProof
