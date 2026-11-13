module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.ComparisonProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem sound {n ctx : Nat} (p : Program n) (stag ltag rtag : Nat)
    (hs : (nodes p)[stag]? = some ⟨3,HistoryCodec.select⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩) (a b c d : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (call stag (HistoryKernel.pairCall ltag a b ::ᵥ .zero ::ᵥ HistoryKernel.pairCall rtag c d ::ᵥ nil)) (.succ .zero))
        (.conj (.equal a b) (.equal c d)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let A := HistoryKernel.pairCall ltag a b
  let B := HistoryKernel.pairCall rtag c d
  let V := call stag (A ::ᵥ .zero ::ᵥ B ::ᵥ nil)
  let E := Formula.equal V (.succ .zero)
  let Z := Formula.equal A .zero
  let O := Formula.equal A (.succ .zero)
  let Q := Formula.conj (.equal a b) (.equal c d)
  obtain ⟨hcases⟩ := HistoryKernel.RangeProof.equalRange p ltag hl a b
  obtain ⟨hz⟩ := HistoryCodec.PairProof.selectZero p stag hs (.zero : Term ctx) B
  obtain ⟨ho⟩ := HistoryCodec.PairProof.selectPositive p stag hs (.zero : Term ctx) B .zero
  obtain ⟨hls⟩ := HistoryKernel.EqualProof.internalEqualSound n p ltag hl ctx a b
  obtain ⟨hrs⟩ := HistoryKernel.EqualProof.internalEqualSound n p rtag hr ctx c d
  have hzero : Hilbert.Local T ctx [E] (.imp Z Q) := by
    have he : Hilbert.Local T ctx [Z,E] E := .hypothesis (by simp)
    have htest : Hilbert.Local T ctx [Z,E] Z := .hypothesis List.mem_cons_self
    have eqzero := localTrans _ _ _ (HistoryDecoder.SelectGraphProof.testCongruence stag A .zero .zero B htest) (.base hz)
    exact Hilbert.Local.discharge (HistoryRuleSuffix.SuffixProof.reject V Q he eqzero)
  have hone : Hilbert.Local T ctx [E] (.imp O Q) := by
    have he : Hilbert.Local T ctx [O,E] E := .hypothesis (by simp)
    have htest : Hilbert.Local T ctx [O,E] O := .hypothesis List.mem_cons_self
    have eqright := localTrans _ _ _ (HistoryDecoder.SelectGraphProof.testCongruence stag A (.succ .zero) .zero B htest) (.base ho)
    have eb := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ eqright) he
    have hab := Hilbert.Local.mp (.base hls) htest
    have hcd := Hilbert.Local.mp (.base hrs) eb
    exact Hilbert.Local.discharge (.mp (.mp (.base (.logical (.andIntro _ _))) hab) hcd)
  have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z O Q))) hzero) hone) (.base hcases)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem complete {n ctx : Nat} (p : Program n) (stag ltag rtag : Nat)
    (hs : (nodes p)[stag]? = some ⟨3,HistoryCodec.select⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩) (a b c d : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.conj (.equal a b) (.equal c d))
        (.equal (call stag (HistoryKernel.pairCall ltag a b ::ᵥ .zero ::ᵥ HistoryKernel.pairCall rtag c d ::ᵥ nil)) (.succ .zero)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let A := HistoryKernel.pairCall ltag a b
  let B := HistoryKernel.pairCall rtag c d
  let H := Formula.conj (.equal a b) (.equal c d)
  obtain ⟨hlc⟩ := HistoryKernel.EqualProof.internalEqualComplete n p ltag hl ctx a b
  obtain ⟨hrc⟩ := HistoryKernel.EqualProof.internalEqualComplete n p rtag hr ctx c d
  obtain ⟨ho⟩ := HistoryCodec.PairProof.selectPositive p stag hs (.zero : Term ctx) B .zero
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have ea := Hilbert.Local.mp (.base hlc) (.mp (.base (.logical (.andLeft _ _))) hh)
  have eb := Hilbert.Local.mp (.base hrc) (.mp (.base (.logical (.andRight _ _))) hh)
  have he := localTrans _ _ _ (HistoryDecoder.SelectGraphProof.testCongruence stag A (.succ .zero) .zero B ea) (.base ho)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ he eb))⟩

theorem internalFinishCharacterization : Targets.InternalFinishCharacterization := by
  intro n p ftag ptag ctag hf hp hc ctx context raw tail lines requested formula certificate
  let T := GorbowPRNumeralCalculation.Theory p
  let V := finalCall ftag (successfulState ptag ctag context raw tail lines) requested formula certificate
  let E := Formula.equal V (.succ .zero)
  let H := Formula.conj (.equal requested context) (.equal formula (.add raw raw))
  obtain ⟨he⟩ := EquationsProof.finalizerEquation p ftag ptag ctag hf hp hc context raw tail lines requested formula certificate
  obtain ⟨hsel,hl,hr⟩ := EquationsProof.comparisonNodes p ftag hf
  obtain ⟨hs⟩ := sound p (EquationsProof.checksTag ftag+1) (EquationsProof.leftTag ftag) (EquationsProof.rightTag ftag) hsel hl hr requested context formula (.add raw raw)
  obtain ⟨hc'⟩ := complete p (EquationsProof.checksTag ftag+1) (EquationsProof.leftTag ftag) (EquationsProof.rightTag ftag) hsel hl hr requested context formula (.add raw raw)
  have ea : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have ds : Derivation T (.imp E H) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.base hs) (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) ea)))
  have ha : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have dc : Derivation T (.imp H E) := Hilbert.Local.finish (Hilbert.Local.discharge
    (localTrans _ _ _ (.base he) (.mp (.base hc') ha)))
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) ds) dc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.ComparisonProof
