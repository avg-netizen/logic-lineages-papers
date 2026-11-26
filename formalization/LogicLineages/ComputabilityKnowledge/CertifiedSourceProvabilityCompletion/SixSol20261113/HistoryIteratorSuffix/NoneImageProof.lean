module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StateEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneImageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel

/-- Actual pair injectivity distinguishes NONE from every SOME, including SOME zero. -/
theorem noneNotSome {n ctx : Nat} (p : Program n) ptag
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (lines out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.neg (.equal (pairCall ptag .zero lines) (pairCall ptag (.succ out) rest)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (pairCall ptag .zero lines) (pairCall ptag (.succ out) rest)
  obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx .zero lines (.succ out) rest
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have hpair := Hilbert.Local.mp (.base hi) hh
  have he : Hilbert.Local T ctx [H] (.equal (.zero : Term ctx) (.succ out)) :=
    .mp (.base (.logical (.andLeft _ _))) hpair
  have hs := HistoryOrder.StepProof.localSym _ _ he
  exact ⟨Hilbert.modusTollens (Hilbert.Local.finish (Hilbert.Local.discharge hs))
    (.arithmetic (.succNotZero out))⟩

/-- Rejection is stable when the input history is already NONE. This is NOT
preservation of a missing reference when appending to a successful history. -/
theorem noneConsReject {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line rest index fuel out remaining : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.neg (.equal (kernelCall tag (pairCall ptag .zero (HistoryLookup.consCall ctag line rest)) index fuel)
        (pairCall ptag (.succ out) remaining)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (kernelCall tag (pairCall ptag .zero (HistoryLookup.consCall ctag line rest)) index fuel)
    (pairCall ptag (.succ out) remaining)
  obtain ⟨he⟩ := StateEquationsProof.kernelNoneCons p tag ptag ctag v l a x ht hp hc line rest index fuel
  obtain ⟨hn⟩ := noneNotSome p ptag hp rest out remaining
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have hout := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) hh
  exact ⟨Hilbert.modusTollens (Hilbert.Local.finish (Hilbert.Local.discharge hout)) hn⟩

theorem noneNilReject {n ctx : Nat} (p : Program n) tag ptag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index fuel out remaining : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.neg (.equal (kernelCall tag (pairCall ptag .zero .zero) index fuel)
        (pairCall ptag (.succ out) remaining)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (kernelCall tag (pairCall ptag .zero .zero) index fuel)
    (pairCall ptag (.succ out) remaining)
  obtain ⟨he⟩ := StateEquationsProof.kernelNil p tag ptag v l a x ht hp (.zero : Term ctx) index fuel
  obtain ⟨hn⟩ := noneNotSome p ptag hp (.zero : Term ctx) out remaining
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have hout := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) hh
  exact ⟨Hilbert.modusTollens (Hilbert.Local.finish (Hilbert.Local.discharge hout)) hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneImageProof
