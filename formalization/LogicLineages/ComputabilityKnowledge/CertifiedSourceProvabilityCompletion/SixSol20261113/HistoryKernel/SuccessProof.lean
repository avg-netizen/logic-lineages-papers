module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.OptionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.SuccessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FieldsProof EntryProof TransitionEquationsProof OptionProof

theorem successOption {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest out : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (kernelCall tag (activeState ptag ctag h line rest) index fuel) (pairCall ptag (.succ out) rest))
        (.equal (optionValue tag v l a x index fuel h line) (.succ out)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (kernelCall tag (activeState ptag ctag h line rest) index fuel) (pairCall ptag (.succ out) rest)
  obtain ⟨hpair,hs,he,hd,hcons⟩ := kernelNodes p tag v l a x ht
  obtain ⟨hn⟩ := NormalProof.kernelEquation p tag ptag ctag v l a x ht hp hc index fuel h line rest
  obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p ptag (outputPairTag tag v l a x) hp hpair (.succ out) rest
  obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p (outputPairTag tag v l a x) hpair ctx
    (optionValue tag v l a x index fuel h line) rest (.succ out) rest
  have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have eqpair := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hn)) (localTrans _ _ _ e (.base hcopy))
  have pieces := Hilbert.Local.mp (.base hinj) eqpair
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (.logical (.andLeft _ _))) pieces))⟩

theorem successfulParts {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest out : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (kernelCall tag (activeState ptag ctag h line rest) index fuel) (pairCall ptag (.succ out) rest))
        (.conj (.equal (HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line) (.succ .zero))
          (.equal (newHistory (someTag tag v l a x) h line) out)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (kernelCall tag (activeState ptag ctag h line rest) index fuel) (pairCall ptag (.succ out) rest)
  let O := optionValue tag v l a x index fuel h line
  let C := HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line
  let N := newHistory (someTag tag v l a x) h line
  let H := Formula.conj (.equal C (.succ .zero)) (.equal O (.succ N))
  let Q := Formula.conj (.equal C (.succ .zero)) (.equal N out)
  obtain ⟨hs⟩ := successOption p tag ptag ctag v l a x ht hp hc index fuel h line rest out
  obtain ⟨hg⟩ := optionGraph p tag v l a x ht index fuel h line
  have hz : Hilbert.Local T ctx [E] (.imp (.equal O .zero) Q) := by
    have e : Hilbert.Local T ctx [.equal O .zero,E] E := .hypothesis (by simp)
    have z : Hilbert.Local T ctx [.equal O .zero,E] (.equal O .zero) := .hypothesis List.mem_cons_self
    have pos := Hilbert.Local.mp (.base hs) e
    have bad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ pos) z
    exact Hilbert.Local.discharge (Hilbert.Local.explosion Q bad (.base (.arithmetic (.succNotZero out))))
  have hh : Hilbert.Local T ctx [E] (.imp H Q) := by
    have e : Hilbert.Local T ctx [H,E] E := .hypothesis (by simp)
    have hh : Hilbert.Local T ctx [H,E] H := .hypothesis List.mem_cons_self
    have hcheck := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
    have hvalue := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
    have pos := Hilbert.Local.mp (.base hs) e
    have sn := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hvalue) pos
    have hn := Hilbert.Local.mp (.base (.arithmetic (.succInjective N out))) sn
    exact Hilbert.Local.discharge (.mp (.mp (.base (.logical (.andIntro _ _))) hcheck) hn)
  have result := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hz) hh) (.base hg)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge result)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.SuccessProof
