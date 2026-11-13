module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StateEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepSuffixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel HistoryKernel.TransitionEquationsProof

def suffix {ctx : Nat} (tag atag ptag : Nat) (index fuel h tail lines out rest : Term ctx) : Formula ctx :=
  .imp (.equal (kernelCall tag (pairCall ptag (.succ h) lines) index fuel) (pairCall ptag (.succ out) rest))
    (.equal (kernelCall tag (pairCall ptag (.succ (pairCall atag h tail)) lines) index fuel)
      (pairCall ptag (.succ (pairCall atag out tail)) rest))

noncomputable def pairCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (a b c d : Term ctx) (ha : Hilbert.Local T ctx G (.equal a c))
    (hb : Hilbert.Local T ctx G (.equal b d)) :
    Hilbert.Local T ctx G (.equal (pairCall tag a b) (pairCall tag c d)) := by
  have h1 := localUnary (pairCall tag (.var 0) (liftTerm b)) a c ha
  have h2 := localUnary (pairCall tag (liftTerm c) (.var 0)) b d hb
  simp only [pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at h1 h2
  exact localTrans _ _ _ h1 h2

theorem nilSuffix {n ctx : Nat} (p : Program n) tag atag ptag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index fuel h tail out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (suffix tag atag ptag index fuel h tail .zero out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (kernelCall tag (pairCall ptag (.succ h) .zero) index fuel) (pairCall ptag (.succ out) rest)
  obtain ⟨hz⟩ := StateEquationsProof.kernelNil p tag ptag v l a x ht hp (.succ h) index fuel
  obtain ⟨hn⟩ := StateEquationsProof.kernelNil p tag ptag v l a x ht hp (.succ (pairCall atag h tail)) index fuel
  obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx (.succ h) .zero (.succ out) rest
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have ep := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hz)) hh
  have both := Hilbert.Local.mp (.base hi) ep
  have eh : Hilbert.Local T ctx [H] (.equal h out) :=
    .mp (.base (.arithmetic (.succInjective h out))) (.mp (.base (.logical (.andLeft _ _))) both)
  have er : Hilbert.Local T ctx [H] (.equal (.zero : Term ctx) rest) := .mp (.base (.logical (.andRight _ _))) both
  have ea := pairCongruence atag h tail out tail eh (.base (.logical (.reflexive tail)))
  have es := localUnary (.succ (.var 0)) _ _ ea
  have eo := pairCongruence ptag _ .zero _ rest es er
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hn) eo))⟩

theorem consSuffix {n ctx : Nat} (p : Program n) tag atag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h tail line lines out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (suffix tag atag ptag index fuel h tail (HistoryLookup.consCall ctag line lines) out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (kernelCall tag (activeState ptag ctag h line lines) index fuel) (pairCall ptag (.succ out) rest)
  obtain ⟨he⟩ := HistoryKernel.NormalProof.kernelEquation p tag ptag ctag v l a x ht hp hc index fuel h line lines
  have hn := nextInstalled p tag v l a x ht
  have hop := Equations.functionChild p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) hn
  obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (outputPairTag tag v l a x) ptag hop hp
    (optionValue tag v l a x index fuel h line) lines
  have en : Derivation T (.equal (kernelCall tag (activeState ptag ctag h line lines) index fuel)
      (pairCall ptag (optionValue tag v l a x index fuel h line) lines)) := Logic.trans _ _ _ he hcopy
  obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx
    (optionValue tag v l a x index fuel h line) lines (.succ out) rest
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have ep := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ en)) hh
  have both := Hilbert.Local.mp (.base hi) ep
  have er : Hilbert.Local T ctx [H] (.equal lines rest) := .mp (.base (.logical (.andRight _ _))) both
  have eo := pairCongruence ptag (.succ out) lines (.succ out) rest (.base (.logical (.reflexive _))) er
  have old := localTrans _ _ _ hh (HistoryOrder.StepProof.localSym _ _ eo)
  obtain ⟨hs⟩ := HistoryKernel.SuffixProof.internalStepSuffix v l a x n p tag atag ptag ctag ht ha hp hc ctx index fuel h tail line lines out
  have next := Hilbert.Local.mp (.base hs) old
  have eo' := pairCongruence ptag (.succ (pairCall atag out tail)) lines (.succ (pairCall atag out tail)) rest (.base (.logical (.reflexive _))) er
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ next eo'))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepSuffixProof
