module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepSuffixProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SurjectivityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepGeneralProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof HistoryKernel StepSuffixProof

theorem substSuffix {m n : Nat} (sub : Fin m → Term n) tag atag ptag (index fuel h tail out rest lines : Term m) :
    substituteFormula sub (suffix tag atag ptag index fuel h tail lines out rest) =
      suffix tag atag ptag (substitute sub index) (substitute sub fuel) (substitute sub h) (substitute sub tail)
        (substitute sub lines) (substitute sub out) (substitute sub rest) := by
  simp only [suffix,kernelCall,substituteFormula,substPair,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem suffixAt {ctx : Nat} tag atag ptag (index fuel h tail out rest lines : Term ctx) :
    GorbowStandardInstances.instantiate
      (suffix tag atag ptag (liftTerm index) (liftTerm fuel) (liftTerm h) (liftTerm tail) (.var 0) (liftTerm out) (liftTerm rest)) lines =
      suffix tag atag ptag index fuel h tail lines out rest := by
  simp only [GorbowStandardInstances.instantiate,substSuffix,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenSuffix {ctx : Nat} tag atag ptag (index fuel h tail out rest lines : Term ctx) :
    GorbowPACore.weaken (suffix tag atag ptag index fuel h tail lines out rest) =
      suffix tag atag ptag (liftTerm index) (liftTerm fuel) (liftTerm h) (liftTerm tail) (liftTerm lines) (liftTerm out) (liftTerm rest) := by
  rw [GorbowPACore.weaken,substSuffix]
  rfl

noncomputable def suffixTransport {T : Sentence → Prop} {ctx : Nat} tag atag ptag
    (index fuel h tail out rest a b : Term ctx) :
    Derivation T (.imp (.equal a b)
      (.imp (suffix tag atag ptag index fuel h tail a out rest) (suffix tag atag ptag index fuel h tail b out rest))) := by
  have h := Derivation.logical (A := T) (.equalityReplace
    (suffix tag atag ptag (liftTerm index) (liftTerm fuel) (liftTerm h) (liftTerm tail) (.var 0) (liftTerm out) (liftTerm rest)) a b)
  rwa [GorbowPACore.logicalFormula,suffixAt,suffixAt] at h

theorem positiveSuffix {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h tail out rest code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (suffix tag atag ptag index fuel h tail (.succ code) out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag + GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  let Q := suffix tag atag ptag index fuel h tail (.succ code) out rest
  let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall cp A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
  have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
  obtain ⟨hn⟩ := StepSuffixProof.consSuffix p tag atag ptag ctag v l a x ht ha hp hc
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (liftTerm (liftTerm h)) (liftTerm (liftTerm tail))
    A B (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
  have hout : Hilbert.Local T (ctx+2) [H]
      (suffix tag atag ptag (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
        (liftTerm (liftTerm h)) (liftTerm (liftTerm tail)) (.succ C) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))) :=
    .mp (.mp (.base (suffixTransport tag atag ptag _ _ _ _ _ _ _ _)) hcons) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenSuffix,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
  obtain ⟨hs⟩ := SurjectivityProof.internalPairSurjective n p cp hcp ctx code
  exact ⟨.mp helim hs⟩

theorem generalSuffix {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h tail out rest lines : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (suffix tag atag ptag index fuel h tail lines out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := suffix tag atag ptag index fuel h tail lines out rest
  let E := Formula.equal lines .zero
  obtain ⟨hz⟩ := StepSuffixProof.nilSuffix p tag atag ptag v l a x ht hp index fuel h tail out rest
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (suffixTransport tag atag ptag index fuel h tail out rest .zero lines))
      (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody lines
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm lines) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := positiveSuffix p tag atag ptag ctag v l a x ht ha hp hc
    (liftTerm index) (liftTerm fuel) (liftTerm h) (liftTerm tail) (liftTerm out) (liftTerm rest) (.var (0 : Fin (ctx+1)))
  have hout : Hilbert.Local T (ctx+1) [H] (GorbowPACore.weaken Q) := by
    rw [show Q = suffix tag atag ptag index fuel h tail lines out rest from rfl,weakenSuffix]
    exact .mp (.mp (.base (suffixTransport tag atag ptag _ _ _ _ _ _ _ _))
      (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q
    ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T lines
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepGeneralProof
