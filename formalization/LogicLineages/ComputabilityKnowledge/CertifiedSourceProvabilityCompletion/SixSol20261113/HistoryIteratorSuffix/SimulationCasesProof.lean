module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SimulationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SimulationCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel RelationProof SimulationProof

theorem imageEvolves {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option lines new tail index fuel out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (evolves tag atag ptag (pairCall ptag option lines) new tail index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := evolves tag atag ptag (pairCall ptag option lines) new tail index fuel out rest
  let E := Formula.equal option .zero
  obtain ⟨hz⟩ := noneEvolves p tag atag ptag ctag v l a x ht hp hc lines new tail index fuel out rest
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have ep := StepSuffixProof.pairCongruence ptag .zero lines option lines
    (HistoryOrder.StepProof.localSym _ _ he) (.base (.logical (.reflexive lines)))
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (oldTransport tag atag ptag _ _ new tail index fuel out rest)) ep) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody option
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm option) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  have ep' := StepSuffixProof.pairCongruence ptag (.succ (.var 0)) (liftTerm lines) (liftTerm option) (liftTerm lines)
    (HistoryOrder.StepProof.localSym _ _ hh) (.base (.logical (.reflexive _)))
  obtain ⟨hn⟩ := someEvolves p tag atag ptag ctag v l a x ht ha hp hc (.var (0 : Fin (ctx+1)))
    (liftTerm lines) (liftTerm new) (liftTerm tail) (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)
  have hout : Hilbert.Local T (ctx+1) [H]
      (evolves tag atag ptag (pairCall ptag (liftTerm option) (liftTerm lines))
        (liftTerm new) (liftTerm tail) (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)) :=
    .mp (.mp (.base (oldTransport tag atag ptag _ _ _ _ _ _ _ _)) ep') (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenEvolves,liftTerm,renameTerm,substitute,RelationProof.substPair] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T option
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩

/-- Every raw input state is covered by internal pair surjectivity, not native codec totality. -/
theorem kernelEvolves {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new tail index fuel out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (evolves tag atag ptag old new tail index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := evolves tag atag ptag old new tail index fuel out rest
  let H := WitnessProof.secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm old)
  let C := liftTerm (liftTerm old)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall ptag A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨hi⟩ := imageEvolves p tag atag ptag ctag v l a x ht ha hp hc A B
    (liftTerm (liftTerm new)) (liftTerm (liftTerm tail)) (liftTerm (liftTerm index))
    (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
  have hout : Hilbert.Local T (ctx+2) [H]
      (evolves tag atag ptag C (liftTerm (liftTerm new)) (liftTerm (liftTerm tail)) (liftTerm (liftTerm index))
        (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))) :=
    .mp (.mp (.base (oldTransport tag atag ptag _ _ _ _ _ _ _ _)) hh) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenEvolves] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (WitnessProof.firstBody ptag old) Q ⟨hinner⟩
  obtain ⟨hs⟩ := SurjectivityProof.internalPairSurjective n p ptag hp ctx old
  exact ⟨.mp helim hs⟩

theorem kernelPreserves {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new tail index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (relation atag ptag old new tail)
        (relation atag ptag (kernelCall tag old index fuel) (kernelCall tag new index fuel) tail))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let R := relation atag ptag old new tail
  let K := kernelCall tag old index fuel
  let N := kernelCall tag new index fuel
  let Q := inner atag ptag (liftTerm K) (liftTerm N) (liftTerm tail) (.var (0 : Fin (ctx+1)))
  let B := body atag ptag (liftTerm (liftTerm K)) (liftTerm (liftTerm N)) (liftTerm (liftTerm tail))
    (.var (1 : Fin (ctx+2))) (.var 0)
  obtain ⟨hi⟩ := kernelEvolves p tag atag ptag ctag v l a x ht ha hp hc
    (liftTerm (liftTerm old)) (liftTerm (liftTerm new)) (liftTerm (liftTerm tail))
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (.var (1 : Fin (ctx+2))) (.var 0)
  have hh : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken R)) B) := by
    simpa only [evolves,R,B,K,N,GorbowPACore.weaken,substRelation,liftTerm,renameTerm,substKernel] using hi
  have hinner : Derivation T (.imp (GorbowPACore.weaken R) Q) := universalUnder (GorbowPACore.weaken R) B hh
  exact ⟨universalUnder R Q hinner⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SimulationCasesProof
