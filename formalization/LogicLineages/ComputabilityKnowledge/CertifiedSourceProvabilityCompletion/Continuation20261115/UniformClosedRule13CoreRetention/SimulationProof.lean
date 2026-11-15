module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.SimulationBasicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Simulation.Proof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalSimulation RawUniversalSimulation.RelationProof RawUniversalSimulation.SupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open RawUniversalSimulation.RelationProof RawUniversalSimulation.SupportProof BasicProof
theorem imageEvolves {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
    (hn : (nodes p)[nt]? = some ⟨3,kernel v (UniformClosedRule13.logicalLeaf l) a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option lines new  index fuel out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (evolves ot nt ptag (pairCall ptag option lines) new  index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := evolves ot nt ptag (pairCall ptag option lines) new  index fuel out rest
  let E := Formula.equal option .zero
  obtain ⟨hz⟩ := noneEvolves p ot nt ptag ctag v l a x ho hn hp hc lines new  index fuel out rest
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have ep := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag .zero lines option lines
    (HistoryOrder.StepProof.localSym _ _ he) (.base (.logical (.reflexive lines)))
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (oldTransport ot nt ptag _ _ new  index fuel out rest)) ep) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody option
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm option) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  have ep' := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag (.succ (.var 0)) (liftTerm lines) (liftTerm option) (liftTerm lines)
    (HistoryOrder.StepProof.localSym _ _ hh) (.base (.logical (.reflexive _)))
  obtain ⟨hn⟩ := someEvolves p ot nt ptag ctag v l a x ho hn hp hc (.var (0 : Fin (ctx+1)))
    (liftTerm lines) (liftTerm new)  (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)
  have hout : Hilbert.Local T (ctx+1) [H]
      (evolves ot nt ptag (pairCall ptag (liftTerm option) (liftTerm lines))
        (liftTerm new)  (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)) :=
    .mp (.mp (.base (oldTransport ot nt ptag _ _ _ _ _ _ _)) ep') (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenEvolves,liftTerm,renameTerm,substitute,RawUniversalSimulation.RelationProof.substPair] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T option
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩

/-- Every raw input state is covered by internal pair surjectivity, not native codec totality. -/
theorem kernelEvolves {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
    (hn : (nodes p)[nt]? = some ⟨3,kernel v (UniformClosedRule13.logicalLeaf l) a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new  index fuel out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (evolves ot nt ptag old new  index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := evolves ot nt ptag old new  index fuel out rest
  let H := HistoryIteratorSuffix.WitnessProof.secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm old)
  let C := liftTerm (liftTerm old)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall ptag A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨hi⟩ := imageEvolves p ot nt ptag ctag v l a x ho hn hp hc A B
    (liftTerm (liftTerm new))  (liftTerm (liftTerm index))
    (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
  have hout : Hilbert.Local T (ctx+2) [H]
      (evolves ot nt ptag C (liftTerm (liftTerm new))  (liftTerm (liftTerm index))
        (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))) :=
    .mp (.mp (.base (oldTransport ot nt ptag _ _ _ _ _ _ _)) hh) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenEvolves] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (HistoryIteratorSuffix.WitnessProof.firstBody ptag old) Q ⟨hinner⟩
  obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p ptag hp ctx old
  exact ⟨.mp helim hs⟩

theorem kernelPreserves {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
    (hn : (nodes p)[nt]? = some ⟨3,kernel v (UniformClosedRule13.logicalLeaf l) a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (old new  index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (relation ptag old new )
        (relation ptag (kernelCall ot old index fuel) (kernelCall nt new index fuel) ))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let R := relation ptag old new 
  let K := kernelCall ot old index fuel
  let N := kernelCall nt new index fuel
  let Q := inner ptag (liftTerm K) (liftTerm N)  (.var (0 : Fin (ctx+1)))
  let B := body ptag (liftTerm (liftTerm K)) (liftTerm (liftTerm N)) 
    (.var (1 : Fin (ctx+2))) (.var 0)
  obtain ⟨hi⟩ := kernelEvolves p ot nt ptag ctag v l a x ho hn hp hc
    (liftTerm (liftTerm old)) (liftTerm (liftTerm new)) 
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (.var (1 : Fin (ctx+2))) (.var 0)
  have hh : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken R)) B) := by
    simpa only [evolves,R,B,K,N,GorbowPACore.weaken,substRelation,liftTerm,renameTerm,substKernel] using hi
  have hinner : Derivation T (.imp (GorbowPACore.weaken R) Q) := universalUnder (GorbowPACore.weaken R) B hh
  exact ⟨universalUnder R Q hinner⟩
theorem internalKernelSimulation : Targets.InternalKernelSimulation := by
 intro n p v l a x ot nt ptag ctag ho hn hp hc ctx old new index fuel
 exact kernelPreserves p ot nt ptag ctag v l a x ho hn hp hc old new index fuel

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Simulation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Simulation.Proof
