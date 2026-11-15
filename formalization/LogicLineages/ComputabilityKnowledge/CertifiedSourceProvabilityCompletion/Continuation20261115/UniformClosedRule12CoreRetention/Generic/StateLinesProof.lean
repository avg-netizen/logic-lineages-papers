module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.StateCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.State.LinesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalStateRetention RawUniversalStateRetention.TransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix HistoryIteratorSuffix.WitnessProof HistoryIteratorSuffix.StepSuffixProof
open RawUniversalStateRetention.TransportProof
variable (test : Program 1)

theorem positiveStep {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
    (hn : (nodes p)[nt]? = some ⟨3,kernel v (extend test l) a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h out rest code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (preserves ot nt ptag (pairCall ptag (.succ h) (.succ code)) index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag + GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  let Q := preserves ot nt ptag (pairCall ptag (.succ h) (.succ code)) index fuel out rest
  let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall cp A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
  have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
  obtain ⟨hn⟩ := CasesProof.consStep test p ot nt ptag ctag v l a x ho hn hp hc
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (liftTerm (liftTerm h)) 
    A B (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
  have hout : Hilbert.Local T (ctx+2) [H]
      (preserves ot nt ptag (pairCall ptag (.succ (liftTerm (liftTerm h))) (.succ C))
        (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))) :=
    .mp (.mp (.base (moveLines ot nt ptag _ _ _ _ _ _ _)) hcons) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenPreserves,substPair,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
  obtain ⟨hs⟩ := SurjectivityProof.internalPairSurjective n p cp hcp ctx code
  exact ⟨.mp helim hs⟩

theorem generalStep {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
    (hn : (nodes p)[nt]? = some ⟨3,kernel v (extend test l) a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h out rest lines : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (preserves ot nt ptag (pairCall ptag (.succ h) lines) index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := preserves ot nt ptag (pairCall ptag (.succ h) lines) index fuel out rest
  let E := Formula.equal lines .zero
  obtain ⟨hz⟩ := CasesProof.nilStep test p ot nt ptag ctag v l a x ho hn hp hc index fuel h out rest
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (moveLines ot nt ptag h .zero lines index fuel out rest))
      (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody lines
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm lines) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := positiveStep test p ot nt ptag ctag v l a x ho hn hp hc
    (liftTerm index) (liftTerm fuel) (liftTerm h)  (liftTerm out) (liftTerm rest) (.var (0 : Fin (ctx+1)))
  have hout : Hilbert.Local T (ctx+1) [H] (GorbowPACore.weaken Q) := by
    rw [show Q = preserves ot nt ptag (pairCall ptag (.succ h) lines) index fuel out rest from rfl,weakenPreserves]
    simp only [liftTerm,renameTerm,substPair,substitute]
    exact .mp (.mp (.base (moveLines ot nt ptag _ _ _ _ _ _ _))
      (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q
    ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T lines
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.State.LinesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.State.LinesProof
