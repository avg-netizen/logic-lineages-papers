module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneImageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SurjectivityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof HistoryKernel

def rejects {ctx : Nat} (tag ptag : Nat) (index fuel out rest lines : Term ctx) : Formula ctx :=
  .neg (.equal (kernelCall tag (pairCall ptag .zero lines) index fuel) (pairCall ptag (.succ out) rest))

theorem substRejects {m n : Nat} (sub : Fin m → Term n) tag ptag (index fuel out rest lines : Term m) :
    substituteFormula sub (rejects tag ptag index fuel out rest lines) =
      rejects tag ptag (substitute sub index) (substitute sub fuel) (substitute sub out)
        (substitute sub rest) (substitute sub lines) := by
  simp only [rejects,kernelCall,substituteFormula,substPair,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem rejectsAt {ctx : Nat} tag ptag (index fuel out rest lines : Term ctx) :
    GorbowStandardInstances.instantiate
      (rejects tag ptag (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) (.var 0)) lines =
      rejects tag ptag index fuel out rest lines := by
  simp only [GorbowStandardInstances.instantiate,substRejects,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenRejects {ctx : Nat} tag ptag (index fuel out rest lines : Term ctx) :
    GorbowPACore.weaken (rejects tag ptag index fuel out rest lines) =
      rejects tag ptag (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) (liftTerm lines) := by
  rw [GorbowPACore.weaken,substRejects]
  rfl

noncomputable def rejectTransport {T : Sentence → Prop} {ctx : Nat} tag ptag
    (index fuel out rest a b : Term ctx) :
    Derivation T (.imp (.equal a b)
      (.imp (rejects tag ptag index fuel out rest a) (rejects tag ptag index fuel out rest b))) := by
  have h := Derivation.logical (A := T) (.equalityReplace
    (rejects tag ptag (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) (.var 0)) a b)
  rwa [GorbowPACore.logicalFormula,rejectsAt,rejectsAt] at h

theorem nonePositive {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel out rest code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (rejects tag ptag index fuel out rest (.succ code))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag + GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  let Q := rejects tag ptag index fuel out rest (.succ code)
  let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall cp A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
  have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
  obtain ⟨hn⟩ := NoneImageProof.noneConsReject p tag ptag ctag v l a x ht hp hc A B
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
  have hout : Hilbert.Local T (ctx+2) [H]
      (rejects tag ptag (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
        (liftTerm (liftTerm out)) (liftTerm (liftTerm rest)) (.succ C)) :=
    .mp (.mp (.base (rejectTransport tag ptag _ _ _ _ _ _)) hcons) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenRejects,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
  obtain ⟨hs⟩ := SurjectivityProof.internalPairSurjective n p cp hcp ctx code
  exact ⟨.mp helim hs⟩

theorem noneReject {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel out rest lines : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (rejects tag ptag index fuel out rest lines)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := rejects tag ptag index fuel out rest lines
  let E := Formula.equal lines .zero
  obtain ⟨hz⟩ := NoneImageProof.noneNilReject p tag ptag v l a x ht hp index fuel out rest
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (rejectTransport tag ptag index fuel out rest .zero lines))
      (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody lines
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm lines) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := nonePositive p tag ptag ctag v l a x ht hp hc
    (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) (.var (0 : Fin (ctx+1)))
  have hout : Hilbert.Local T (ctx+1) [H] (GorbowPACore.weaken Q) := by
    rw [show Q = rejects tag ptag index fuel out rest lines from rfl,weakenRejects]
    exact .mp (.mp (.base (rejectTransport tag ptag _ _ _ _ _ _))
      (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q
    ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T lines
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneProof
