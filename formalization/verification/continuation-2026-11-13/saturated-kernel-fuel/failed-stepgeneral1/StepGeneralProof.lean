module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SurjectivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepGeneralProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix.WitnessProof StepProof

theorem substTransport {m n : Nat} (sub : Fin m → Term n) tag ptag (index s t h lines out rest : Term m) :
 substituteFormula sub (stepTransport tag ptag index s t h lines out rest) =
 stepTransport tag ptag (substitute sub index) (substitute sub s) (substitute sub t)
  (substitute sub h) (substitute sub lines) (substitute sub out) (substitute sub rest) := by
 simp only [stepTransport,kernelCall,substituteFormula,FuelWitness.ExtractionLogicProof.substOrder,substPair,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem transportAt {ctx : Nat} tag ptag (index s t h out rest lines : Term ctx) :
 GorbowStandardInstances.instantiate
  (stepTransport tag ptag (liftTerm index) (liftTerm s) (liftTerm t) (liftTerm h) (.var 0) (liftTerm out) (liftTerm rest)) lines =
 stepTransport tag ptag index s t h lines out rest := by
 simp only [GorbowStandardInstances.instantiate,substTransport,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenTransport {ctx : Nat} tag ptag (index s t h lines out rest : Term ctx) :
 GorbowPACore.weaken (stepTransport tag ptag index s t h lines out rest) =
 stepTransport tag ptag (liftTerm index) (liftTerm s) (liftTerm t) (liftTerm h) (liftTerm lines) (liftTerm out) (liftTerm rest) := by
 rw [GorbowPACore.weaken,substTransport]
 rfl

noncomputable def linesTransport {T : Sentence → Prop} {ctx : Nat} tag ptag
 (index s t h out rest a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (stepTransport tag ptag index s t h a out rest) (stepTransport tag ptag index s t h b out rest))) := by
 have he := Derivation.logical (A := T) (.equalityReplace
  (stepTransport tag ptag (liftTerm index) (liftTerm s) (liftTerm t) (liftTerm h) (.var 0) (liftTerm out) (liftTerm rest)) a b)
 rwa [GorbowPACore.logicalFormula,transportAt,transportAt] at he

theorem positiveStep {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,kernel v l a (SaturatedAxiomLeaf.saturated x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index s t h out rest code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stepTransport tag ptag index s t h (.succ code) out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let cp := ctag + GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 let Q := stepTransport tag ptag index s t h (.succ code) out rest
 let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
 let C := liftTerm (liftTerm code)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall cp A B) C) := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
 have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
 obtain ⟨hn⟩ := consStep p tag ptag ctag v l a x ht hp hc
  (liftTerm (liftTerm index)) (liftTerm (liftTerm s)) (liftTerm (liftTerm t)) (liftTerm (liftTerm h))
  A B (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
 have hout : Hilbert.Local T (ctx+2) [H]
  (stepTransport tag ptag (liftTerm (liftTerm index)) (liftTerm (liftTerm s)) (liftTerm (liftTerm t))
   (liftTerm (liftTerm h)) (.succ C) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))) :=
  .mp (.mp (.base (linesTransport tag ptag _ _ _ _ _ _ _ _)) hcons) (.base hn)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,C,weakenTransport,liftTerm,renameTerm,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
 obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
 exact ⟨.mp helim hs⟩

theorem internalStep : Targets.InternalStep := by
 intro v l a x n p tag ptag ctag ht hp hc ctx index s t h lines out rest
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := stepTransport tag ptag index s t h lines out rest
 let E := Formula.equal lines .zero
 obtain ⟨hz⟩ := nilStep p tag ptag v l a x ht hp index s t h out rest
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (linesTransport tag ptag index s t h out rest .zero lines))
   (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
 let H := HistoryOrder.SupportProof.predBody lines
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm lines) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := positiveStep p tag ptag ctag v l a x ht hp hc
  (liftTerm index) (liftTerm s) (liftTerm t) (liftTerm h) (liftTerm out) (liftTerm rest) (.var (0 : Fin (ctx+1)))
 have hout : Hilbert.Local T (ctx+1) [H] (GorbowPACore.weaken Q) := by
  rw [show Q = stepTransport tag ptag index s t h lines out rest from rfl,weakenTransport]
  exact .mp (.mp (.base (linesTransport tag ptag _ _ _ _ _ _ _ _)) (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
 obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
 obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T lines
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepGeneralProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepGeneralProof
