module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SurjectivityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ReconstructionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations
open GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof

def reconstructed {ctx : Nat} (ptag ltag rtag : Nat) (code : Term ctx) : Formula ctx :=
  .equal (HistoryKernel.pairCall ptag (call ltag (code ::ᵥ nil)) (call rtag (code ::ᵥ nil))) code

theorem substReconstructed {m n : Nat} (sub : Fin m → Term n) ptag ltag rtag (code : Term m) :
    substituteFormula sub (reconstructed ptag ltag rtag code) =
      reconstructed ptag ltag rtag (substitute sub code) := by
  simp only [reconstructed,substituteFormula,substPair,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil]

theorem weakenReconstructed {ctx : Nat} ptag ltag rtag (code : Term ctx) :
    GorbowPACore.weaken (reconstructed ptag ltag rtag code) =
      reconstructed ptag ltag rtag (liftTerm code) := by
  rw [GorbowPACore.weaken,substReconstructed]
  rfl

noncomputable def pairCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (a b c d : Term ctx) (ha : Hilbert.Local T ctx G (.equal a c))
    (hb : Hilbert.Local T ctx G (.equal b d)) :
    Hilbert.Local T ctx G (.equal (HistoryKernel.pairCall tag a b) (HistoryKernel.pairCall tag c d)) := by
  have h1 := localUnary (HistoryKernel.pairCall tag (.var 0) (liftTerm b)) a c ha
  have h2 := localUnary (HistoryKernel.pairCall tag (liftTerm c) (.var 0)) b d hb
  simp only [substPair,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at h1 h2
  exact localTrans _ _ _ h1 h2

theorem internalDecoderReconstruction : Targets.InternalDecoderReconstruction := by
  intro n p ptag ltag rtag hp hl hr ctx code
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := reconstructed ptag ltag rtag code
  let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  let V := HistoryKernel.pairCall ptag A B
  have hh : Hilbert.Local T (ctx+2) [H] (.equal V C) := .hypothesis List.mem_cons_self
  obtain ⟨hleft⟩ := HistoryLookup.DestructorProof.decoderCrossPair p ltag ptag false hl hp A B
  obtain ⟨hright⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp A B
  have lc := localUnary (call ltag (.var 0 ::ᵥ nil)) V C hh
  have rc := localUnary (call rtag (.var 0 ::ᵥ nil)) V C hh
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at lc rc
  have le : Hilbert.Local T (ctx+2) [H] (.equal (call ltag (C ::ᵥ nil)) A) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ lc) (.base hleft)
  have re : Hilbert.Local T (ctx+2) [H] (.equal (call rtag (C ::ᵥ nil)) B) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ rc) (.base hright)
  have hout : Hilbert.Local T (ctx+2) [H] (reconstructed ptag ltag rtag C) :=
    localTrans _ _ _ (pairCongruence ptag _ _ A B le re) hh
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenReconstructed] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody ptag code) Q ⟨hinner⟩
  obtain ⟨hs⟩ := SurjectivityProof.internalPairSurjective n p ptag hp ctx code
  exact ⟨.mp helim hs⟩

/-- Actual destructor normalization on every positive input, not just cons images. -/
theorem positiveDestructor {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨1,.composition (HistoryDecoder.decoder right)
      (fun _ : Fin 1 => HistoryCodec.predecessor)⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (.succ code ::ᵥ nil)) (call (tag+1) (code ::ᵥ nil)))) := by
  obtain ⟨he⟩ := HistoryLookup.DestructorProof.destructorEquation p tag right ht (.succ code)
  have hp := Equations.argumentChild p tag (HistoryDecoder.decoder right)
    (fun _ : Fin 1 => HistoryCodec.predecessor) ht 0
  obtain ⟨hpred⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p
    (HistoryLookup.DestructorProof.predTag right tag) hp ctx code
  exact ⟨Logic.trans _ _ _ he (HistoryLookup.DestructorProof.unaryCallCongruence (tag+1) _ _ hpred)⟩

theorem internalListReconstruction : Targets.InternalListReconstruction := by
  intro n p ctag htag ttag hc hh ht ctx code
  let cp := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  have hl := Equations.functionChild p htag (HistoryDecoder.decoder false)
    (fun _ : Fin 1 => HistoryCodec.predecessor) hh
  have hr := Equations.functionChild p ttag (HistoryDecoder.decoder true)
    (fun _ : Fin 1 => HistoryCodec.predecessor) ht
  obtain ⟨hrec⟩ := internalDecoderReconstruction n p cp (htag+1) (ttag+1) hp hl hr ctx code
  obtain ⟨heh⟩ := positiveDestructor p htag false hh code
  obtain ⟨het⟩ := positiveDestructor p ttag true ht code
  let A := call htag (.succ code ::ᵥ nil)
  let B := call ttag (.succ code ::ᵥ nil)
  obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx A B
  have hpair : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryKernel.pairCall cp A B) code) :=
    Hilbert.Local.finish (localTrans _ _ _ (pairCongruence cp _ _ _ _ (.base heh) (.base het)) (.base hrec))
  exact ⟨Logic.trans _ _ _ hcons (Logic.unary (.succ (.var 0)) _ _ hpair)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ReconstructionProof
