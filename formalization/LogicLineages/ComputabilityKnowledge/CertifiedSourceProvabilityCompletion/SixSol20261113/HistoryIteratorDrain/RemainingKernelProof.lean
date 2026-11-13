module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingImageProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingKernelProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix.WitnessProof RemainingEquationsProof

def kernelEquation {ctx : Nat} (tag dtag ttag : Nat) (state index fuel : Term ctx) : Formula ctx :=
  .equal (decoded dtag (kernelCall tag state index fuel)) (decoded ttag (decoded dtag state))

theorem substKernelEquation {m n : Nat} (sub : Fin m → Term n) tag dtag ttag (state index fuel : Term m) :
    substituteFormula sub (kernelEquation tag dtag ttag state index fuel) =
      kernelEquation tag dtag ttag (substitute sub state) (substitute sub index) (substitute sub fuel) := by
  simp only [kernelEquation,decoded,kernelCall,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem equationAt {ctx : Nat} tag dtag ttag (state index fuel : Term ctx) :
    GorbowStandardInstances.instantiate (kernelEquation tag dtag ttag (.var 0) (liftTerm index) (liftTerm fuel)) state =
      kernelEquation tag dtag ttag state index fuel := by
  simp only [GorbowStandardInstances.instantiate,substKernelEquation,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem weakenEquation {ctx : Nat} tag dtag ttag (state index fuel : Term ctx) :
    GorbowPACore.weaken (kernelEquation tag dtag ttag state index fuel) =
      kernelEquation tag dtag ttag (liftTerm state) (liftTerm index) (liftTerm fuel) := by
  rw [GorbowPACore.weaken,substKernelEquation]
  rfl
noncomputable def stateTransport {T : Sentence → Prop} {ctx : Nat} tag dtag ttag (s t index fuel : Term ctx) :
    Derivation T (.imp (.equal s t) (.imp (kernelEquation tag dtag ttag s index fuel) (kernelEquation tag dtag ttag t index fuel))) := by
  have he := Derivation.logical (A := T) (.equalityReplace (kernelEquation tag dtag ttag (.var 0) (liftTerm index) (liftTerm fuel)) s t)
  rwa [GorbowPACore.logicalFormula,equationAt,equationAt] at he

theorem imageRemaining {n ctx : Nat} (p : Program n) (tag dtag ttag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (htt : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option lines index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (kernelEquation tag dtag ttag (pairCall ptag option lines) index fuel)) := by
  obtain ⟨he⟩ := RemainingImageProof.allImage p tag dtag ttag ptag ctag v l a x ht hd htt hp hc option lines index fuel
  obtain ⟨hdp⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag ptag true hd hp option lines
  have htail := HistoryLookup.DestructorProof.unaryCallCongruence ttag _ _ hdp
  exact ⟨Logic.trans _ _ _ he (Support.equalitySymmetry _ _ htail)⟩

theorem kernelRemaining {n ctx : Nat} (p : Program n) (tag dtag ttag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (htt : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (state index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (kernelEquation tag dtag ttag state index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := kernelEquation tag dtag ttag state index fuel
  let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm state)
  let C := liftTerm (liftTerm state)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall ptag A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨hi⟩ := imageRemaining p tag dtag ttag ptag ctag v l a x ht hd htt hp hc A B
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
  have hout : Hilbert.Local T (ctx+2) [H] (kernelEquation tag dtag ttag C (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))) :=
    .mp (.mp (.base (stateTransport tag dtag ttag _ _ _ _)) hh) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenEquation] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody ptag state) Q ⟨hinner⟩
  obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p ptag hp ctx state
  exact ⟨.mp helim hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingKernelProof
