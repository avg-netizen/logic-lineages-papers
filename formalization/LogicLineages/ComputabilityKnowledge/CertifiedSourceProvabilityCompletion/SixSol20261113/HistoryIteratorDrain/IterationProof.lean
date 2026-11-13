module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingKernelProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.DropInductionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations
open GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix.IterationProof (substIteration)

def template {ctx : Nat} (itag dtag dropTag ptag : Nat) (option lines index fuel : Term ctx) : Formula (ctx+1) :=
  .equal (remainingCall dtag itag ptag (.var 0) (liftTerm option) (liftTerm lines) (liftTerm index) (liftTerm fuel))
    (dropCall dropTag (.var 0) (liftTerm lines))

theorem substRemaining {m n : Nat} (sub : Fin m → Term n) dtag itag ptag (count option lines index fuel : Term m) :
    substitute sub (remainingCall dtag itag ptag count option lines index fuel) =
      remainingCall dtag itag ptag (substitute sub count) (substitute sub option) (substitute sub lines)
        (substitute sub index) (substitute sub fuel) := by
  simp only [remainingCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substIteration,
    HistoryIteratorSuffix.WitnessProof.substPair]
theorem templateAt {ctx : Nat} itag dtag dropTag ptag (option lines index fuel count : Term ctx) :
    GorbowStandardInstances.instantiate (template itag dtag dropTag ptag option lines index fuel) count =
      .equal (remainingCall dtag itag ptag count option lines index fuel) (dropCall dropTag count lines) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substRemaining,
    DropInductionProof.substDrop,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalIteratorRemaining : Targets.InternalIteratorRemaining := by
  intro v l a x n p itag dtag dropTag ptag ctag ht hd hdrop hp hc ctx count option lines index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template itag dtag dropTag ptag option lines index fuel
  obtain ⟨hz⟩ := HistoryMachine.Equations.zero p itag (kernel v l a x) ht (pairCall ptag option lines) index fuel
  obtain ⟨hpair⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag ptag true hd hp option lines
  obtain ⟨hdrop0⟩ := HistoryLookup.DropEquationsProof.dropZero p dropTag hdrop lines
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi=template itag dtag dropTag ptag option lines index fuel from rfl,templateAt]
    exact Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence dtag _ _ hz)
      (Logic.trans _ _ _ hpair (Support.equalitySymmetry _ _ hdrop0))
  let O := liftTerm option
  let L := liftTerm lines
  let I := liftTerm index
  let F := liftTerm fuel
  let z : Term (ctx+1) := .var 0
  let tt := HistoryLookup.DropEquationsProof.tailTag dropTag
  have htt := HistoryLookup.DropEquationsProof.tailInstalled p dropTag hdrop
  have hk := Equations.functionChild p (itag+stepTag iterationBase) (kernel v l a x) iterationArguments
    (Equations.recursionStepChild p itag iterationBase (iterationStep (kernel v l a x)) ht)
  obtain ⟨hsucc⟩ := HistoryMachine.Equations.successor p itag (kernel v l a x) ht z (pairCall ptag O L) I F
  obtain ⟨hnext⟩ := RemainingKernelProof.kernelRemaining p (itag+stepTag iterationBase+1) dtag tt ptag ctag v l a x hk hd htt hp hc
    (iterationCall itag z (pairCall ptag O L) I F) I F
  obtain ⟨hds⟩ := HistoryLookup.DropEquationsProof.dropSuccessor p dropTag hdrop z L
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (remainingCall dtag itag ptag z O L I F) (dropCall dropTag z L)) := .hypothesis List.mem_cons_self
  have hcong := localUnary (call tt (.var 0 ::ᵥ nil)) _ _ ih
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hcong
  have hout := localTrans _ _ _ (.base (HistoryLookup.DestructorProof.unaryCallCongruence dtag _ _ hsucc))
    (localTrans _ _ _ (.base hnext) (localTrans _ _ _ hcong (.base (Support.equalitySymmetry _ _ hds))))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,O,L,I,F,z,GorbowStandardInduction.successorInstance,substituteFormula,
      substRemaining,DropInductionProof.substDrop,substitute,successorLift,Fin.cases_zero,
      remainingCall,dropCall,HistoryLookup.DropEquationsProof.dropCall,Logic.substCall,
      List.Vector.map_cons,List.Vector.map_nil,substIteration,HistoryIteratorSuffix.WitnessProof.substPair] using
        Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  exact ⟨by simpa only [phi,templateAt] using h⟩

theorem internalIteratorDrain : Targets.InternalIteratorDrain := by
  intro v l a x n p itag dtag dropTag ptag ctag ht hd hdrop hp hc ctx option lines index fuel
  obtain ⟨hr⟩ := internalIteratorRemaining v l a x n p itag dtag dropTag ptag ctag ht hd hdrop hp hc ctx lines option lines index fuel
  obtain ⟨he⟩ := DropInductionProof.internalDropExhaustion n p dropTag hdrop ctx lines lines
  exact ⟨Logic.trans _ _ _ hr (.mp he (HistoryCancellation.OrderSupportProof.weakReflexive lines))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.IterationProof
