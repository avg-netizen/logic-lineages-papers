module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.IdleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryIteratorSuffix.WitnessProof (substPair)

theorem substRun {m n : Nat} (sub : Fin m → Term n) itag ptag (count option lines index fuel : Term m) :
    substitute sub (run itag ptag count option lines index fuel)=
      run itag ptag (substitute sub count) (substitute sub option) (substitute sub lines) (substitute sub index) (substitute sub fuel) := by
  simp only [run,state,iterationCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substPair]
def template {ctx : Nat} (itag ptag : Nat) (option index fuel : Term ctx) : Formula (ctx+1) :=
  .equal (run itag ptag (.var 0) (liftTerm option) .zero (liftTerm index) (liftTerm fuel))
    (state ptag (liftTerm option) .zero)
theorem templateAt {ctx : Nat} itag ptag (option index fuel count : Term ctx) :
    GorbowStandardInstances.instantiate (template itag ptag option index fuel) count=
      .equal (run itag ptag count option .zero index fuel) (state ptag option .zero) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substRun,state,substPair,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem kernelInstalled {n : Nat} (p : Program n) itag (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩) :
    (nodes p)[itag+stepTag iterationBase+1]? = some ⟨3,HistoryKernel.kernel v l a x⟩ := by
  have hs := Equations.recursionStepChild p itag iterationBase (iterationStep (HistoryKernel.kernel v l a x)) hi
  exact Equations.functionChild p _ (HistoryKernel.kernel v l a x) iterationArguments hs

theorem internalIdle : Targets.InternalIdle := by
  intro v l a x n p itag ptag hi hp ctx count option index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let k := HistoryKernel.kernel v l a x
  let kt := itag+stepTag iterationBase+1
  let phi := template itag ptag option index fuel
  have hk := kernelInstalled p itag v l a x hi
  obtain ⟨hz⟩ := SixSol20261113.HistoryMachine.Equations.zero p itag k hi (state ptag option .zero) index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,templateAt] using hz
  let O := liftTerm option
  let I := liftTerm index
  let F := liftTerm fuel
  let j : Term (ctx+1) := .var 0
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (run itag ptag j O .zero I F) (state ptag O .zero)) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := SixSol20261113.HistoryMachine.Equations.successor p itag k hi j (state ptag O .zero) I F
  obtain ⟨hn⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p kt ptag v l a x hk hp O I F
  have hcong := localUnary (call kt (.var 0 ::ᵥ liftTerm I ::ᵥ liftTerm F ::ᵥ nil)) _ _ ih
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hcong
  have hout := localTrans _ _ _ (.base he) (localTrans _ _ _ hcong (.base hn))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,substRun,state,substPair,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi=template itag ptag option index fuel from rfl,templateAt] at h
  exact ⟨h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.IdleProof
