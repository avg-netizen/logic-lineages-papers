module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowSubstitution GorbowFormulaSubstitution InvariantSupport
open RawAdditionIteration (binaryCall)
theorem substBinary {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
 substitute sub (binaryCall tag a b) = binaryCall tag (substitute sub a) (substitute sub b) := by
 simp only [binaryCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
def template {ctx : Nat} (q c a l r num it : Nat) (m index fuel : Term ctx) : Formula (ctx+1) :=
 property q c a l r num (.var 0) (liftTerm m) (liftTerm index) (liftTerm fuel)
  (binaryCall it (.var 0) (liftTerm m))
theorem templateAt {ctx : Nat} q c a l r num it (m index fuel count : Term ctx) :
 GorbowStandardInstances.instantiate (template q c a l r num it m index fuel) count =
 property q c a l r num count m index fuel (binaryCall it count m) := by
 simp only [GorbowStandardInstances.instantiate,template,substProperty,substBinary,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalIteration : Targets.InternalIteration := by
 intro n p old a x I ctx m count index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.numeralTag I.mulIteratorTag m index fuel
 obtain ⟨hb0⟩ := InvariantProof.baseProperty p old a x I m index fuel
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,templateAt] using hb0
 let m' := liftTerm m
 let index' := liftTerm index
 let fuel' := liftTerm fuel
 let j : Term (ctx+1) := .var 0
 let previous := binaryCall I.mulIteratorTag j m'
 have hih : Hilbert.Local T (ctx+1) [phi] phi := .hypothesis List.mem_cons_self
 obtain ⟨hstep⟩ := InvariantProof.stepProperty p old a x I j m' index' fuel' previous
 have hnext := Hilbert.Local.mp (.base hstep) hih
 obtain ⟨hs⟩ := EquationsProof.iteratorSuccessor p old a x I j m'
 have hout := Hilbert.Local.mp (.mp (.base (InvariantSupport.transport I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.numeralTag
  (.succ j) m' index' fuel' (binaryCall I.mulStepTag m' previous) (binaryCall I.mulIteratorTag (.succ j) m')))
  (.base (Support.equalitySymmetry _ _ hs))) hnext
 have hsucc : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substProperty,substBinary,
   substitute,successorLift,Fin.cases_zero,m',index',fuel',j,previous] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hsucc)
 exact ⟨by simpa only [phi,templateAt,InvariantSupport.property,InvariantSupport.contents,T] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.IterationProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.IterationProof.internalIteration
