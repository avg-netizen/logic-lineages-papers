module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open GorbowSubstitution GorbowFormulaSubstitution InvariantSupport

theorem substBinary {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
 substitute sub (binaryCall tag a b) = binaryCall tag (substitute sub a) (substitute sub b) := by
 simp only [binaryCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
def template {ctx : Nat} (v q c a l r num pref it : Nat) (t index fuel : Term ctx) : Formula (ctx+1) :=
 .imp (RawReflexivityDispatcher.valid v (liftTerm t))
  (property v q c a l r num pref (.var 0) (liftTerm t) (liftTerm index) (liftTerm fuel)
   (binaryCall it (.var 0) (liftTerm t)))
theorem templateAt {ctx : Nat} v q c a l r num pref it (t index fuel count : Term ctx) :
 GorbowStandardInstances.instantiate (template v q c a l r num pref it t index fuel) count =
 .imp (RawReflexivityDispatcher.valid v t)
  (property v q c a l r num pref count t index fuel (binaryCall it count t)) := by
 simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substProperty,substBinary,
  RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalIteration : Targets.InternalIteration := by
 intro n p old a x I ctx count t index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag I.numeralTag I.prefixTag I.iteratorTag t index fuel
 obtain ⟨hb0⟩ := InvariantProof.baseProperty p old a x I t index fuel
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,templateAt] using hb0
 let t' := liftTerm t
 let index' := liftTerm index
 let fuel' := liftTerm fuel
 let j : Term (ctx+1) := .var 0
 let H := RawReflexivityDispatcher.valid I.vtag t'
 let previous := binaryCall I.iteratorTag j t'
 have ht : Hilbert.Local T (ctx+1) [H,phi] H := .hypothesis List.mem_cons_self
 have hih : Hilbert.Local T (ctx+1) [H,phi] phi := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hprev := Hilbert.Local.mp hih ht
 obtain ⟨hstep⟩ := InvariantProof.stepProperty p old a x I j t' index' fuel' previous
 have hnext := Hilbert.Local.mp (Hilbert.Local.mp (.base hstep) ht) hprev
 obtain ⟨hs⟩ := EquationsProof.iteratorSuccessor p old a x I j t'
 have hout := Hilbert.Local.mp (.mp (.base (transport I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag I.numeralTag I.prefixTag
  (.succ j) t' index' fuel' (binaryCall I.stepTag t' previous) (binaryCall I.iteratorTag (.succ j) t')))
  (.base (Support.equalitySymmetry _ _ hs))) hnext
 have hsucc : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,substProperty,substBinary,
   RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   substitute,successorLift,Fin.cases_zero,t',index',fuel',j,H,previous] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
 have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hsucc)
 exact ⟨by simpa only [phi,templateAt] using h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.IterationProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.IterationProof.internalIteration
