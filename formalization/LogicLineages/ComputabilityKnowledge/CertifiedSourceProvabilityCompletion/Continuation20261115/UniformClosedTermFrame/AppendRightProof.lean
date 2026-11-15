module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightBounded
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport AppendRightSupport AppendRightBounded

theorem zeroAll {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allBounded (ctx := ctx) tag .zero)) := by
 obtain ⟨h⟩ := zeroAt p tag ht (.var (0 : Fin (ctx+1)))
 exact ⟨.generalize h⟩
theorem nextAll {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (bound : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (allBounded tag bound) (allBounded tag (.succ bound)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := allBounded tag bound
 let Q := bounded tag (.succ (liftTerm bound)) (.var (0 : Fin (ctx+1)))
 obtain ⟨hs⟩ := nextAt p tag ht (liftTerm bound) (.var (0 : Fin (ctx+1)))
 have hs' : Derivation T (.imp (GorbowPACore.weaken P) Q) := by
  simpa only [P,Q,GorbowPACore.weaken,substAll,liftTerm,renameTerm] using hs
 have hd := Derivation.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize hs')
 exact ⟨Hilbert.compose hd (.logical (.allVacuous P))⟩
def template {ctx : Nat} (tag : Nat) : Formula (ctx+1) :=
 allBounded tag (.var 0)
theorem templateAt {ctx : Nat} tag (bound : Term ctx) :
 GorbowStandardInstances.instantiate (template tag) bound = allBounded tag bound := by
 simp only [GorbowStandardInstances.instantiate,template,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem rightNil {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (left : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall tag left .zero) left)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := template tag
 obtain ⟨hz⟩ := zeroAll (ctx := ctx) p tag ht
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  rw [show phi=template tag from rfl,templateAt]
  exact hz
 obtain ⟨hs0⟩ := nextAll p tag ht (.var (0 : Fin (ctx+1)))
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substAll,substitute,successorLift,Fin.cases_zero] using hs0
 have hall := atTerm phi left (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 rw [show phi=template tag from rfl,templateAt] at hall
 exact ⟨.mp (.mp (allElim tag left left) hall) (HistoryCancellation.OrderSupportProof.weakReflexive left)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightProof
