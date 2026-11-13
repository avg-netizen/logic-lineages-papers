module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendBounded
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport AppendSupport AppendBounded

theorem zeroAll {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allBounded tag .zero middle right)) := by
 obtain ⟨h⟩ := zeroAt p tag ht (.var (0 : Fin (ctx+1))) (liftTerm middle) (liftTerm right)
 exact ⟨.generalize h⟩
theorem nextAll {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (bound middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (allBounded tag bound middle right) (allBounded tag (.succ bound) middle right))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := allBounded tag bound middle right
 let Q := bounded tag (.succ (liftTerm bound)) (.var (0 : Fin (ctx+1))) (liftTerm middle) (liftTerm right)
 obtain ⟨hs⟩ := nextAt p tag ht (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm middle) (liftTerm right)
 have hs' : Derivation T (.imp (GorbowPACore.weaken P) Q) := by
  simpa only [P,Q,GorbowPACore.weaken,substAll,liftTerm,renameTerm] using hs
 have hd := Derivation.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize hs')
 exact ⟨Hilbert.compose hd (.logical (.allVacuous P))⟩
def template {ctx : Nat} (tag : Nat) (middle right : Term ctx) : Formula (ctx+1) :=
 allBounded tag (.var 0) (liftTerm middle) (liftTerm right)
theorem templateAt {ctx : Nat} tag (middle right bound : Term ctx) :
 GorbowStandardInstances.instantiate (template tag middle right) bound = allBounded tag bound middle right := by
 simp only [GorbowStandardInstances.instantiate,template,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalAppendAssociativity : Targets.InternalAppendAssociativity := by
 intro n p tag ctag ltag rtag ht hc hl hr ctx left middle right
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template tag middle right
 obtain ⟨hz⟩ := zeroAll p tag ht middle right
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  rw [show phi=template tag middle right from rfl,templateAt]
  exact hz
 obtain ⟨hs0⟩ := nextAll p tag ht (.var (0 : Fin (ctx+1))) (liftTerm middle) (liftTerm right)
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substAll,substitute,successorLift,Fin.cases_zero] using hs0
 have hall := atTerm phi left (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 rw [show phi=template tag middle right from rfl,templateAt] at hall
 exact ⟨.mp (.mp (allElim tag left left middle right) hall) (HistoryCancellation.OrderSupportProof.weakReflexive left)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendProof
