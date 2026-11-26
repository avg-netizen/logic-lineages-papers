module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.GuardBound
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

open GorbowSubstitution GorbowFormulaSubstitution HistoryCodec.ArithmeticSupport FuelWitness.ExtractionLogicProof
theorem numeralAdd (T : Sentence → Prop) {ctx : Nat} (a b : Nat) :
 Nonempty (Derivation T (.equal (.add (Term.numeral (n := ctx) a) (Term.numeral b)) (Term.numeral (a+b)))) := by
 induction b with
 | zero => exact ⟨.arithmetic (.addZero _)⟩
 | succ b ih =>
  obtain ⟨ih⟩ := ih
  have hs := Logic.unary (.succ (.var 0)) _ _ ih
  simp only [substitute,Fin.cases_zero] at hs
  exact ⟨Logic.trans _ _ _ (.arithmetic (.addSucc _ _)) hs⟩

theorem lowerAdd (T : Sentence → Prop) {ctx : Nat} (a d : Nat) (fuel : Term ctx) :
 Nonempty (Derivation T (.imp (orderGuard (Term.numeral (a+d)) fuel) (orderGuard (Term.numeral a) fuel))) := by
 let H := orderBody (Term.numeral (n := ctx) (a+d)) fuel
 have hh : Hilbert.Local T (ctx+1) [H]
  (.equal (.add (Term.numeral (a+d)) (.var 0)) (liftTerm fuel)) := by
  simpa only [H,orderBody,liftTerm,renameTerm,Logic.substNumeral] using (Hilbert.Local.hypothesis (T := T) (List.mem_cons_self (a := H) (l := [])))
 obtain ⟨hn⟩ := numeralAdd (ctx := ctx+1) T a d
 have hc := Logic.unary (.add (.var 0) (liftTerm (.var 0 : Term (ctx+1)))) _ _ hn
 simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
 have ha := HistoryBounds.SupportProof.addAssoc (T := T) (Term.numeral (n := ctx+1) a) (Term.numeral d) (.var 0)
 have he := localTrans _ _ _ (.base (NamedArithmeticGraph.Support.equalitySymmetry _ _ ha)) (localTrans _ _ _ (.base hc) hh)
 have hout : Hilbert.Local T (ctx+1) [H] (orderGuard (Term.numeral a) (liftTerm fuel)) :=
  .mp (.base (orderIntro _ _ (.add (Term.numeral d) (.var 0)))) he
 have hbody : Derivation T (.imp H (GorbowPACore.weaken (orderGuard (Term.numeral (n := ctx) a) fuel))) := by
  simpa only [GorbowPACore.weaken,substOrder,Logic.substNumeral,liftTerm,renameTerm] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T H (orderGuard (Term.numeral a) fuel) ⟨hbody⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.GuardBound
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.GuardBound
