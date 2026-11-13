module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph

theorem substSuccess {m n : Nat} (sub : Fin m → Term n) tag
 (index fuel context formula cert : Term m) :
 substituteFormula sub (success tag index fuel context formula cert) =
 success tag (substitute sub index) (substitute sub fuel) (substitute sub context) (substitute sub formula) (substitute sub cert) := by
 simp only [success,inputs,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral]
theorem substOrder {m n : Nat} (sub : Fin m → Term n) (a b : Term m) :
 substituteFormula sub (orderGuard a b) = orderGuard (substitute sub a) (substitute sub b) := by
 simp only [orderGuard,substituteFormula,substitute,HistoryOrder.SupportProof.substituteLift,liftSubstitute,Fin.cases_zero]
theorem substBounded {m n : Nat} (sub : Fin m → Term n) tag
 (index fuel context formula cert : Term m) :
 substituteFormula sub (boundedCore tag index fuel context formula cert) =
 boundedCore tag (substitute sub index) (substitute sub fuel) (substitute sub context) (substitute sub formula) (substitute sub cert) := by
 simp only [boundedCore,substituteFormula,substOrder,substSuccess,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]

def body {ctx : Nat} (tag : Nat) (index fuel context formula cert : Term ctx) : Formula (ctx+1) :=
 .conj (orderGuard (.var 0) (liftTerm fuel))
  (success tag (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert))
theorem bodyAt {ctx : Nat} tag (index fuel context formula cert t : Term ctx) :
 GorbowStandardInstances.instantiate (body tag index fuel context formula cert) t =
 .conj (orderGuard t fuel) (success tag index t context formula cert) := by
 simp only [GorbowStandardInstances.instantiate,body,substituteFormula,substOrder,substSuccess,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero]
noncomputable def introduce {T : Sentence → Prop} {ctx : Nat} tag
 (index fuel context formula cert t : Term ctx) :
 Derivation T (.imp (.conj (orderGuard t fuel) (success tag index t context formula cert))
  (boundedCore tag index fuel context formula cert)) := by
 have h := HistoryOrder.SupportProof.existsIntroRule (T := T) (body tag index fuel context formula cert) t
 rw [bodyAt] at h
 exact h

def orderBody {ctx : Nat} (a b : Term ctx) : Formula (ctx+1) :=
 .equal (.add (liftTerm a) (.var 0)) (liftTerm b)
theorem orderBodyAt {ctx : Nat} (a b gap : Term ctx) :
 GorbowStandardInstances.instantiate (orderBody a b) gap = .equal (.add a gap) b := by
 simp only [GorbowStandardInstances.instantiate,orderBody,substituteFormula,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def orderIntro {T : Sentence → Prop} {ctx : Nat} (a b gap : Term ctx) :
 Derivation T (.imp (.equal (.add a gap) b) (orderGuard a b)) := by
 have h := HistoryOrder.SupportProof.existsIntroRule (T := T) (orderBody a b) gap
 rw [orderBodyAt] at h
 exact h
noncomputable def orderRefl {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
 Derivation T (orderGuard a a) := .mp (orderIntro a a .zero) (.arithmetic (.addZero a))

theorem orderNext (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
 Nonempty (Derivation T (.imp (orderGuard a b) (orderGuard a (.succ b)))) := by
 let H := orderBody a b
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (.add (liftTerm a) (.var 0)) (liftTerm b)) :=
  .hypothesis List.mem_cons_self
 have hs := HistoryCodec.ArithmeticSupport.localUnary (.succ (.var 0)) _ _ hh
 have he := HistoryCodec.ArithmeticSupport.localTrans _ _ _
  (.base (.arithmetic (.addSucc (liftTerm a) (.var 0)))) hs
 have hout : Hilbert.Local T (ctx+1) [H] (orderGuard (liftTerm a) (.succ (liftTerm b))) :=
  .mp (.base (orderIntro (liftTerm a) (.succ (liftTerm b)) (.succ (.var 0)))) he
 have hbody : Derivation T (.imp H (GorbowPACore.weaken (orderGuard a (.succ b)))) := by
  simpa only [GorbowPACore.weaken,substOrder,substitute,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T H (orderGuard a (.succ b)) ⟨hbody⟩

theorem boundedNext (T : Sentence → Prop) {ctx : Nat} tag
 (index fuel context formula cert : Term ctx) :
 Nonempty (Derivation T (.imp (boundedCore tag index fuel context formula cert)
  (boundedCore tag index (.succ fuel) context formula cert))) := by
 let H := body tag index fuel context formula cert
 let H' := body tag index (.succ fuel) context formula cert
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 have ho : Hilbert.Local T (ctx+1) [H] (orderGuard (.var 0) (liftTerm fuel)) :=
  .mp (.base (.logical (.andLeft _ _))) hh
 have hc : Hilbert.Local T (ctx+1) [H]
   (success tag (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert)) :=
  .mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨hn⟩ := orderNext T (.var 0 : Term (ctx+1)) (liftTerm fuel)
 have hout : Hilbert.Local T (ctx+1) [H] H' :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.mp (.base hn) ho)) hc
 exact HBQuantifier.existentialMonotonicity T H H' ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

noncomputable def atBound {T : Sentence → Prop} {ctx : Nat} tag
 (index fuel context formula cert : Term ctx) :
 Derivation T (.imp (success tag index fuel context formula cert)
  (boundedCore tag index fuel context formula cert)) := by
 let P := success tag index fuel context formula cert
 have hp : Hilbert.Local T ctx [P] P := .hypothesis List.mem_cons_self
 have hpair := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base (orderRefl fuel))) hp
 exact Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (introduce tag index fuel context formula cert fuel)) hpair))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
