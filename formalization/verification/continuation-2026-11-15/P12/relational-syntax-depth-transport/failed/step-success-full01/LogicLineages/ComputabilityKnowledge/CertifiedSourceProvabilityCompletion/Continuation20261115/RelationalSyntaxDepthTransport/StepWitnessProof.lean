module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepWitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open StepSuccessTargets HistoryOrder.SupportProof

theorem substBody {m n : Nat} (s : Fin m → Term n) e c a (tasks tok result head tail added : Term m) :
 substituteFormula s (witnessBody e c a tasks tok result head tail added) =
 witnessBody e c a (substitute s tasks) (substitute s tok) (substitute s result)
  (substitute s head) (substitute s tail) (substitute s added) := by
 simp only [witnessBody,substituteFormula,LiteralSyntaxStep.expandCall,HistoryLookup.consCall,
  HistoryAppend.appendCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
def addedBody {ctx : Nat} (e c a : Nat) (tasks tok result head tail : Term ctx) : Formula (ctx+1) :=
 witnessBody e c a (liftTerm tasks) (liftTerm tok) (liftTerm result) (liftTerm head) (liftTerm tail) (.var 0)
def tailBody {ctx : Nat} (e c a : Nat) (tasks tok result head : Term ctx) : Formula (ctx+1) :=
 .ex (addedBody e c a (liftTerm tasks) (liftTerm tok) (liftTerm result) (liftTerm head) (.var 0))
def headBody {ctx : Nat} (e c a : Nat) (tasks tok result : Term ctx) : Formula (ctx+1) :=
 .ex (tailBody e c a (liftTerm tasks) (liftTerm tok) (liftTerm result) (.var 0))

theorem substAdded {m n : Nat} (s : Fin m → Term n) e c a (tasks tok result head tail : Term m) :
 substituteFormula (liftSubstitute s) (addedBody e c a tasks tok result head tail) =
 addedBody e c a (substitute s tasks) (substitute s tok) (substitute s result)
  (substitute s head) (substitute s tail) := by
 simp only [addedBody,substBody,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substTail {m n : Nat} (s : Fin m → Term n) e c a (tasks tok result head : Term m) :
 substituteFormula (liftSubstitute s) (tailBody e c a tasks tok result head) =
 tailBody e c a (substitute s tasks) (substitute s tok) (substitute s result) (substitute s head) := by
 simp only [tailBody,substituteFormula,substAdded,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substHead {m n : Nat} (s : Fin m → Term n) e c a (tasks tok result : Term m) :
 substituteFormula (liftSubstitute s) (headBody e c a tasks tok result) =
 headBody e c a (substitute s tasks) (substitute s tok) (substitute s result) := by
 simp only [headBody,substituteFormula,substTail,substituteLift,substitute,liftSubstitute,Fin.cases_zero]

theorem addedAt {ctx : Nat} e c a (tasks tok result head tail added : Term ctx) :
 GorbowStandardInstances.instantiate (addedBody e c a tasks tok result head tail) added =
 witnessBody e c a tasks tok result head tail added := by
 simp only [GorbowStandardInstances.instantiate,addedBody,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem tailAt {ctx : Nat} e c a (tasks tok result head tail : Term ctx) :
 GorbowStandardInstances.instantiate (tailBody e c a tasks tok result head) tail =
 .ex (addedBody e c a tasks tok result head tail) := by
 simp only [GorbowStandardInstances.instantiate,tailBody,substituteFormula,substAdded,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem headAt {ctx : Nat} e c a (tasks tok result head : Term ctx) :
 GorbowStandardInstances.instantiate (headBody e c a tasks tok result) head =
 .ex (tailBody e c a tasks tok result head) := by
 simp only [GorbowStandardInstances.instantiate,headBody,substituteFormula,substTail,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
/-- Match the exact frozen triple binder and original de Bruijn indices. -/
theorem witnessesEq {ctx : Nat} e c a (tasks tok result : Term ctx) :
 witnesses e c a tasks tok result = .ex (headBody e c a tasks tok result) := by
 rfl
noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} e c a
 (tasks tok result head tail added : Term ctx) :
 Derivation T (.imp (witnessBody e c a tasks tok result head tail added) (witnesses e c a tasks tok result)) := by
 have ha := existsIntroRule (T := T) (addedBody e c a tasks tok result head tail) added
 rw [addedAt] at ha
 have ht := existsIntroRule (T := T) (tailBody e c a tasks tok result head) tail
 rw [tailAt] at ht
 have hh := existsIntroRule (T := T) (headBody e c a tasks tok result) head
 rw [headAt] at hh
 rw [witnessesEq]
 exact Hilbert.compose hh (Hilbert.compose ht ha)
theorem substWitnesses {m n : Nat} (s : Fin m → Term n) e c a (tasks tok result : Term m) :
 substituteFormula s (witnesses e c a tasks tok result) =
 witnesses e c a (substitute s tasks) (substitute s tok) (substitute s result) := by
 rw [witnessesEq,witnessesEq]
 simp only [substituteFormula,substHead]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepWitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepWitnessProof
