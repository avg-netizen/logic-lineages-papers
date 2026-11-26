module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsWitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelatedConsTargets SubstitutionProof HistoryOrder.SupportProof

theorem substBody {m n : Nat} (s : Fin m → Term n) len q l r c (oh ot nt nh tail : Term m) :
 substituteFormula s (witnessBody len q l r c oh ot nt nh tail) =
 witnessBody len q l r c (substitute s oh) (substitute s ot) (substitute s nt) (substitute s nh) (substitute s tail) := by
 simp only [witnessBody,substituteFormula,substTask,substStack,HistoryLookup.DropEquationsProof.substCons]
def tailBody {ctx : Nat} (len q l r c : Nat) (oh ot nt nh : Term ctx) : Formula (ctx+1) :=
 witnessBody len q l r c (liftTerm oh) (liftTerm ot) (liftTerm nt) (liftTerm nh) (.var 0)
def headBody {ctx : Nat} (len q l r c : Nat) (oh ot nt : Term ctx) : Formula (ctx+1) :=
 .ex (tailBody len q l r c (liftTerm oh) (liftTerm ot) (liftTerm nt) (.var 0))
theorem substTail {m n : Nat} (s : Fin m → Term n) len q l r c (oh ot nt nh : Term m) :
 substituteFormula (liftSubstitute s) (tailBody len q l r c oh ot nt nh) =
 tailBody len q l r c (substitute s oh) (substitute s ot) (substitute s nt) (substitute s nh) := by
 simp only [tailBody,substBody,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substHead {m n : Nat} (s : Fin m → Term n) len q l r c (oh ot nt : Term m) :
 substituteFormula (liftSubstitute s) (headBody len q l r c oh ot nt) =
 headBody len q l r c (substitute s oh) (substitute s ot) (substitute s nt) := by
 simp only [headBody,substituteFormula,substTail,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem tailAt {ctx : Nat} len q l r c (oh ot nt nh tail : Term ctx) :
 GorbowStandardInstances.instantiate (tailBody len q l r c oh ot nt nh) tail =
 witnessBody len q l r c oh ot nt nh tail := by
 simp only [GorbowStandardInstances.instantiate,tailBody,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem headAt {ctx : Nat} len q l r c (oh ot nt nh : Term ctx) :
 GorbowStandardInstances.instantiate (headBody len q l r c oh ot nt) nh =
 .ex (tailBody len q l r c oh ot nt nh) := by
 simp only [GorbowStandardInstances.instantiate,headBody,substituteFormula,substTail,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem witnessesEq {ctx : Nat} len q l r c (oh ot nt : Term ctx) :
 witnesses len q l r c oh ot nt = .ex (headBody len q l r c oh ot nt) := by rfl
noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} len q l r c (oh ot nt nh tail : Term ctx) :
 Derivation T (.imp (witnessBody len q l r c oh ot nt nh tail) (witnesses len q l r c oh ot nt)) := by
 have ht := existsIntroRule (T := T) (tailBody len q l r c oh ot nt nh) tail
 rw [tailAt] at ht
 have hh := existsIntroRule (T := T) (headBody len q l r c oh ot nt) nh
 rw [headAt] at hh
 rw [witnessesEq]
 exact Hilbert.compose hh ht
theorem substWitnesses {m n : Nat} (s : Fin m → Term n) len q l r c (oh ot nt : Term m) :
 substituteFormula s (witnesses len q l r c oh ot nt) =
 witnesses len q l r c (substitute s oh) (substitute s ot) (substitute s nt) := by
 rw [witnessesEq,witnessesEq]
 simp only [substituteFormula,substHead]

def property {ctx : Nat} (len q l r c : Nat) (oh ot nt : Term ctx) : Formula ctx :=
 .imp (stackRelation len q l r (HistoryLookup.consCall c oh ot) nt) (witnesses len q l r c oh ot nt)
theorem substProperty {m n : Nat} (s : Fin m → Term n) len q l r c (oh ot nt : Term m) :
 substituteFormula s (property len q l r c oh ot nt) =
 property len q l r c (substitute s oh) (substitute s ot) (substitute s nt) := by
 simp only [property,substituteFormula,substStack,substWitnesses,HistoryLookup.DropEquationsProof.substCons]
theorem weakenProperty {ctx : Nat} len q l r c (oh ot nt : Term ctx) :
 GorbowPACore.weaken (property len q l r c oh ot nt) =
 property len q l r c (liftTerm oh) (liftTerm ot) (liftTerm nt) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} len q l r c (oh ot a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property len q l r c oh ot a) (property len q l r c oh ot b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property len q l r c (liftTerm oh) (liftTerm ot) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsWitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RelatedConsWitnessProof
