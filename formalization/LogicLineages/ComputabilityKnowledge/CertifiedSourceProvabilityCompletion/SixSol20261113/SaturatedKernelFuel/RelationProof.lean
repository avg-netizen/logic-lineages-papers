module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.Targets

public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.RelationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel

def body {ctx : Nat} (ptag : Nat) (old new h lines : Term ctx) : Formula ctx :=
  .imp (.equal old (pairCall ptag (.succ h) lines))
    (.equal new (pairCall ptag (.succ h) lines))
def inner {ctx : Nat} (ptag : Nat) (old new h : Term ctx) : Formula ctx :=
  .all (body ptag (liftTerm old) (liftTerm new) (liftTerm h) (.var 0))
/-- Backward simulation of successful states. No constraint is imposed when
old is NONE, so this never equates rejected low-fuel runs with high-fuel runs. -/
def relation {ctx : Nat} (ptag : Nat) (old new : Term ctx) : Formula ctx :=
  .all (inner ptag (liftTerm old) (liftTerm new) (.var 0))

theorem substPair {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substitute sub (pairCall tag a b) = pairCall tag (substitute sub a) (substitute sub b) := by
  simp only [pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem substBody {m n : Nat} (sub : Fin m → Term n) ptag (old new h lines : Term m) :
    substituteFormula sub (body ptag old new h lines) =
      body ptag (substitute sub old) (substitute sub new)
        (substitute sub h) (substitute sub lines) := by
  simp only [body,substituteFormula,substPair,substitute]

theorem substInner {m n : Nat} (sub : Fin m → Term n) ptag (old new h : Term m) :
    substituteFormula sub (inner ptag old new h) =
      inner ptag (substitute sub old) (substitute sub new) (substitute sub h) := by
  simp only [inner,substituteFormula,substBody,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]

theorem substRelation {m n : Nat} (sub : Fin m → Term n) ptag (old new : Term m) :
    substituteFormula sub (relation ptag old new) =
      relation ptag (substitute sub old) (substitute sub new) := by
  simp only [relation,substituteFormula,substInner,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]

theorem firstAt {ctx : Nat} ptag (old new h : Term ctx) :
    GorbowStandardInstances.instantiate
      (inner ptag (liftTerm old) (liftTerm new) (.var 0)) h = inner ptag old new h := by
  simp only [GorbowStandardInstances.instantiate,substInner,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem secondAt {ctx : Nat} ptag (old new h lines : Term ctx) :
    GorbowStandardInstances.instantiate
      (body ptag (liftTerm old) (liftTerm new) (liftTerm h) (.var 0)) lines = body ptag old new h lines := by
  simp only [GorbowStandardInstances.instantiate,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} ptag (old new h lines : Term ctx) :
    Derivation T (.imp (relation ptag old new) (body ptag old new h lines)) := by
  have h1 := Derivation.logical (A := T) (.allInstantiate
    (inner ptag (liftTerm old) (liftTerm new) (.var 0)) h)
  rw [GorbowPACore.logicalFormula,firstAt] at h1
  have h2 := Derivation.logical (A := T) (.allInstantiate
    (body ptag (liftTerm old) (liftTerm new) (liftTerm h) (.var 0)) lines)
  rw [GorbowPACore.logicalFormula,secondAt] at h2
  exact Hilbert.compose h2 h1

noncomputable def universalUnder {T : Sentence → Prop} {ctx : Nat} (P : Formula ctx) (Q : Formula (ctx+1))
    (h : Derivation T (.imp (GorbowPACore.weaken P) Q)) : Derivation T (.imp P (.all Q)) :=
  Hilbert.compose (.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize h))
    (.logical (.allVacuous P))

/-- Identity is a success relation for every raw state, with no codec premise. -/
theorem reflexive (T : Sentence → Prop) {ctx : Nat} ptag (state : Term ctx) :
 Nonempty (Derivation T (relation ptag state state)) := by
 let E : Formula (ctx+2) := .equal (liftTerm (liftTerm state))
  (pairCall ptag (.succ (.var 1)) (.var 0))
 have h : Derivation T (.imp E E) := Hilbert.identity E
 exact ⟨.generalize (.generalize h)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.RelationProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.RelationProof
