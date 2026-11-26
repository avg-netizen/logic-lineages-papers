module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepSuffixProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.RelationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel

def body {ctx : Nat} (atag ptag : Nat) (old new tail h lines : Term ctx) : Formula ctx :=
  .imp (.equal old (pairCall ptag (.succ h) lines))
    (.equal new (pairCall ptag (.succ (pairCall atag h tail)) lines))
def inner {ctx : Nat} (atag ptag : Nat) (old new tail h : Term ctx) : Formula ctx :=
  .all (body atag ptag (liftTerm old) (liftTerm new) (liftTerm tail) (liftTerm h) (.var 0))
/-- Backward simulation of successful states. No constraint is imposed when
old is NONE, so this does not falsely preserve invalid references under append. -/
def relation {ctx : Nat} (atag ptag : Nat) (old new tail : Term ctx) : Formula ctx :=
  .all (inner atag ptag (liftTerm old) (liftTerm new) (liftTerm tail) (.var 0))

theorem substPair {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substitute sub (pairCall tag a b) = pairCall tag (substitute sub a) (substitute sub b) := by
  simp only [pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem substBody {m n : Nat} (sub : Fin m → Term n) atag ptag (old new tail h lines : Term m) :
    substituteFormula sub (body atag ptag old new tail h lines) =
      body atag ptag (substitute sub old) (substitute sub new) (substitute sub tail)
        (substitute sub h) (substitute sub lines) := by
  simp only [body,substituteFormula,substPair,substitute]

theorem substInner {m n : Nat} (sub : Fin m → Term n) atag ptag (old new tail h : Term m) :
    substituteFormula sub (inner atag ptag old new tail h) =
      inner atag ptag (substitute sub old) (substitute sub new) (substitute sub tail) (substitute sub h) := by
  simp only [inner,substituteFormula,substBody,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]

theorem substRelation {m n : Nat} (sub : Fin m → Term n) atag ptag (old new tail : Term m) :
    substituteFormula sub (relation atag ptag old new tail) =
      relation atag ptag (substitute sub old) (substitute sub new) (substitute sub tail) := by
  simp only [relation,substituteFormula,substInner,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]

theorem firstAt {ctx : Nat} atag ptag (old new tail h : Term ctx) :
    GorbowStandardInstances.instantiate
      (inner atag ptag (liftTerm old) (liftTerm new) (liftTerm tail) (.var 0)) h = inner atag ptag old new tail h := by
  simp only [GorbowStandardInstances.instantiate,substInner,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem secondAt {ctx : Nat} atag ptag (old new tail h lines : Term ctx) :
    GorbowStandardInstances.instantiate
      (body atag ptag (liftTerm old) (liftTerm new) (liftTerm tail) (liftTerm h) (.var 0)) lines = body atag ptag old new tail h lines := by
  simp only [GorbowStandardInstances.instantiate,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} atag ptag (old new tail h lines : Term ctx) :
    Derivation T (.imp (relation atag ptag old new tail) (body atag ptag old new tail h lines)) := by
  have h1 := Derivation.logical (A := T) (.allInstantiate
    (inner atag ptag (liftTerm old) (liftTerm new) (liftTerm tail) (.var 0)) h)
  rw [GorbowPACore.logicalFormula,firstAt] at h1
  have h2 := Derivation.logical (A := T) (.allInstantiate
    (body atag ptag (liftTerm old) (liftTerm new) (liftTerm tail) (liftTerm h) (.var 0)) lines)
  rw [GorbowPACore.logicalFormula,secondAt] at h2
  exact Hilbert.compose h2 h1

noncomputable def universalUnder {T : Sentence → Prop} {ctx : Nat} (P : Formula ctx) (Q : Formula (ctx+1))
    (h : Derivation T (.imp (GorbowPACore.weaken P) Q)) : Derivation T (.imp P (.all Q)) :=
  Hilbert.compose (.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize h))
    (.logical (.allVacuous P))

/-- Initial successful states are related at precisely the same pair/append addresses. -/
theorem initialRelation {n ctx : Nat} (p : Program n) atag ptag
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (h tail lines : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (relation atag ptag (pairCall ptag (.succ h) lines) (pairCall ptag (.succ (pairCall atag h tail)) lines) tail)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := liftTerm (liftTerm h)
  let L := liftTerm (liftTerm lines)
  let Z := liftTerm (liftTerm tail)
  let A : Term (ctx+2) := .var (Fin.succ (0 : Fin (ctx+1)))
  let B : Term (ctx+2) := .var 0
  let E := Formula.equal (pairCall ptag (.succ H) L) (pairCall ptag (.succ A) B)
  obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp (ctx+2) (.succ H) L (.succ A) B
  have he : Hilbert.Local T (ctx+2) [E] E := .hypothesis List.mem_cons_self
  have both := Hilbert.Local.mp (.base hi) he
  have eh : Hilbert.Local T (ctx+2) [E] (.equal H A) :=
    .mp (.base (.arithmetic (.succInjective H A))) (.mp (.base (.logical (.andLeft _ _))) both)
  have el : Hilbert.Local T (ctx+2) [E] (.equal L B) := .mp (.base (.logical (.andRight _ _))) both
  have ea := StepSuffixProof.pairCongruence atag H Z A Z eh (.base (.logical (.reflexive Z)))
  have es := localUnary (.succ (.var 0)) _ _ ea
  have eo := StepSuffixProof.pairCongruence ptag _ L _ B es el
  have result := Derivation.generalize (Derivation.generalize (Hilbert.Local.finish (Hilbert.Local.discharge eo)))
  exact ⟨by simpa only [relation,inner,body,H,L,Z,A,B,E,liftTerm,renameTerm,substitute,substPair,Fin.cases_zero] using result⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.RelationProof
