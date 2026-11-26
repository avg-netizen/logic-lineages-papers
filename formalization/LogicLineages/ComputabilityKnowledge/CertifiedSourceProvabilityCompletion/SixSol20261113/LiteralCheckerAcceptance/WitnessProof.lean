module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.NormalizationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.WitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryOrder.SupportProof
open LiteralCheckerAuxiliaries HistoryIteratorSuffix.WitnessProof

 def body {ctx : Nat} (ptag ctag : Nat) (state requested formula raw tail : Term ctx) : Formula ctx :=
  .conj (.equal formula (.add raw raw))
    (.equal state (successfulState ptag ctag requested raw tail .zero))
 def inner {ctx : Nat} (ptag ctag : Nat) (state requested formula raw : Term ctx) : Formula (ctx+1) :=
  body ptag ctag (liftTerm state) (liftTerm requested) (liftTerm formula) (liftTerm raw) (.var 0)
 def outer {ctx : Nat} (ptag ctag : Nat) (state requested formula : Term ctx) : Formula (ctx+1) :=
  .ex (inner ptag ctag (liftTerm state) (liftTerm requested) (liftTerm formula) (.var 0))
 def witness {ctx : Nat} (ptag ctag : Nat) (state requested formula : Term ctx) : Formula ctx :=
  .ex (outer ptag ctag state requested formula)

 theorem substState {m n : Nat} (sub : Fin m → Term n) ptag ctag (requested raw tail lines : Term m) :
    substitute sub (successfulState ptag ctag requested raw tail lines) =
      successfulState ptag ctag (substitute sub requested) (substitute sub raw) (substitute sub tail) (substitute sub lines) := by
  simp only [successfulState,substPair,substitute]
 theorem substBody {m n : Nat} (sub : Fin m → Term n) ptag ctag (state requested formula raw tail : Term m) :
    substituteFormula sub (body ptag ctag state requested formula raw tail) =
      body ptag ctag (substitute sub state) (substitute sub requested) (substitute sub formula) (substitute sub raw) (substitute sub tail) := by
  simp only [body,substituteFormula,substState,substitute]
 theorem innerAt {ctx : Nat} ptag ctag (state requested formula raw tail : Term ctx) :
    GorbowStandardInstances.instantiate (inner ptag ctag state requested formula raw) tail =
      body ptag ctag state requested formula raw tail := by
  simp only [GorbowStandardInstances.instantiate,inner,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
 theorem substInner {m n : Nat} (sub : Fin m → Term n) ptag ctag (state requested formula raw : Term m) :
    substituteFormula (liftSubstitute sub) (inner ptag ctag state requested formula raw) =
      inner ptag ctag (substitute sub state) (substitute sub requested) (substitute sub formula) (substitute sub raw) := by
  simp only [inner,substBody,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
 theorem outerAt {ctx : Nat} ptag ctag (state requested formula raw : Term ctx) :
    GorbowStandardInstances.instantiate (outer ptag ctag state requested formula) raw =
      .ex (inner ptag ctag state requested formula raw) := by
  simp only [GorbowStandardInstances.instantiate,outer,substituteFormula,substInner,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
 theorem substWitness {m n : Nat} (sub : Fin m → Term n) ptag ctag (state requested formula : Term m) :
    substituteFormula sub (witness ptag ctag state requested formula) =
      witness ptag ctag (substitute sub state) (substitute sub requested) (substitute sub formula) := by
  simp only [witness,outer,substituteFormula,substInner,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
 theorem weakenWitness {ctx : Nat} ptag ctag (state requested formula : Term ctx) :
    GorbowPACore.weaken (witness ptag ctag state requested formula) =
      witness ptag ctag (liftTerm state) (liftTerm requested) (liftTerm formula) := by
  rw [GorbowPACore.weaken,substWitness]
  rfl
 noncomputable def introWitness {T : Sentence → Prop} {ctx : Nat} ptag ctag (state requested formula raw tail : Term ctx) :
    Derivation T (.imp (body ptag ctag state requested formula raw tail) (witness ptag ctag state requested formula)) := by
  have hi := existsIntroRule (T := T) (inner ptag ctag state requested formula raw) tail
  rw [innerAt] at hi
  have ho := existsIntroRule (T := T) (outer ptag ctag state requested formula) raw
  rw [outerAt] at ho
  exact Hilbert.compose ho hi

 theorem frozenWitness {ctx : Nat} itag ptag ctag (index fuel requested formula certificate : Term ctx) :
    successfulWitness itag ptag ctag index fuel requested formula certificate =
      witness ptag ctag (runCall itag ptag index fuel certificate) requested formula := by
  simp only [successfulWitness,witness,outer,inner,body,runCall,
    SixSol20261112.HistoryMachine.iterationCall,liftTerm,renameTerm,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substPair,substitute]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.WitnessProof
