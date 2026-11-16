module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple GorbowSubstitution GorbowFormulaSubstitution

theorem tailEval {m : Nat} (q : Program m) (tag : Nat) (inputs : List.Vector Nat m) :
 evaluate (tailProgram q) (tag ::ᵥ inputs) = evaluate q inputs := by
 change evaluate q _ = _
 congr 1
 ext i
 simp [evaluate]

def terms {m : Nat} (q : Program m) (tag : Nat) (inputs : List.Vector Nat m) : Fin (m+2) → Term 0 :=
 Fin.cases (Term.numeral (evaluate q inputs)) (fun i => Term.numeral ((tag ::ᵥ inputs).get i))

theorem rawArguments {m : Nat} (q : Program m) (tag : Nat) (inputs : List.Vector Nat m) :
 (List.Vector.ofFn fun i => evaluate (arguments q i) (tag ::ᵥ inputs)) =
 FixedFormulaSubstitution.rawInputs (terms q tag inputs) := by
 ext i
 cases i using Fin.cases with
 | zero =>
  change evaluate LiteralNumeralPrefix.numeralCode (evaluate (tailProgram q) (tag ::ᵥ inputs) ::ᵥ nil) = _
  rw [tailEval,LiteralNumeralPrefix.StatementChecks.exactNative]
  rfl
 | succ i =>
  simp only [List.Vector.get_ofFn,arguments,Fin.cases_succ]
  change evaluate LiteralNumeralPrefix.numeralCode ((tag ::ᵥ inputs).get i ::ᵥ nil) = _
  rw [LiteralNumeralPrefix.StatementChecks.exactNative]
  simp only [FixedFormulaSubstitution.rawInputs,List.Vector.get_ofFn,terms,Fin.cases_succ]

theorem substPair {a b : Nat} (s : Fin a → Term b) (x y : Term a) :
 substitute s (pairTerm x y) = pairTerm (substitute s x) (substitute s y) := rfl

theorem substTuple {a b : Nat} (s : Fin a → Term b) (xs : List (Term a)) :
 substitute s (tupleTerm xs) = tupleTerm (xs.map (substitute s)) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [tupleTerm,substitute,substPair,List.map_cons,ih]

theorem assigned {m : Nat} (q : Program m) (tag : Nat) (inputs : List.Vector Nat m) :
 substituteFormula (FixedFormulaSubstitution.assignment (environment m) (terms q tag inputs)) (template m) =
 EffectiveNumeral.calculation tag q inputs := by
 let s := FixedFormulaSubstitution.assignment (environment m) (terms q tag inputs)
 have hs (i : Fin (m+2)) : s i = terms q tag inputs i := by
  simp only [s,FixedFormulaSubstitution.assignment,environment]
  unfold GorbowFormulaSubstitution.renameTerm
  have he : (fun i : Fin 0 => (Term.var (Fin.elim0 i) : Term 0)) = Term.var := funext (fun i => Fin.elim0 i)
  rw [he]
  exact GorbowSubstitution.substitute_variables _
 have hargs : (List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ : Term (m+2)))).map (substitute s) =
  GorbowPRNumeralCalculation.numeralArguments inputs := by
  ext i
  simp only [List.Vector.get_map,List.Vector.get_ofFn,substitute,hs,terms,Fin.cases_succ,
   List.Vector.get_cons_succ,GorbowPRNumeralCalculation.numeralArguments,List.Vector.get_map]
 change substituteFormula s (template m) = _
 simp only [template,substituteFormula,substitute,substPair,substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,hs,terms,Fin.cases_zero,Fin.cases_succ,List.Vector.get_cons_zero,
  ← List.Vector.toList_map,hargs,EffectiveNumeral.calculation,call,headerTerm]
 rfl

theorem exactNative : Targets.NativeFormula := by
 intro m q tag inputs
 change evaluate (FixedFormulaSubstitution.formulaProgram (template m) (environment m)) _ = _
 rw [rawArguments,FixedFormulaSubstitution.StatementChecks.exactNativeFormula,assigned]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.NativeProof
