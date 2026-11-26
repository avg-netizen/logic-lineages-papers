module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence GorbowRegistryTuple FixedFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem tailCall {arity m ctx : Nat} (p : Program arity) (q : Program m) (qtag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨m,q⟩) (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (tailProgram q) (target ::ᵥ inputs) (call qtag inputs) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p _ q qtag hq _ inputs
 intro i
 exact projection p (target ::ᵥ inputs) i.succ

theorem argumentsCall {arity m ctx : Nat} (p : Program arity) (q : Program m) (qtag ntag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨m,q⟩) (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin (m+2)) :
 Computes p (arguments q i) (target ::ᵥ inputs)
  ((LiteralNumeralPrefix.numeralCall ntag (call qtag inputs) ::ᵥ
    (target ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall ntag)).get i) := by
 cases i using Fin.cases with
 | zero =>
  exact LiteralRawMP.ConstructorSupportProof.unary p _ LiteralNumeralPrefix.numeralCode ntag hn (tailProgram q) (call qtag inputs) (tailCall p q qtag hq target inputs)
 | succ i =>
  simp only [arguments,Fin.cases_succ,List.Vector.get_cons_succ,List.Vector.get_map]
  apply CurrentRecursionAccumulator.GraphSupport.composition p (target ::ᵥ inputs) LiteralNumeralPrefix.numeralCode ntag hn (fun _ => .projection i) (((target ::ᵥ inputs).get i) ::ᵥ nil)
  intro j
  cases j using Fin.cases with
  | zero => exact projection p _ i
  | succ j => exact Fin.elim0 j

theorem rawGraph {arity m ctx : Nat} (p : Program arity) (q : Program m) (tag qtag ctag atag ntag : Nat)
 (ht : (nodes p)[tag]? = some ⟨m+1,program q⟩)
 (hq : (nodes p)[qtag]? = some ⟨m,q⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (target ::ᵥ inputs))
   (formulaValue ctag atag (LiteralNumeralPrefix.numeralCall ntag (call qtag inputs) ::ᵥ
    (target ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall ntag)) (template m) (environment m)))) := by
 let raw := LiteralNumeralPrefix.numeralCall ntag (call qtag inputs) ::ᵥ
    (target ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall ntag)
 obtain ⟨he⟩ := Equations.compositionValues p tag (formulaProgram (template m) (environment m)) (arguments q) ht
  (target ::ᵥ inputs) raw (fun i => argumentsCall p q qtag ntag hq hn target inputs i _
   (Equations.argumentChild p tag _ _ ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalFormula (m+2) 0 (m+2) (environment m) (template m)
  arity p (tag+1) ctag atag (Equations.functionChild p tag _ _ ht) hc ha ctx raw
 exact ⟨Logic.trans _ _ _ he hf⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.GraphProof
