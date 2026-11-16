module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.EvaluatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
def rhsValue {ctx : Nat} : {n : Nat} → Kind n → List.Vector (Term ctx) n → Term ctx
 | _, .zero, _ => .zero
 | _, .successor, inputs => .succ inputs.head
 | _, .projection i, inputs => inputs.get i

theorem rhsSubstitution {ctx n : Nat} (kind : Kind n) (inputs : List.Vector (Term ctx) n) :
 substitute inputs.get (rhs kind) = rhsValue kind inputs := by
 cases kind with
 | zero => rfl
 | successor => simp only [rhs,substitute,rhsValue,List.Vector.get_zero]
 | projection i => rfl

theorem actual {arity n ctx : Nat} (p : Program arity) (kind : Kind n) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨n,evaluator kind⟩) (inputs : List.Vector (Term ctx) n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call target inputs) (rhsValue kind inputs))) := by
 have hargs : (argumentVariables n).map (substitute inputs.get) = inputs := by
  ext i
  simp only [argumentVariables,List.Vector.get_map,List.Vector.get_ofFn,substitute]
 have h := GorbowPRSymbolicEquations.Proof.nodeEquationInstances arity p target n (evaluator kind) ht n ctx
  (call target (argumentVariables n)) (rhs kind) (SyntaxProof.equation kind target) inputs.get
 rw [Logic.substCall,hargs,rhsSubstitution] at h
 exact h

theorem member {arity n : Nat} (p : Program arity) (kind : Kind n) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨n,evaluator kind⟩) :
 GorbowStandardInduction.universalClosure (rootFormula kind target) ∈ axioms p := by
 apply EffectiveNumeral.NodeSupport.intoRegistry (evaluator kind) arity p target ht
 apply EffectiveNumeral.NodeSupport.rootIncluded
 exact SyntaxProof.equation kind target

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.EvaluatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.EvaluatorProof
