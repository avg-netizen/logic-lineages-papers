module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.EvaluatorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RhsEncoding
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open FixedFormulaSubstitution PrescribedRuntimeCallCongruence
theorem rhsCode {arity ctx n : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p J) (kind : Kind n) (inputs : List.Vector (Term ctx) n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment n)
   (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)) (rhs kind))
   (LiteralNumeralPrefix.numeralCall J.numeralTag (EvaluatorProof.rhsValue kind inputs)))) := by
 cases kind with
 | zero =>
  obtain ⟨h⟩ := ValueTraceProof.numeral (ctx := ctx) p J H.hn 0
  exact ⟨Support.equalitySymmetry _ _ h⟩
 | successor =>
  obtain ⟨h⟩ := LiteralNumeralPrefix.EquationsProof.successor p J.numeralTag J.ctag H.hn H.hc inputs.head
  have hs := Support.equalitySymmetry _ _ h
  simp only [rhs,EvaluatorProof.rhsValue,termValue,PrescribedRuntimeSpecialization.runtimeEnvironment,
   List.Vector.get_map,List.Vector.get_zero,List.Vector.head_map,FixedFormulaSubstitution.unaryValue] at hs ⊢
  exact ⟨hs⟩
 | projection i =>
  simp only [rhs,EvaluatorProof.rhsValue,termValue,PrescribedRuntimeSpecialization.runtimeEnvironment,List.Vector.get_map]
  exact ⟨.logical (.reflexive _)⟩

theorem actual {arity ctx n : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p J) (kind : Kind n) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨n,evaluator kind⟩) (inputs : List.Vector (Term ctx) n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment n)
   (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)) (rhs kind))
   (LiteralNumeralPrefix.numeralCall J.numeralTag (call target inputs)))) := by
 obtain ⟨hs⟩ := rhsCode p J H kind inputs
 obtain ⟨he⟩ := EvaluatorProof.actual p kind target ht inputs
 have hc := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) J.numeralTag
  (call target inputs ::ᵥ nil) (EvaluatorProof.rhsValue kind inputs ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact he
   | succ i => exact Fin.elim0 i)
 exact ⟨Logic.trans _ _ _ hs (Support.equalitySymmetry _ _ hc)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RhsEncoding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RhsEncoding
