module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality FixedFormulaSubstitution
theorem member {arity m : Nat} (p : Program arity) (f : Program m)
 (g : Program (m+2)) (tag : Nat)
 (h : (nodes p)[tag]? = some ⟨m+1,Program.recursion f g⟩) :
 GorbowStandardInduction.universalClosure (rootFormula m tag) ∈ axioms p := by
 apply EffectiveNumeral.NodeSupport.intoRegistry (.recursion f g) arity p tag h
 apply EffectiveNumeral.NodeSupport.rootIncluded
 exact List.mem_cons_self
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootProof
