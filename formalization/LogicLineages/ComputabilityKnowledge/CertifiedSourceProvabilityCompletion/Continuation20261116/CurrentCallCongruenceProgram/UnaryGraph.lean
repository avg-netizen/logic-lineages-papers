module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TransitivityGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.UnaryGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem ordinary {arity inputs n rawCount ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (e : FixedFormulaSubstitution.Environment n 1 rawCount)
 (f : Term n) (raw : List.Vector (Program inputs) rawCount) (rv : List.Vector (Term ctx) rawCount)
 (t u code : Program inputs) (tv uv cv : Term ctx)
 (hr : ∀ i, Computes p (raw.get i) args (rv.get i))
 (ht : Computes p t args tv) (hu : Computes p u args uv) (hc : Computes p code args cv) :
 Computes p (CurrentCallCongruenceProgram.unary e f raw t u code) args
  (PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag e f rv tv uv cv) := by
 have hraw (q : Program inputs) (qv : Term ctx) (hq : Computes p q args qv) :
  ∀ i, Computes p ((q ::ᵥ raw).get i) args ((qv ::ᵥ rv).get i) := by
  intro i
  cases i using Fin.cases with
  | zero => exact hq
  | succ i => exact hr i
 have hft := GraphSupport.term p args f (UniformRuntimeEnvironmentAgreement.specialize e) (t ::ᵥ raw) (tv ::ᵥ rv) J I (hraw t tv ht)
 have hfu := GraphSupport.term p args f (UniformRuntimeEnvironmentAgreement.specialize e) (u ::ᵥ raw) (uv ::ᵥ rv) J I (hraw u uv hu)
 have hopen := GraphSupport.term p args f e raw rv J I hr
 have heq := GraphSupport.binaryCode p args J I 0 _ _ _ _ hft hfu
 have href := GraphSupport.binaryCode p args J I 0 _ _ _ _ hft hft
 have hmatrix := GraphSupport.binaryCode p args J I 0 _ _ _ _ hft hopen
 exact mpGraph p args J.mtag I.hm _ _ _ _ _ _ heq
  (mpGraph p args J.mtag I.hm _ _ _ _ _ _
   (GraphSupport.binaryCode p args J I 7 _ _ _ _ href heq)
   (replacementGraph p args J.ctag J.constructorTag I.hc I.h12 _ _ _ _ _ _ hmatrix ht hu) hc)
  (GraphSupport.reflexivity p args J I _ _ hft)

theorem closed {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (f : Term 1) (t u code : Program inputs) (tv uv cv : Term ctx)
 (ht : Computes p t args tv) (hu : Computes p u args uv) (hc : Computes p code args cv) :
 Computes p (unaryClosed f t u code) args (PrescribedRuntimeCallCongruence.unaryCertificate J f tv uv cv) :=
 ordinary p args J I boundEnvironment f nil nil t u code tv uv cv (fun i => Fin.elim0 i) ht hu hc

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.UnaryGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.UnaryGraph
