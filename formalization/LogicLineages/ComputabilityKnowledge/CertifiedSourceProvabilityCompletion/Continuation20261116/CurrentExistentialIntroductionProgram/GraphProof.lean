module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphRule
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.ConstructorSupportProof CurrentRecursionBaseProgram.GraphPrimitives
open GraphInterface GraphRule GraphSyntax
def value {ctx : Nat} (J : Tags) (a w code : Term ctx) : Term ctx :=
 LiteralMPRun.certificate J.mtag .zero (FixedFormulaSubstitution.unaryValue J.ctag 11 a) (ruleValue J a w) code
theorem graph {n ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) 3)
 (J : Tags) (I : Installation p J) :
 Computes p program args (value J (args.get 0) (args.get 1) (args.get 2)) :=
 mpGraph p args J.mtag I.hm _ _ _ _ _ _
  (unaryGraph p args J I 11 _ _ (projection p args 0))
  (ruleGraph p args J I _ _ _ _ (projection p args 0) (projection p args 1))
  (projection p args 2)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphProof
