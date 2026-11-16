module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphSyntax
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphValues
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphDNE
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.ConstructorSupportProof CurrentRecursionBaseProgram.GraphPrimitives
open GraphInterface GraphOperations GraphSyntax GraphValues
theorem dneGraph {n inputs ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (a : Program inputs) (av : Term ctx)
 (ha : Computes p a args av) :
 Computes p (doubleNegation a) args (dneValue J av) := by
 dsimp only [doubleNegation,dneValue]
 apply mpUnderGraph p args J I
 · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
 · exact constantValue p args _
 · exact ha
 · apply composeGraph p args J I
   · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
   · apply binaryGraph p args J.ctag J.atag I.hc I.ha 7
     · exact unaryGraph p args J I 6 _ _ ha
     · exact unaryGraph p args J I 6 _ _ (constantValue p args _)
   · exact binaryGraph p args J.ctag J.atag I.hc I.ha 7 _ _ _ _ (constantValue p args _) ha
   · exact logicalGraph p args J I false _ _ _ _ ha (constantValue p args _)
   · apply composeGraph p args J I
     · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
     · apply binaryGraph p args J.ctag J.atag I.hc I.ha 7
       · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ (constantValue p args _))
       · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
     · apply binaryGraph p args J.ctag J.atag I.hc I.ha 7
       · exact unaryGraph p args J I 6 _ _ ha
       · exact unaryGraph p args J I 6 _ _ (constantValue p args _)
     · exact logicalGraph p args J I false _ _ _ _
        (unaryGraph p args J I 6 _ _ (constantValue p args _)) (unaryGraph p args J I 6 _ _ ha)
     · apply propositionalGraph p args J.ctag J.ktag false I.hc I.hk
       · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
       · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ (constantValue p args _))
       · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
 · apply liftGraph p args J I
   · exact constantValue p args _
   · exact unaryGraph p args J I 6 _ _ (unaryGraph p args J I 6 _ _ ha)
   · exact reflexivityGraph p args J I _ _ (constantValue p args _)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphDNE
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphDNE
