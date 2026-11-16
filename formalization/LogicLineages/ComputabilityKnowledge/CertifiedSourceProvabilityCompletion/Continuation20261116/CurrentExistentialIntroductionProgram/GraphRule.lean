module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphDNE
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphRule
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.ConstructorSupportProof CurrentRecursionBaseProgram.GraphPrimitives
open GraphInterface GraphOperations GraphSyntax GraphValues GraphDNE
abbrev instanceValue {ctx : Nat} (J : Tags) (a w : Term ctx) :=
 call J.predTag (UniformClosedInstanceRecognizer.instanceCall J.instanceTag a w ::ᵥ nil)
def ruleValue {ctx : Nat} (J : Tags) (a w : Term ctx) : Term ctx :=
 let P := FixedFormulaSubstitution.unaryValue J.ctag 10 (nv J a)
 let V := instanceValue J a w
 let inst := UniformClosedRule13Certificate.certificate J.ctag J.allTag (nv J a) w
 let bridge := composeValue J (nv J (nv J P)) P (nv J V) inst (dneValue J P)
 let negated := LiteralMPRun.certificate J.mtag .zero (iv J V (nv J P)) (cc J (nv J P) V) bridge
 let dual := OriginalQuantifierLogicalProducers.lineCall J.dualTag a .zero
 composeValue J V (nv J P) (FixedFormulaSubstitution.unaryValue J.ctag 11 a) dual negated

theorem ruleGraph {n inputs ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (a w : Program inputs) (av wv : Term ctx)
 (ha : Computes p a args av) (hw : Computes p w args wv) :
 Computes p (rule a w) args (ruleValue J av wv) := by
 have hi := instanceGraph p args J I a w av wv ha hw
 have hn := unaryGraph p args J I 6 a av ha
 have hp := unaryGraph p args J I 10 _ _ hn
 have hnp := unaryGraph p args J I 6 _ _ hp
 have hnnp := unaryGraph p args J I 6 _ _ hnp
 have hni := unaryGraph p args J I 6 _ _ hi
 have hall := allGraph p args J.ctag J.allTag I.hc I.hall _ _ _ _ hn hw
 have hdne := dneGraph p args J I _ _ hp
 have hbridge := composeGraph p args J I _ _ _ _ _ _ _ _ _ _ hnnp hp hni hall hdne
 have hc := logicalGraph p args J I false _ _ _ _ hnp hi
 have himp := binaryGraph p args J.ctag J.atag I.hc I.ha 7 _ _ _ _ hi hnp
 have hnegative := mpGraph p args J.mtag I.hm _ _ _ _ _ _ himp hc hbridge
 have hdual := logicalGraph p args J I true a _ av .zero ha (constantValue p args 0)
 have hex := unaryGraph p args J I 11 a av ha
 exact composeGraph p args J I _ _ _ _ _ _ _ _ _ _ hi hnp hex hdual hnegative
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphRule
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphRule
