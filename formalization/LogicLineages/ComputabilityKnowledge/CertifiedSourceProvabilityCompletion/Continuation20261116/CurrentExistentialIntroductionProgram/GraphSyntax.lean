module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.ConstructorSupportProof CurrentRecursionBaseProgram.GraphPrimitives GraphInterface GraphOperations
theorem unaryGraph {n inputs ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (token : Nat) (a : Program inputs) (av : Term ctx)
 (ha : Computes p a args av) :
 Computes p (FixedFormulaSubstitution.unary token a) args (FixedFormulaSubstitution.unaryValue J.ctag token av) :=
 binary p args HistoryCodec.cons J.ctag I.hc _ _ _ _ (constantValue p args token) ha

theorem logicalGraph {n inputs ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (isExists : Bool) (a b : Program inputs) (av bv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) :
 Computes p (logicalSingleton isExists a b) args
  (OriginalQuantifierLogicalProducers.lineCall (if isExists then J.dualTag else J.contraTag) av bv) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p args _ (if isExists then J.dualTag else J.contraTag)
  (by cases isExists with | false => exact I.hcontra | true => exact I.hdual) _ (av ::ᵥ bv ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact ha
 | succ i => cases i using Fin.cases with
  | zero => exact hb
  | succ i => exact Fin.elim0 i

theorem instanceGraph {n inputs ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (a witness : Program inputs) (av tv : Term ctx)
 (ha : Computes p a args av) (ht : Computes p witness args tv) :
 Computes p (instantiateCode a witness) args
  (call J.predTag (UniformClosedInstanceRecognizer.instanceCall J.instanceTag av tv ::ᵥ nil)) :=
 unary p args HistoryCodec.predecessor J.predTag I.hpred _ _
  (binary p args UniformClosedInstanceRecognizer.instanceCode J.instanceTag I.hi a witness av tv ha ht)

theorem composeGraph {n inputs ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (a b c hqr hpq : Program inputs) (av bv cv qrv pqv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) (hc : Computes p c args cv)
 (hqr' : Computes p hqr args qrv) (hpq' : Computes p hpq args pqv) :
 Computes p (compose a b c hqr hpq) args (composeValue J av bv cv qrv pqv) :=
 mpUnderGraph p args J I a b c _ hpq av bv cv _ pqv ha hb hc
  (liftGraph p args J I _ a hqr _ av qrv
   (binaryGraph p args J.ctag J.atag I.hc I.ha 7 b c bv cv hb hc) ha hqr') hpq'
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphSyntax
