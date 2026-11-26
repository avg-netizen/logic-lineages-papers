module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.Preflight
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphInterface
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
structure Tags where
 ctag : Nat
 atag : Nat
 mtag : Nat
 ktag : Nat
 stag : Nat
 reflexivityTag : Nat
 allTag : Nat
 contraTag : Nat
 dualTag : Nat
 instanceTag : Nat
 predTag : Nat
structure Installation {n : Nat} (p : Program n) (J : Tags) : Prop where
 hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩
 hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩
 hk : (nodes p)[J.ktag]? = some ⟨3,UniformClosedPropositional.lineConstructor false⟩
 hs : (nodes p)[J.stag]? = some ⟨3,UniformClosedPropositional.lineConstructor true⟩
 hr : (nodes p)[J.reflexivityTag]? = some ⟨1,Continuation20261114.RawReflexivity.lineConstructor⟩
 hall : (nodes p)[J.allTag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩
 hcontra : (nodes p)[J.contraTag]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor false⟩
 hdual : (nodes p)[J.dualTag]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor true⟩
 hi : (nodes p)[J.instanceTag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩
 hpred : (nodes p)[J.predTag]? = some ⟨1,HistoryCodec.predecessor⟩
def liftValue {ctx : Nat} (J : Tags) (A B code : Term ctx) : Term ctx :=
 LiteralMPRun.certificate J.mtag .zero (PrescribedRuntimeEquality.impValue J.ctag J.atag B A)
  (UniformClosedPropositionalCertificate.certificate J.ctag J.ktag A B A) code
def mpUnderValue {ctx : Nat} (J : Tags) (P Q R hi ha : Term ctx) : Term ctx :=
 let imp := PrescribedRuntimeEquality.impValue J.ctag J.atag
 LiteralMPRun.certificate J.mtag .zero (imp P R)
  (LiteralMPRun.certificate J.mtag .zero (imp (imp P Q) (imp P R))
   (UniformClosedPropositionalCertificate.certificate J.ctag J.stag P Q R) hi) ha
def composeValue {ctx : Nat} (J : Tags) (P Q R hqr hpq : Term ctx) : Term ctx :=
 mpUnderValue J P Q R (liftValue J (PrescribedRuntimeEquality.impValue J.ctag J.atag Q R) P hqr) hpq
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphInterface
