module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphInterface
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeTags
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
variable {n k : Nat} {p : Program n} {f : Formula 1} {lhs rhs : Term 1} {t : Term k}
 {old ar : Program 1} {x : Program 3}
def tags (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (contra dual : Nat) : GraphInterface.Tags where
 ctag := I.previous.current.ctag
 atag := I.previous.current.atag
 mtag := I.previous.previous.previous.previous.previous.mpTag
 ktag := I.currentK.constructorTag
 stag := I.currentS.constructorTag
 reflexivityTag := I.previous.previous.previous.previous.previous.reflexivityTag
 allTag := I.previous.previous.current.constructorTag
 contraTag := contra
 dualTag := dual
 instanceTag := I.previous.previous.current.itag
 predTag := I.previous.previous.current.predTag

theorem installed (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (contra dual : Nat)
 (hc : (nodes p)[contra]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor false⟩)
 (hd : (nodes p)[dual]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor true⟩) :
 GraphInterface.Installation p (tags I contra dual) :=
 { hc := I.previous.current.h_ctag
   ha := I.previous.current.h_atag
   hm := I.previous.previous.previous.previous.previous.hmp
   hk := I.currentK.h_constructorTag
   hs := I.currentS.h_constructorTag
   hr := I.previous.previous.previous.previous.previous.hreflexivity
   hall := I.previous.previous.current.h_constructor
   hcontra := hc
   hdual := hd
   hi := I.previous.previous.current.h_itag
   hpred := I.previous.previous.current.h_predTag }
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeTags
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeTags
