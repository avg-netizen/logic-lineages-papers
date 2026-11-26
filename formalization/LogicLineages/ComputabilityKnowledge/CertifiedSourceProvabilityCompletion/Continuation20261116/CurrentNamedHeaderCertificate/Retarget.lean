module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.Preflight
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.Retarget
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
def installation {n k : Nat} {p : Program n} {f : Formula 1} {lhs rhs : Term 1} {t : Term k}
 {old ar : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (J : ArithmeticTemplateEvaluation.TemplateInstallation p template) :
 CumulativePropositionalSource.JointInstallation p f lhs rhs template old ar x :=
 { previous :=
   { previous :=
     { previous :=
       { previous :=
         { previous := I.previous.previous.previous.previous.previous
           template := J
           current := I.previous.previous.previous.previous.current }
         current := I.previous.previous.previous.current }
       current := I.previous.previous.current }
     current := I.previous.current }
   currentK := I.currentK
   currentS := I.currentS }
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.Retarget
