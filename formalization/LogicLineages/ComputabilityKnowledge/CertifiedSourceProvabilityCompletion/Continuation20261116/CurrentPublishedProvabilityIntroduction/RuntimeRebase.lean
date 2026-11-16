module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeRebase
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CumulativePropositionalSource
/-- Same actual root, CORE and verifier. Uniform13's closed-term validator is
another actual occurrence of the exact same program, never a tag-equality cast. -/
def shared {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old ar x) :
 JointInstallation p f lhs rhs t old ar x :=
 let R := CurrentExistentialIntroductionProgram.RuntimeRebase.shared p f lhs rhs t old ar x I
 { R with previous := { R.previous with previous := { R.previous.previous with
    current := { R.previous.previous.current with vtag := I.previous.current.vtag, h_vtag := I.previous.current.h_vtag } } } }
theorem addresses {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old ar x) :
 (shared p f lhs rhs t old ar x I).currentK.coreTag = I.currentK.coreTag ∧
 (shared p f lhs rhs t old ar x I).currentK.verifierTag = I.currentK.verifierTag := ⟨rfl,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeRebase
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeRebase
