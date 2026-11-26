module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CumulativePropositionalSource
/-- Same root/current checker addresses. Every changed primitive occurrence
carries actual membership; no address equality or source cast is assumed. -/
def shared {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old ar x) :
 JointInstallation p f lhs rhs t old ar x :=
 { I with
  currentK := { I.currentK with
   ctag := I.previous.current.ctag, h_ctag := I.previous.current.h_ctag,
   atag := I.previous.current.atag, h_atag := I.previous.current.h_atag,
   ptag := I.previous.current.ptag, h_ptag := I.previous.current.h_ptag }
  currentS := { I.currentS with
   ctag := I.previous.current.ctag, h_ctag := I.previous.current.h_ctag,
   atag := I.previous.current.atag, h_atag := I.previous.current.h_atag,
   ptag := I.previous.current.ptag, h_ptag := I.previous.current.h_ptag,
   fval := I.currentK.fval, h_fval := I.currentK.h_fval }
  previous := { I.previous with previous := { I.previous.previous with
   current := { I.previous.previous.current with
    ctag := I.previous.current.ctag, h_ctag := I.previous.current.h_ctag,
    atag := I.previous.current.atag, h_atag := I.previous.current.h_atag,
    ptag := I.previous.current.ptag, h_ptag := I.previous.current.h_ptag,
    fval := I.currentK.fval, h_fval := I.currentK.h_fval } } } }
/-- Auditable address preservation, not a new semantic contract. -/
theorem currentAddresses {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old ar x) :
 (shared p f lhs rhs t old ar x I).currentK.coreTag = I.currentK.coreTag ∧
 (shared p f lhs rhs t old ar x I).currentK.verifierTag = I.currentK.verifierTag := ⟨rfl,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
