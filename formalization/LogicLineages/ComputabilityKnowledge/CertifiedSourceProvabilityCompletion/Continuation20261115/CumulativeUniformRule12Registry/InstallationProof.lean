module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.CurrentInstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Both complete packages rebuilt from actual same-root structural memberships. -/
theorem installed {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (hall : ∀ q ∈ items f lhs rhs t old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (JointInstallation p f lhs rhs t old a x) := by
 obtain ⟨previous⟩ := CumulativeUniformRule13Registry.InstallationProof.installed p f lhs rhs t old a x
  (fun q hq => hall q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨current⟩ := CurrentInstallationProof.installed (previousLogical f lhs rhs old)
  (RawMulNewestAddition.arithmetic a) x p
  (fun q hq => hall q (by simp only [items,List.mem_append]; exact Or.inr hq))
 exact ⟨{previous,current}⟩
theorem finiteInstallation (f : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (x : Program 3) :
 Nonempty (JointInstallation (carrier f lhs rhs t old a x) f lhs rhs t old a x) := by
 let p := carrier f lhs rhs t old a x
 have hall : ∀ q ∈ items f lhs rhs t old a x, ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (items f lhs rhs t old a x) 6 p 0
   (GorbowPRRegistry.StatementChecks.rootTag 6 p)
 exact installed p f lhs rhs t old a x hall
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.InstallationProof
