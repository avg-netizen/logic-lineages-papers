module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CurrentInstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RegistryInstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem installed {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (hall : ∀ q ∈ items f lhs rhs t old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 ∃ I : JointInstallation p f lhs rhs t old a x,
 I.currentK.coreTag = I.currentS.coreTag ∧ I.currentK.iteratorTag = I.currentS.iteratorTag := by
 obtain ⟨previous⟩ := CumulativeUniformRule12Registry.InstallationProof.installed p f lhs rhs t old a x
  (fun q hq => hall q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨K,S,hcore,hiterator⟩ := CurrentInstallationProof.installed (previousLogical f lhs rhs old) (arithmetic a) x p
  (fun q hq => hall q (by simp only [items,List.mem_append]; exact Or.inr hq))
 exact ⟨{previous,currentK := K,currentS := S},hcore,hiterator⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RegistryInstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RegistryInstallationProof
