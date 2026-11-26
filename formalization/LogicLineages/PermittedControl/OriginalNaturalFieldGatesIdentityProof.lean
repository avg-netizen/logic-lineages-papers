module
public import LogicLineages.PermittedControl.OriginalNaturalFieldGatesTargets
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNaturalFieldGates
open OrdinalComparison FieldComparison

private theorem identityAt (f : Nat → Nat) (mu : NONote) (x : Nat) (ok : IdentityDomain mu x) :
    (Interval.identity mu).firstHit f x 0 ∧ (Interval.identity mu).entryNorm f x 0 = x :=
  identityEntry f mu.1.repr x (normalRepresentationSound mu) ok.1 ok.2

theorem identityHit (f : Nat → Nat) (mu : NONote) (x i : Nat) (ok : IdentityDomain mu x) :
    (Interval.identity mu).firstHit f x i ↔ i = 0 := by
  have hit := (identityAt f mu x ok).1
  exact ⟨fun hi => firstEntry_unique f _ _ i 0 hi hit,fun eq => eq.symm ▸ hit⟩

theorem identityValue (f : Nat → Nat) (mu : NONote) (x v : Nat) (ok : IdentityDomain mu x) :
    (∃ i, (Interval.identity mu).firstHit f x i ∧
      v = (Interval.identity mu).entryNorm f x i) ↔ v = x := by
  have norm := (identityAt f mu x ok).2
  constructor
  · rintro ⟨i,hi,hv⟩
    have eq := (identityHit f mu x i ok).mp hi
    subst i
    exact hv.trans norm
  · intro hv
    exact ⟨0,(identityAt f mu x ok).1,hv.trans norm.symm⟩

theorem exactOrdinaryIdentityBoundary : ExactOrdinaryIdentityBoundary := by
  intro f mu x ok
  obtain ⟨hit,norm⟩ := identityAt f mu x ok
  refine ⟨hit,norm,?_⟩
  intro s o
  exact ⟨by simp only [Gate.readAt,identityRead,if_pos ok],
    by simp only [Gate.readAt,identityRead,if_pos ok]⟩

end LogicLineages.PermittedControl.OriginalNaturalFieldGates
