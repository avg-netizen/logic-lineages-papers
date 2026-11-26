import LogicLineages.PersistentMarking.MarkedExtrasFoundationProof
namespace LogicLineages.PersistentMarking.MarkedExtrasDownProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedExtras

theorem canonicalFilter (E : Environment) (Γ : Context) (p : Tagged → Bool) :
    Canonical E Γ ((universe E Γ).filter p) := by
  apply List.filter_congr
  intro a ha
  simp only [List.mem_filter,ha,true_and]
  cases h : p a <;> simp [h]

theorem canonicalMember (E : Environment) (Γ : Context) (xs : List Tagged)
    (h : Canonical E Γ xs) (a : Tagged) (ha : a ∈ xs) : a ∈ universe E Γ := by
  rw [h] at ha
  exact (List.mem_filter.mp ha).1

theorem canonicalExt (E : Environment) (Γ : Context) (xs ys : List Tagged)
    (hx : Canonical E Γ xs) (hy : Canonical E Γ ys)
    (h : ∀ a, a ∈ universe E Γ → (a ∈ xs ↔ a ∈ ys)) : xs=ys := by
  rw [hx,hy]
  apply List.filter_congr
  intro a ha
  exact congrArg decide (propext (h a ha))

theorem downExtra : MarkedExtrasTargets.DownIsExtra := by
  intro E Γ xs hw hxs
  refine ⟨canonicalFilter E Γ _,?_⟩
  intro a ha b hb hba
  obtain ⟨ham,x,hx,hax⟩ := (MarkedExtrasFoundationProof.downExact E Γ xs a).mp ha
  apply (MarkedExtrasFoundationProof.downExact E Γ xs b).mpr
  exact ⟨hb,x,hx,(MarkedExtrasFoundationProof.order E Γ hw).2.1 b a x hb ham (hxs x hx) hba hax⟩

theorem downIdentity : MarkedExtrasTargets.DownIdentity := by
  intro E Γ xs hw hx
  apply canonicalExt E Γ _ xs (canonicalFilter E Γ _) hx.1
  intro a ha
  constructor
  · intro h
    obtain ⟨ha',b,hb,hab⟩ := (MarkedExtrasFoundationProof.downExact E Γ xs a).mp h
    exact hx.2 b hb a ha hab
  · intro h
    exact (MarkedExtrasFoundationProof.downExact E Γ xs a).mpr
      ⟨ha,a,h,(MarkedExtrasFoundationProof.order E Γ hw).1 a ha⟩
end LogicLineages.PersistentMarking.MarkedExtrasDownProof
