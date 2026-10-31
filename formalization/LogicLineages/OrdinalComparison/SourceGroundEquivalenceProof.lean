module
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDAGProof
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceScalarProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundEquivalence.Proof
open OriginalDomain SourceCollisionCompletion SourceCollisionCompletion.Proof
attribute [local irreducible] Phi actualCollapse

theorem g_lt_iff (a b : Nat) : g a<g b ↔ a<b := by
  constructor
  · intro h
    by_contra hn
    have hm := g_strictMono.monotone (show b≤a by omega)
    omega
  · intro h
    exact g_strictMono h

theorem g_le_iff (a b : Nat) : g a≤g b ↔ a≤b := by
  constructor
  · intro h
    by_contra hn
    have hm := g_strictMono (show b<a by omega)
    omega
  · intro h
    exact g_strictMono.monotone h

theorem magnified_gap (a b : Nat) (h : a<b) : g (3*a+3)+2≤g (3*b+3) := by
  have hh := g_four_lt (3*a+3) (3*b+3) (by omega)
  have hp := g_positive (3*a+3)
  omega

theorem numeric_equivalence (a b : Nat) :
    (a≤b ↔ g (g (3*a+3)+3)<g (g (3*b+3)+5)) ∧
    (a<b ↔ g (g (3*a+3)+5)≤g (g (3*b+3)+3)) := by
  rw [g_lt_iff,g_le_iff]
  constructor
  · constructor
    · intro h
      have hm := g_strictMono.monotone (show 3*a+3≤3*b+3 by omega)
      omega
    · intro h
      by_contra hn
      have hg := magnified_gap b a (by omega)
      omega
  · constructor
    · intro h
      have hg := magnified_gap a b h
      omega
    · intro h
      by_contra hn
      have hm := g_strictMono.monotone (show 3*b+3≤3*a+3 by omega)
      omega

theorem pointwise (Γ : List Ty) (a b : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ) :
    (rawScalar (valuation ρ) a≤rawScalar (valuation ρ) b ↔
      rawScalar (valuation ρ) (lower a)<rawScalar (valuation ρ) (upper b)) ∧
    (rawScalar (valuation ρ) a<rawScalar (valuation ρ) b ↔
      rawScalar (valuation ρ) (upper a)≤rawScalar (valuation ρ) (lower b)) := by
  unfold lower upper
  rw [identity_raw,constant_raw,constant_raw,identity_raw,magnify_raw,magnify_raw]
  exact numeric_equivalence _ _

theorem fullGroundEquivalence : Targets.FullGroundEquivalence := by
  refine ⟨pointwise,?_,?_⟩
  · intro Γ hΓ a b
    constructor
    · exact forall_congr' (fun ρ => (pointwise Γ a b (UnitObservation.substitution ρ)).1)
    · exact forall_congr' (fun ρ => (pointwise Γ a b (UnitObservation.substitution ρ)).2)
  · intro Γ d
    refine ⟨lower_input d,upper_input d,lower_size d,upper_size d,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals rfl
end LogicLineages.OrdinalComparison.Source.GroundEquivalence.Proof
