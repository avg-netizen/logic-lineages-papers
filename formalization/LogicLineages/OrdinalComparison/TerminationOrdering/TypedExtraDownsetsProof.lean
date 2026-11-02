module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets

theorem packedSame {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (τ : TypeIndex I) (a b : Value I τ.val P) : PackedLE ⟨τ,a⟩ ⟨τ,b⟩ ↔ a ≤ b := by
  simp only [PackedLE,dif_pos rfl]
  rfl

theorem packedType {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    {a b : Packed I P} (h : PackedLE a b) : a.1=b.1 := by
  by_cases he : a.1=b.1
  · exact he
  · simp only [PackedLE,dif_neg he] at h

theorem packedOrder : TypedExtraDownsetsTargets.PackedOrder := by
  intro Symbol inst arity I P
  refine ⟨?_,?_,?_⟩
  · rintro ⟨τ,a⟩
    exact (packedSame τ a a).mpr le_rfl
  · rintro ⟨α,a⟩ ⟨β,b⟩ ⟨γ,c⟩ hab hbc
    have he : α=β := packedType hab
    cases he
    have he : α=γ := packedType hbc
    cases he
    exact (packedSame α a c).mpr (le_trans ((packedSame α a b).mp hab) ((packedSame α b c).mp hbc))
  · rintro ⟨α,a⟩ ⟨β,b⟩ hab hba
    have he : α=β := packedType hab
    cases he
    have hv := le_antisymm ((packedSame α a b).mp hab) ((packedSame α b a).mp hba)
    cases hv
    rfl

theorem fiberRepresentation : TypedExtraDownsetsTargets.FiberRepresentation := by
  intro Symbol inst arity I P
  constructor
  · intro E
    rintro ⟨α,a⟩ ha ⟨β,b⟩ hba
    have he : β=α := packedType hba
    cases he
    exact (E α).property a ha b ((packedSame α b a).mp hba)
  · intro S hS
    classical
    let E : Extras I P := fun τ => ⟨Finset.univ.filter (fun a : Value I τ.val P => (⟨τ,a⟩ : Packed I P) ∈ S),by
      intro a ha b hba
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact hS ⟨τ,a⟩ ha ⟨τ,b⟩ ((packedSame τ b a).mpr hba)⟩
    have he : ∀ a,contains E a ↔ a ∈ S := by
      rintro ⟨τ,a⟩
      simp only [contains,E,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨E,he,?_⟩
    intro F hF
    funext τ
    apply Subtype.ext
    apply Finset.ext
    intro a
    exact (hF ⟨τ,a⟩).trans (he ⟨τ,a⟩).symm

theorem exhaustiveEnumeration : TypedExtraDownsetsTargets.ExhaustiveEnumeration := by
  intro Symbol inst arity I P E
  exact Finset.mem_univ E

theorem imageMembership {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {P Q : World I} (h : Extends P Q) (E : Finset (Value I τ P)) (b : Value I τ Q) :
    b ∈ imageFiber h E ↔ ∃ a ∈ E,b ≤ RecursiveNaturalDomains.weaken h a := by
  simp only [imageFiber,Finset.mem_filter,Finset.mem_univ,true_and]

theorem downwardImage : TypedExtraDownsetsTargets.DownwardImage := by
  intro Symbol inst arity I τ P Q h E a ha b hba
  obtain ⟨x,hx,hax⟩ := (imageMembership h E a).mp ha
  exact (imageMembership h E b).mpr ⟨x,hx,le_trans hba hax⟩

theorem imageIdentity : TypedExtraDownsetsTargets.ImageIdentity := by
  intro Symbol inst arity I τ P E
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb,hab⟩ := (imageMembership _ E.val a).mp ha
    rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inst arity I τ P b] at hab
    exact E.property b hb a hab
  · intro ha
    apply (imageMembership _ E.val a).mpr
    refine ⟨a,ha,?_⟩
    rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inst arity I τ P a]

theorem imageComposition : TypedExtraDownsetsTargets.ImageComposition := by
  intro Symbol inst arity I τ P Q R h k E
  apply Finset.ext
  intro c
  constructor
  · intro hc
    obtain ⟨b,hb,hcb⟩ := (imageMembership k _ c).mp hc
    obtain ⟨a,ha,hba⟩ := (imageMembership h E b).mp hb
    apply (imageMembership _ E c).mpr
    refine ⟨a,ha,?_⟩
    rw [←RecursiveNaturalDomainsProof.weakeningComposition Symbol inst arity I τ P Q R h k a]
    exact le_trans hcb ((family I τ).restrictMonotone Q R k b _ hba)
  · intro hc
    obtain ⟨a,ha,hca⟩ := (imageMembership _ E c).mp hc
    apply (imageMembership k _ c).mpr
    refine ⟨RecursiveNaturalDomains.weaken h a,(imageMembership h E _).mpr ⟨a,ha,le_rfl⟩,?_⟩
    rw [RecursiveNaturalDomainsProof.weakeningComposition Symbol inst arity I τ P Q R h k a]
    exact hca

theorem imageMonotone : TypedExtraDownsetsTargets.ImageMonotone := by
  intro Symbol inst arity I τ P Q h E F hef b hb
  obtain ⟨a,ha,hba⟩ := (imageMembership h E b).mp hb
  exact (imageMembership h F b).mpr ⟨a,hef ha,hba⟩

theorem packedImageCalibration : TypedExtraDownsetsTargets.PackedImageCalibration := by
  intro Symbol inst arity I P Q h E b
  rcases b with ⟨τ,b⟩
  constructor
  · intro hb
    obtain ⟨a,ha,hba⟩ := (imageMembership h (E τ).val b).mp hb
    exact ⟨⟨τ,a⟩,ha,(packedSame τ b _).mpr hba⟩
  · rintro ⟨⟨υ,a⟩,ha,hba⟩
    have he : τ=υ := packedType hba
    cases he
    exact (imageMembership h (E τ).val b).mpr ⟨a,ha,(packedSame τ b _).mp hba⟩

/-- Actual finite ordered extra family used later as constructor inputs. -/
def extrasFamily {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) : Family I where
  carrier := Extras I
  finite := fun P => extrasFinite I P
  equality := fun P E F =>
    decidable_of_iff (E ≤ F ∧ F ≤ E)
      ⟨fun h => le_antisymm h.1 h.2,fun h => by cases h; exact ⟨le_rfl,le_rfl⟩⟩
  order := fun P => inferInstance
  orderDecision := fun P E F => inferInstanceAs (Decidable (∀ τ,(E τ).val ⊆ (F τ).val))
  restrict := fun {P Q} h E τ => ⟨imageFiber h (E τ).val,downwardImage Symbol inferInstance arity I τ.val P Q h (E τ).val⟩
  restrictIdentity := by
    intro P E
    funext τ
    apply Subtype.ext
    exact imageIdentity Symbol inferInstance arity I τ.val P (E τ)
  restrictComposition := by
    intro P Q R h k E
    funext τ
    apply Subtype.ext
    exact imageComposition Symbol inferInstance arity I τ.val P Q R h k (E τ).val
  restrictMonotone := by
    intro P Q h E F hef τ
    exact imageMonotone Symbol inferInstance arity I τ.val P Q h (E τ).val (F τ).val (hef τ)

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsProof
