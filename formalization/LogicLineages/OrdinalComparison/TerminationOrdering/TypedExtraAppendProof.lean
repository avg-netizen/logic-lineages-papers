module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets TypedExtraAppend TypedExtraDownsetsProof

theorem membershipCalibration : TypedExtraAppendTargets.MembershipCalibration := by
  intro Symbol inst arity I P E xs a
  simp only [appendRaw,Finset.mem_filter,Finset.mem_univ,true_and,contains]

theorem downwardClosure : TypedExtraAppendTargets.DownwardClosure := by
  intro Symbol inst arity I P E xs τ a ha b hba
  have hm := membershipCalibration Symbol inst arity I P E xs
  apply (hm ⟨τ,b⟩).mpr
  rcases (hm ⟨τ,a⟩).mp ha with ha | ⟨p,hp,hap⟩
  · exact Or.inl ((E τ).property a ha b hba)
  · exact Or.inr ⟨p,hp,(packedOrder Symbol inst arity I P).2.1 _ _ _ ((packedSame τ b a).mpr hba) hap⟩

theorem emptyIdentity : TypedExtraAppendTargets.EmptyIdentity := by
  intro Symbol inst arity I P E τ
  apply Finset.ext
  intro a
  simp only [appendRaw,Finset.mem_filter,Finset.mem_univ,true_and,List.not_mem_nil,false_and,exists_false,or_false]

theorem suppliedIncluded : TypedExtraAppendTargets.SuppliedIncluded := by
  intro Symbol inst arity I P E xs p hp
  exact (membershipCalibration Symbol inst arity I P E xs p).mpr
    (Or.inr ⟨p,hp,(packedOrder Symbol inst arity I P).1 p⟩)

theorem appendMonotone : TypedExtraAppendTargets.AppendMonotone := by
  intro Symbol inst arity I P E F xs ys hef hxy τ a ha
  apply (membershipCalibration Symbol inst arity I P F ys ⟨τ,a⟩).mpr
  rcases (membershipCalibration Symbol inst arity I P E xs ⟨τ,a⟩).mp ha with ha | ⟨p,hp,hap⟩
  · exact Or.inl (hef τ ha)
  · obtain ⟨q,hq,hpq⟩ := hxy p hp
    exact Or.inr ⟨q,hq,(packedOrder Symbol inst arity I P).2.1 _ _ _ hap hpq⟩

theorem leastClosure : TypedExtraAppendTargets.LeastClosure := by
  intro Symbol inst arity I P E F xs hef hxs τ a ha
  rcases (membershipCalibration Symbol inst arity I P E xs ⟨τ,a⟩).mp ha with ha | ⟨p,hp,hap⟩
  · exact hef τ ha
  · exact (fiberRepresentation Symbol inst arity I P).1 F p (hxs p hp) ⟨τ,a⟩ hap

theorem packedWeakenMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} {P Q : World I} (h : Extends P Q) {a b : Packed I P}
    (hab : PackedLE a b) : PackedLE (packedWeaken h a) (packedWeaken h b) := by
  rcases a with ⟨α,a⟩
  rcases b with ⟨β,b⟩
  have he : α=β := packedType hab
  cases he
  exact (packedSame α _ _).mpr ((family I α.val).restrictMonotone P Q h a b ((packedSame α a b).mp hab))

theorem restrictionAppend : TypedExtraAppendTargets.RestrictionAppend := by
  intro Symbol inst arity I P Q h E xs τ
  apply Finset.ext
  intro b
  let F := (extrasFamily I).restrict h E
  constructor
  · intro hb
    obtain ⟨a,ha,hba⟩ := (imageMembership h _ b).mp hb
    apply (membershipCalibration Symbol inst arity I Q F (xs.map (packedWeaken h)) ⟨τ,b⟩).mpr
    rcases (membershipCalibration Symbol inst arity I P E xs ⟨τ,a⟩).mp ha with ha | ⟨p,hp,hap⟩
    · exact Or.inl ((imageMembership h (E τ).val b).mpr ⟨a,ha,hba⟩)
    · exact Or.inr ⟨packedWeaken h p,List.mem_map.mpr ⟨p,hp,rfl⟩,
        (packedOrder Symbol inst arity I Q).2.1 _ _ _ ((packedSame τ _ _).mpr hba) (packedWeakenMonotone h hap)⟩
  · intro hb
    rcases (membershipCalibration Symbol inst arity I Q F (xs.map (packedWeaken h)) ⟨τ,b⟩).mp hb with hb | ⟨p,hp,hbp⟩
    · obtain ⟨a,ha,hba⟩ := (imageMembership h (E τ).val b).mp hb
      exact (imageMembership h _ b).mpr ⟨a,(membershipCalibration Symbol inst arity I P E xs ⟨τ,a⟩).mpr (Or.inl ha),hba⟩
    · obtain ⟨p,hxs,rfl⟩ := List.mem_map.mp hp
      rcases p with ⟨υ,a⟩
      have he : τ=υ := packedType hbp
      cases he
      exact (imageMembership h _ b).mpr ⟨a,suppliedIncluded Symbol inst arity I P E xs ⟨τ,a⟩ hxs,(packedSame τ _ _).mp hbp⟩

/-- Executable whole-list append on the actual extra downsets. -/
def appendExtras {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (E : Extras I P) (xs : List (Packed I P)) : Extras I P := fun τ =>
  ⟨appendRaw E xs τ,downwardClosure Symbol inferInstance arity I P E xs τ⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendProof
