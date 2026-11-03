module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryObservationView OrdinaryFunctionalValue FiniteOccurrenceMatching MarkedCopyTest MarkedStatTest

theorem splitRelated {α β : Type} {R : α → β → Prop} (xs ys : List α) (zs : List β)
    (h : List.Forall₂ R (xs++ys) zs) : ∃ us vs,zs=us++vs ∧ List.Forall₂ R xs us ∧ List.Forall₂ R ys vs := by
  induction xs generalizing zs with
  | nil => exact ⟨[],zs,rfl,.nil,h⟩
  | cons x xs ih =>
      cases h with
      | cons hx h =>
          obtain ⟨us,vs,rfl,hu,hv⟩ := ih _ h
          exact ⟨_::us,vs,rfl,.cons hx hu,hv⟩

theorem relatedMember {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : ∀ x ∈ xs,∃ y ∈ ys,R x y := by
  induction h with
  | nil => intro x hx; cases hx
  | cons h rest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_,List.mem_cons_self,h⟩
      · obtain ⟨y,hy,hxy⟩ := ih x hx
        exact ⟨y,List.mem_cons_of_mem _ hy,hxy⟩

theorem pairMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P : World I} (strict : Bool) (p q : Packed I P) (hpq : PackedLE p q)
    (o : Observation Symbol arity I.context (budget I)) : pairBit strict p o ≤ pairBit strict q o := by
  rcases p with ⟨α,p⟩
  rcases q with ⟨β,q⟩
  have he : α=β := TypedExtraDownsetsProof.packedType hpq
  cases he
  exact TypedObservationAccessProof.readMonotone Symbol inferInstance arity I α.val P strict p q o
    ((TypedExtraDownsetsProof.packedSame α p q).mp hpq)

theorem strictSourceMonotone : MarkedStatTestTargets.StrictSourceMonotone := by
  intro Symbol inst arity I P xs ys ts hxy
  apply Bool.le_iff_imp.mpr
  intro ht
  obtain ⟨kept,removed,retained,inserted,hs,ht,hn,hw,hr⟩ :=
    (FiniteOccurrenceMatchingProof.strictSpec (pairBit false) (pairBit true) xs ts).mp ht
  obtain ⟨zs,hzs,hperm⟩ := List.perm_comp_forall₂ hs.symm hxy
  obtain ⟨kept',removed',he,hkept,hremoved⟩ := splitRelated kept removed zs hzs
  subst zs
  apply (FiniteOccurrenceMatchingProof.strictSpec (pairBit false) (pairBit true) ys ts).mpr
  refine ⟨kept',removed',retained,inserted,hperm.symm,ht,?_,?_,?_⟩
  · intro he
    have hlen := hremoved.length_eq
    rw [he] at hlen
    apply hn
    simpa using hlen
  · exact OrdinaryFunctionalNaturalityProof.orderedLift (pairBit false) (pairBit false)
      (List.Forall₂.imp (fun p q hpq o => pairMonotone false p q hpq o) hkept) retained hw
  · intro t hti
    obtain ⟨p,hp,hpt⟩ := hr t hti
    obtain ⟨q,hq,hpq⟩ := relatedMember hremoved p hp
    exact ⟨q,hq,Bool.le_iff_imp.mp (pairMonotone true p q hpq t) hpt⟩

theorem statCalibration : MarkedStatTestTargets.StatCalibration := by
  intro Symbol inst arity I M f P a o
  cases hv : rootView o.body with
  | none => simp [statTest,hv]
  | some data =>
      rcases data with ⟨g,args⟩
      simp only [statTest,hv,Bool.and_eq_true_iff,decide_eq_true_eq]
      rw [FiniteOccurrenceMatchingProof.strictCalibration Symbol inst arity I P (packBase f a.1) (plainChildren o),
        MarkedCopyTestProof.allChildrenCalibration Symbol inst arity I M f P a o]
      constructor
      · rintro ⟨⟨hh,hs⟩,hc⟩; exact ⟨g,args,rfl,hh,hs,hc⟩
      · rintro ⟨g',args',he,hh,hs,hc⟩
        have he' : (⟨g,args⟩ : RootData Symbol arity (portTypes o.ports++I.context))=⟨g',args'⟩ := Option.some.inj he
        cases he'
        exact ⟨⟨hh,hs⟩,hc⟩

theorem testMonotone : MarkedStatTestTargets.TestMonotone := by
  intro Symbol inst arity I M N f P a b o hMN hab
  have hpack : List.Forall₂ PackedLE (packBase f a.1) (packBase f b.1) := by
    apply OrdinaryFunctionalNaturalityProof.relatedOfFn
    intro i
    exact (TypedExtraDownsetsProof.packedSame _ _ _).mpr (hab.1 i)
  have hs := strictSourceMonotone Symbol inst arity I P (packBase f a.1) (packBase f b.1) (plainChildren o) hpack
  have hc := MarkedCopyTestProof.allChildrenMonotone f hMN hab o
  cases hv : rootView o.body with
  | none => simp only [statTest,hv,le_refl]
  | some data =>
      rcases data with ⟨g,args⟩
      simp only [statTest,hv]
      apply Bool.le_iff_imp.mpr
      intro ht
      obtain ⟨h12,h3⟩ := Bool.and_eq_true_iff.mp ht
      obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h12
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨h1,Bool.le_iff_imp.mp hs h2⟩,Bool.le_iff_imp.mp hc h3⟩

theorem coordinatesMonotone : MarkedStatTestTargets.CoordinatesMonotone := by
  intro Symbol inst arity I M N f τ P a b hMN hab Q o
  exact testMonotone Symbol inst arity I M N f Q.val _ _ o.val hMN
    ((inputFamily I f).restrictMonotone P Q.val Q.property a b hab)

theorem coordinatesWeakening : MarkedStatTestTargets.CoordinatesWeakening := by
  intro Symbol inst arity I M f τ P Q h a
  funext R o
  simp only [project,statCoordinates,(inputFamily I f).restrictComposition]

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestProof
