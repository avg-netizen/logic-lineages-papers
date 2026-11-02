module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryFunctionalValue FullTuplePacking MarkedCopyTest MarkedSelectTest

theorem selfTupleCalibration : MarkedSelectTestTargets.SelfTupleCalibration := by
  intro Symbol inst arity I M f P a τ s
  exact ⟨fun _ => rfl,FullTuplePackingProof.exactLength Symbol inst arity I τ s P _⟩

theorem candidateCalibration {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (p : Packed I P) (o : Observation Symbol arity I.context (budget I)) :
    candidateTest M f a p o=true ↔
      (p.1.val=o.resultType ∧ readBit false p.2 o=true) ∨
      ∃ s : Suffix p.1.val,s.val.2=o.resultType ∧ readBit false (applyValue p.2 s (selfTuple M f a p.1 s)) o=true := by
  simp only [candidateTest,Bool.or_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq]

theorem selectCalibration : MarkedSelectTestTargets.SelectCalibration := by
  intro Symbol inst arity I M f P a o
  simp only [selectTest,decide_eq_true_eq,Selected,candidateCalibration]

theorem selectedMonotone : MarkedSelectTestTargets.SelectedMonotone := by
  intro Symbol inst arity I f P a b hab p hp
  rcases hp with hp | hp
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
    cases hi
    refine ⟨⟨baseTag I f i,b.1 i⟩,Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩),?_⟩
    exact (TypedExtraDownsetsProof.packedSame _ _ _).mpr (hab.1 i)
  · exact ⟨p,Or.inr (hab.2 p.1 hp),(TypedExtraDownsetsProof.packedOrder Symbol inst arity I P).1 p⟩

theorem fullApplicationMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {τ : Ty} {P : World I} (p q : Value I τ P) (hpq : p ≤ q) (s : Suffix τ)
    (v w : FullTuple I τ s P) (hvw : v ≤ w) : applyValue p s v ≤ applyValue q s w := by
  have hv := (RecursiveNaturalDomainsProof.transportOrder (family I τ)
    (NaturalTupleLayerProof.layerFamily I τ (lower I τ)) (familyEquation I τ) P p q).mp hpq
  change layerView I τ P p ≤ layerView I τ P q at hv
  exact le_trans (hv.2 ⟨P,fun _ hp => hp⟩ s v)
    (RecursiveNaturalDomainsProof.applicationMonotone Symbol inferInstance arity I τ P q s v w hvw)

theorem selfTupleMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) (τ : TypeIndex I) (s : Suffix τ.val) :
    selfTuple M f a τ s ≤ selfTuple N f b τ s := by
  intro i
  exact le_trans (hMN f (argumentTag I τ s i) P a) (N.property.1 f _ P a b hab)

theorem candidateMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) (p q : Packed I P) (hpq : PackedLE p q)
    (o : Observation Symbol arity I.context (budget I)) : candidateTest M f a p o ≤ candidateTest N f b q o := by
  rcases p with ⟨α,p⟩
  rcases q with ⟨β,q⟩
  have he : α=β := TypedExtraDownsetsProof.packedType hpq
  cases he
  have hv := (TypedExtraDownsetsProof.packedSame α p q).mp hpq
  apply Bool.le_iff_imp.mpr
  intro ht
  apply (candidateCalibration N f b ⟨α,q⟩ o).mpr
  rcases (candidateCalibration M f a ⟨α,p⟩ o).mp ht with ⟨he,hw⟩ | ⟨s,hs,hw⟩
  · exact Or.inl ⟨he,Bool.le_iff_imp.mp (TypedObservationAccessProof.readMonotone Symbol inferInstance arity I α.val P false p q o hv) hw⟩
  · refine Or.inr ⟨s,hs,?_⟩
    exact Bool.le_iff_imp.mp (TypedObservationAccessProof.readMonotone Symbol inferInstance arity I s.val.2 P false _ _ o
      (fullApplicationMonotone p q hv s _ _ (selfTupleMonotone f hMN hab α s))) hw

theorem testMonotone : MarkedSelectTestTargets.TestMonotone := by
  intro Symbol inst arity I M N f P a b o hMN hab
  apply Bool.le_iff_imp.mpr
  simp only [selectTest,decide_eq_true_eq]
  rintro ⟨p,hp,ht⟩
  obtain ⟨q,hq,hpq⟩ := selectedMonotone Symbol inst arity I f P a b hab p hp
  exact ⟨q,hq,Bool.le_iff_imp.mp (candidateMonotone f hMN hab p q hpq o) ht⟩

theorem coordinatesMonotone : MarkedSelectTestTargets.CoordinatesMonotone := by
  intro Symbol inst arity I M N f τ P a b hMN hab Q o
  exact testMonotone Symbol inst arity I M N f Q.val _ _ o.val hMN
    ((inputFamily I f).restrictMonotone P Q.val Q.property a b hab)

theorem coordinatesWeakening : MarkedSelectTestTargets.CoordinatesWeakening := by
  intro Symbol inst arity I M f τ P Q h a
  funext R o
  simp only [project,selectCoordinates,(inputFamily I f).restrictComposition]

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestProof
