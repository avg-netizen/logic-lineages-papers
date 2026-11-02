module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryObservationView MarkedCopyTest

theorem genuineChildGuards : MarkedCopyTestTargets.GenuineChildGuards := by
  intro Symbol inst arity I o ho c hc
  apply (OrdinaryObservationViewProof.childProvenance Symbol arity I o c ho _).2.2
  rw [OrdinaryObservationViewProof.plainChildrenCalibration]
  exact hc

theorem childCalibration {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (o : Observation Symbol arity I.context (budget I)) :
    childWeak M f a o=true ↔ ∃ ht : o.resultType ∈ types I,readBit false (M.val f ⟨o.resultType,ht⟩ P a) o=true := by
  by_cases ht : o.resultType ∈ types I
  · simp only [childWeak,dif_pos ht]
    exact ⟨fun h => ⟨ht,h⟩,fun ⟨_,h⟩ => h⟩
  · simp only [childWeak,dif_neg ht,Bool.false_eq_true]
    exact ⟨False.elim,fun ⟨h,_⟩ => ht h⟩

theorem allChildrenCalibration : MarkedCopyTestTargets.AllChildrenCalibration := by
  intro Symbol inst arity I M f P a o
  simp only [allChildrenWeak,List.all_eq_true,childCalibration]

theorem copyCalibration : MarkedCopyTestTargets.CopyCalibration := by
  intro Symbol inst arity I above dec M f P a o
  cases hv : rootView o.body with
  | none => simp [copyTest,hv]
  | some data =>
      rcases data with ⟨g,args⟩
      simp only [copyTest,hv,Bool.and_eq_true_iff,decide_eq_true_eq]
      rw [allChildrenCalibration Symbol inst arity I M f P a o]
      constructor
      · rintro ⟨hh,hc⟩; exact ⟨g,args,rfl,hh,hc⟩
      · rintro ⟨g',args',he,hh,hc⟩
        have he' : (⟨g,args⟩ : RootData Symbol arity (portTypes o.ports++I.context))=⟨g',args'⟩ := Option.some.inj he
        cases he'
        exact ⟨hh,hc⟩

theorem childMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) (o : Observation Symbol arity I.context (budget I)) :
    childWeak M f a o ≤ childWeak N f b o := by
  by_cases ht : o.resultType ∈ types I
  · simp only [childWeak,dif_pos ht]
    apply TypedObservationAccessProof.readMonotone Symbol inferInstance arity I o.resultType P false _ _ o
    exact le_trans (hMN f _ P a) (N.property.1 f _ P a b hab)
  · simp only [childWeak,dif_neg ht,le_refl]

theorem allChildrenMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) (o : Observation Symbol arity I.context (budget I)) :
    allChildrenWeak M f a o ≤ allChildrenWeak N f b o := by
  apply Bool.le_iff_imp.mpr
  simp only [allChildrenWeak,List.all_eq_true]
  intro hc c hm
  exact Bool.le_iff_imp.mp (childMonotone f hMN hab c) (hc c hm)

theorem testMonotone : MarkedCopyTestTargets.TestMonotone := by
  intro Symbol inst arity I above dec M N f P a b o hMN hab
  cases hv : rootView o.body with
  | none => simp only [copyTest,hv,le_refl]
  | some data =>
      rcases data with ⟨g,args⟩
      simp only [copyTest,hv]
      apply Bool.le_iff_imp.mpr
      intro ht
      obtain ⟨hh,hc⟩ := Bool.and_eq_true_iff.mp ht
      exact Bool.and_eq_true_iff.mpr ⟨hh,Bool.le_iff_imp.mp (allChildrenMonotone f hMN hab o) hc⟩

theorem coordinatesMonotone : MarkedCopyTestTargets.CoordinatesMonotone := by
  intro Symbol inst arity I above dec M N f τ P a b hMN hab Q o
  exact testMonotone Symbol inst arity I above dec M N f Q.val _ _ o.val hMN
    ((inputFamily I f).restrictMonotone P Q.val Q.property a b hab)

theorem coordinatesWeakening : MarkedCopyTestTargets.CoordinatesWeakening := by
  intro Symbol inst arity I above dec M f τ P Q h a
  funext R o
  simp only [project,copyCoordinates,(inputFamily I f).restrictComposition]

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestProof
