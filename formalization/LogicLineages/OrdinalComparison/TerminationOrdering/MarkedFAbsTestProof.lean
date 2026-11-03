module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations Source.SourceTypeSupport FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess MarkedCopyTest MarkedFAbsTest

theorem freshAvailability : MarkedFAbsTestTargets.FreshAvailability := by
  intro Symbol inst arity I P σ υ body ho
  exact (Source.SourceOpenedObservationsProof.openedLambdaClosure Symbol arity I.context I.targetType I.target (budget I) P.val σ υ body ho).1

theorem genuineOpeningGuards : MarkedFAbsTestTargets.GenuineOpeningGuards := by
  intro Symbol inst arity I P σ υ body i ho hi
  have hc := Source.SourceOpenedObservationsProof.openedLambdaClosure Symbol arity I.context I.targetType I.target (budget I) P.val σ υ body ho
  have hsupport := Source.SourceOpenedObservationsProof.openedTypeSupport Symbol arity I.context I.targetType I.target (budget I) ⟨P.val,.arrow σ υ,.lam body⟩ ho
  have hb := Source.SourceTypeSupportProof.literalBinderSupport Symbol arity (portTypes P.val++I.context) σ υ body
  have hσ : σ ∈ types I := Finset.mem_union_right _ (hsupport (hb.2.1 (List.mem_toFinset.mpr (Ty.mem_subtypes_self σ))))
  have hυ : υ ∈ types I := Finset.mem_union_right _ (hsupport (hb.2.2.1
    (Source.SourceTypeSupportProof.actualResultSupport Symbol arity _ υ body)))
  have hp := (FiniteObservationBitsProof.worldCalibration Symbol arity I P.val).mp P.property
  have hw : ((i,σ)::P.val) ∈ worldList I := by
    apply (FiniteObservationBitsProof.worldCalibration Symbol arity I ((i,σ)::P.val)).mpr
    constructor
    · exact List.nodup_cons.mpr ⟨hi,hp.1⟩
    · intro p hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hσ
      · exact hp.2 p hm
  exact ⟨⟨hi,hw,hσ,hυ⟩,hc.2 i hi⟩

theorem lambdaCalibration : MarkedFAbsTestTargets.LambdaCalibration := by
  intro Symbol inst arity I M f P σ υ body a
  simp only [lambdaTest,decide_eq_true_eq]

theorem literalLambdaEquation : MarkedFAbsTestTargets.LiteralLambdaEquation := by
  intro Symbol inst arity I M f P σ υ body a
  simp [fAbsTest,bodyAtWorld,termTest]

theorem openingInputMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (f : HeadIndex I) {P : World I} {a b : Inputs I f P} (hab : a ≤ b)
    (σ υ : Ty) (i : Fin (budget I)) (h : Opening I P σ υ i) : openingInput f a σ υ i h ≤ openingInput f b σ υ i h := by
  apply FunctionalTupleBuilderProof.appendInputMonotone
  · exact (inputFamily I f).restrictMonotone P _ _ a b hab
  · intro p hp
    exact ⟨p,hp,(TypedExtraDownsetsProof.packedOrder Symbol inferInstance arity I _).1 p⟩

theorem openingReadMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) (σ υ : Ty)
    (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) (i : Fin (budget I)) (h : Opening I P σ υ i) :
    openingRead M f a σ υ body i h ≤ openingRead N f b σ υ body i h := by
  apply TypedObservationAccessProof.readMonotone Symbol inferInstance arity I υ _ false _ _ _
  exact le_trans (hMN f _ _ _) (N.property.1 f _ _ _ _ (openingInputMonotone f hab σ υ i h))

theorem lambdaMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) (σ υ : Ty)
    (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) :
    lambdaTest M f a σ υ body ≤ lambdaTest N f b σ υ body := by
  apply Bool.le_iff_imp.mpr
  simp only [lambdaTest,decide_eq_true_eq]
  rintro ⟨i,h,hw⟩
  exact ⟨i,h,Bool.le_iff_imp.mp (openingReadMonotone f hMN hab σ υ body i h) hw⟩

theorem termMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {M N : Constructors I} (f : HeadIndex I) {P : World I} {a b : Inputs I f P}
    (hMN : M ≤ N) (hab : a ≤ b) {τ : Ty} (t : Term Symbol arity (portTypes P.val++I.context) τ) :
    termTest M f a t ≤ termTest N f b t := by
  cases t <;> try exact le_rfl
  case lam body => exact lambdaMonotone f hMN hab _ _ body

theorem testMonotone : MarkedFAbsTestTargets.TestMonotone := by
  intro Symbol inst arity I M N f P a b o hMN hab
  by_cases hp : o.ports=P.val
  · simp only [fAbsTest,dif_pos hp]
    exact termMonotone f hMN hab _
  · simp only [fAbsTest,dif_neg hp,le_refl]

theorem coordinatesMonotone : MarkedFAbsTestTargets.CoordinatesMonotone := by
  intro Symbol inst arity I M N f τ P a b hMN hab Q o
  exact testMonotone Symbol inst arity I M N f Q.val _ _ o.val hMN
    ((inputFamily I f).restrictMonotone P Q.val Q.property a b hab)

theorem coordinatesWeakening : MarkedFAbsTestTargets.CoordinatesWeakening := by
  intro Symbol inst arity I M f τ P Q h a
  funext R o
  simp only [project,fAbsCoordinates,(inputFamily I f).restrictComposition]

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestProof
