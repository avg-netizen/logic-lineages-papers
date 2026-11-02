module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsProof
open Source FiniteObservationBits NaturalTupleLayer NaturalLayerBounds

theorem outputImage {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {P : World I} (S : Set (Natural I τ D P)) (Q R : Future P)
    (h : Extends Q.val R.val) (s : Suffix τ) (v : Tuple D s Q.val) :
    (resultFamily D s).restrict h '' ((fun a : Natural I τ D P => a.val.2 Q s v) '' S)=
      (fun a : Natural I τ D P => a.val.2 R s (tupleWeaken h v)) '' S := by
  ext x
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,(a.property.2 Q R h s v).symm⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.val.2 Q s v,⟨a,ha,rfl⟩,a.property.2 Q R h s v⟩

theorem supNatural : NaturalLayerBoundsTargets.SupNatural := by
  intro Symbol arity I τ D L P S
  constructor
  · intro Q s v w hv
    apply ((resultBounds L s).supSpec Q.val _).2
    rintro x ⟨a,ha,rfl⟩
    exact le_trans (a.property.1 Q s v w hv)
      (((resultBounds L s).supSpec Q.val _).1 ⟨a,ha,rfl⟩)
  · intro Q R h s v
    change (resultFamily D s).restrict h ((resultBounds L s).sup Q.val _)=(resultBounds L s).sup R.val _
    rw [(resultBounds L s).supRestriction,outputImage]

theorem infNatural : NaturalLayerBoundsTargets.InfNatural := by
  intro Symbol arity I τ D L P S
  constructor
  · intro Q s v w hv
    apply ((resultBounds L s).infSpec Q.val _).2
    rintro x ⟨a,ha,rfl⟩
    exact le_trans (((resultBounds L s).infSpec Q.val _).1 ⟨a,ha,rfl⟩)
      (a.property.1 Q s v w hv)
  · intro Q R h s v
    change (resultFamily D s).restrict h ((resultBounds L s).inf Q.val _)=(resultBounds L s).inf R.val _
    rw [(resultBounds L s).infRestriction,outputImage]

theorem supUniversal : NaturalLayerBoundsTargets.SupUniversal := by
  intro Symbol arity I τ D L P S
  constructor
  · rintro a ⟨x,hx,rfl⟩
    constructor
    · exact le_sSup ⟨x,hx,rfl⟩
    · intro Q s v
      exact ((resultBounds L s).supSpec Q.val _).1 ⟨x,hx,rfl⟩
  · intro a ha
    constructor
    · apply sSup_le
      rintro b ⟨x,hx,rfl⟩
      exact (ha ⟨x,hx,rfl⟩).1
    · intro Q s v
      apply ((resultBounds L s).supSpec Q.val _).2
      rintro b ⟨x,hx,rfl⟩
      exact (ha ⟨x,hx,rfl⟩).2 Q s v

theorem infUniversal : NaturalLayerBoundsTargets.InfUniversal := by
  intro Symbol arity I τ D L P S
  constructor
  · rintro a ⟨x,hx,rfl⟩
    constructor
    · exact sInf_le ⟨x,hx,rfl⟩
    · intro Q s v
      exact ((resultBounds L s).infSpec Q.val _).1 ⟨x,hx,rfl⟩
  · intro a ha
    constructor
    · apply le_sInf
      rintro b ⟨x,hx,rfl⟩
      exact (ha ⟨x,hx,rfl⟩).1
    · intro Q s v
      apply ((resultBounds L s).infSpec Q.val _).2
      rintro b ⟨x,hx,rfl⟩
      exact (ha ⟨x,hx,rfl⟩).2 Q s v

theorem supRestriction : NaturalLayerBoundsTargets.SupRestriction := by
  intro Symbol arity I τ D L P Q h S
  apply Prod.ext
  · change FiniteObservationBits.weaken h (sSup ((fun a : Natural I τ D P => a.val.1) '' S))=
      sSup ((fun a : Natural I τ D Q => a.val.1) '' (naturalWeaken h '' S))
    rw [FiniteObservationBitsProof.weakeningSuprema Symbol arity I τ P Q h _]
    simp only [Set.image_image]
    rfl
  · funext R s v
    change (resultBounds L s).sup R.val _=(resultBounds L s).sup R.val _
    congr 1
    rw [Set.image_image]
    rfl

theorem infRestriction : NaturalLayerBoundsTargets.InfRestriction := by
  intro Symbol arity I τ D L P Q h S
  apply Prod.ext
  · change FiniteObservationBits.weaken h (sInf ((fun a : Natural I τ D P => a.val.1) '' S))=
      sInf ((fun a : Natural I τ D Q => a.val.1) '' (naturalWeaken h '' S))
    rw [FiniteObservationBitsProof.weakeningInfima Symbol arity I τ P Q h _]
    simp only [Set.image_image]
    rfl
  · funext R s v
    change (resultBounds L s).inf R.val _=(resultBounds L s).inf R.val _
    congr 1
    rw [Set.image_image]
    rfl

/-- Mathematical induction supplier; the executable Family is unchanged. -/
noncomputable def layerBounds {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (L : LowerBounds D) :
    Bounds (NaturalTupleLayerProof.layerFamily I τ D) where
  sup := fun P S => ⟨supRaw L P S,supNatural Symbol arity I τ D L P S⟩
  inf := fun P S => ⟨infRaw L P S,infNatural Symbol arity I τ D L P S⟩
  supSpec := by
    intro P S
    have hu := supUniversal Symbol arity I τ D L P S
    constructor
    · intro a ha; exact hu.1 ⟨a,ha,rfl⟩
    · intro a ha
      apply hu.2
      rintro b ⟨x,hx,rfl⟩
      exact ha hx
  infSpec := by
    intro P S
    have hu := infUniversal Symbol arity I τ D L P S
    constructor
    · intro a ha; exact hu.1 ⟨a,ha,rfl⟩
    · intro a ha
      apply hu.2
      rintro b ⟨x,hx,rfl⟩
      exact ha hx
  supRestriction := by
    intro P Q h S
    apply Subtype.ext
    exact supRestriction Symbol arity I τ D L P Q h S
  infRestriction := by
    intro P Q h S
    apply Subtype.ext
    exact infRestriction Symbol arity I τ D L P Q h S

end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsProof
