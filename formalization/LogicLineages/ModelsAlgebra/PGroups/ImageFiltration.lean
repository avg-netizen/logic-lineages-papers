module
public import LogicLineages.ModelsAlgebra.PGroups.ImageFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem image_finite_filtration : Targets.groupImageFiniteFiltration := by
  intro G _ p k j
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨z,hz⟩ := (finite_filtration_multiple_image (multipleImage G (p ^ k)) p j).le hy
    obtain ⟨w,hw⟩ := z.property
    apply (finite_filtration_multiple_image G p (k+j)).ge
    refine ⟨w, ?_⟩
    have hz' : p ^ j • (z : G) = (y : G) := congrArg Subtype.val hz
    change p ^ (k+j) • w = (y : G)
    change p ^ k • w = (z : G) at hw
    rw [pow_add, mul_comm, mul_smul, hw, hz']
  · intro hx
    obtain ⟨w,hw⟩ := (finite_filtration_multiple_image G p (k+j)).le hx
    let z : multipleImage G (p ^ k) := ⟨p ^ k • w, ⟨w,rfl⟩⟩
    refine ⟨p ^ j • z, (finite_filtration_multiple_image (multipleImage G (p ^ k)) p j).ge ⟨z,rfl⟩, ?_⟩
    change p ^ j • (p ^ k • w) = x
    change p ^ (k+j) • w = x at hw
    calc
      p ^ j • (p ^ k • w) = (p ^ j * p ^ k) • w := (mul_smul _ _ _).symm
      _ = p ^ (k+j) • w := by rw [pow_add, Nat.mul_comm (p ^ k) (p ^ j)]
      _ = x := hw

theorem image_finite_socle : Targets.groupImageFiniteSocle := by
  intro G _ p k j
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨(image_finite_filtration G p k j).le ⟨y,hy.1,rfl⟩, ?_⟩
    exact congrArg Subtype.val hy.2
  · intro hx
    obtain ⟨y,hy,hxy⟩ := (image_finite_filtration G p k j).ge hx.1
    refine ⟨y, ⟨hy, ?_⟩,hxy⟩
    apply Subtype.ext
    change p • (y : G) = 0
    change (y : G) = x at hxy
    rw [hxy]
    exact hx.2

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
