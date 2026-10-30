module
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsTargets
public import LogicLineages.OrdinalComparison.CollectedFiniteClosureProof
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem coefficient_bound (tags : CollectedPositiveTags) :
    collectedCoefficientSum tags≤collectedTagsEncode tags := by
  cases tags with
  | nil => exact le_rfl
  | cons rho A a rest =>
    have ih := coefficient_bound rest
    have h1 := Nat.add_le_pair a (collectedTagsEncode rest)
    have h2 := Nat.right_le_pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))
    change a+collectedCoefficientSum rest≤1+Nat.pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))
    omega
termination_by tags

theorem collectedCoefficientCodeBound : Targets.CollectedCoefficientCodeBound := coefficient_bound

theorem collectedComponentCodeBounds : Targets.CollectedComponentCodeBounds := by
  intro c b tags
  have h1 := Nat.left_le_pair c (Nat.pair b (collectedTagsEncode tags))
  have h2 := Nat.right_le_pair c (Nat.pair b (collectedTagsEncode tags))
  have h3 := Nat.left_le_pair b (collectedTagsEncode tags)
  have h4 := Nat.right_le_pair b (collectedTagsEncode tags)
  have h5 := coefficient_bound tags
  change c≤Nat.pair c (Nat.pair b (collectedTagsEncode tags)) ∧
    b≤Nat.pair c (Nat.pair b (collectedTagsEncode tags)) ∧
    collectedCoefficientSum tags≤Nat.pair c (Nat.pair b (collectedTagsEncode tags))
  omega

mutual
  private theorem form_bounds (F : CollectedPositiveNF) : ∀ A∈collectedFormClosure F,
      collectedPositiveEncode A≤collectedPositiveEncode F ∧
      collectedOneInputThreshold A≤collectedOneInputThreshold F := by
    cases F with
    | mk c b tags =>
      intro A hm
      rcases List.mem_cons.mp hm with h | h
      · subst A; exact ⟨le_rfl,le_rfl⟩
      · have hb := tag_bounds tags A h
        have h1 := Nat.right_le_pair b (collectedTagsEncode tags)
        have h2 := Nat.right_le_pair c (Nat.pair b (collectedTagsEncode tags))
        exact ⟨hb.1.trans (h1.trans h2),hb.2⟩
  private theorem tag_bounds (tags : CollectedPositiveTags) : ∀ A∈collectedTagFormClosure tags,
      collectedPositiveEncode A≤collectedTagsEncode tags ∧
      collectedOneInputThreshold A≤collectedTagsOneInputThreshold tags := by
    cases tags with
    | nil => simp [collectedTagFormClosure]
    | cons rho B b rest =>
      intro A hm
      have hkey := Nat.right_le_pair (rawNoteEncode rho.1) (collectedPositiveEncode B)
      have hleft := Nat.left_le_pair (collectedTagKey rho B) (Nat.pair b (collectedTagsEncode rest))
      have hright := Nat.right_le_pair (collectedTagKey rho B) (Nat.pair b (collectedTagsEncode rest))
      have hrest := Nat.right_le_pair b (collectedTagsEncode rest)
      rcases List.mem_append.mp hm with h | h
      · have hb := form_bounds B A h
        refine ⟨?_,hb.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
        change collectedPositiveEncode A≤1+Nat.pair (collectedTagKey rho B) (Nat.pair b (collectedTagsEncode rest))
        change collectedPositiveEncode B≤collectedTagKey rho B at hkey
        omega
      · have hb := tag_bounds rest A h
        refine ⟨?_,hb.2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
        change collectedPositiveEncode A≤1+Nat.pair (collectedTagKey rho B) (Nat.pair b (collectedTagsEncode rest))
        omega
end

private theorem root_code_bound (forms : List CollectedPositiveNF) (A : CollectedPositiveNF)
    (h : A∈forms) : collectedPositiveEncode A≤collectedRootCodeBound forms := by
  induction forms with
  | nil => simp at h
  | cons B forms ih =>
    rcases List.mem_cons.mp h with h | h
    · subst A; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem root_threshold_bound (forms : List CollectedPositiveNF) (A : CollectedPositiveNF)
    (h : A∈forms) : collectedOneInputThreshold A≤collectedFamilyThreshold forms := by
  induction forms with
  | nil => simp at h
  | cons B forms ih =>
    rcases List.mem_cons.mp h with h | h
    · subst A; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem root_threshold_pos (forms : List CollectedPositiveNF) : 1≤collectedFamilyThreshold forms := by
  induction forms with
  | nil => exact le_rfl
  | cons A forms ih => exact ih.trans (le_max_right _ _)

theorem collectedClosureBounds : Targets.CollectedClosureBounds := by
  intro forms A hm
  rcases List.mem_cons.mp hm with h | h
  · subst A
    exact ⟨Nat.zero_le _,root_threshold_pos forms⟩
  · rcases List.mem_flatMap.mp h with ⟨F,hF,hAF⟩
    have hb := form_bounds F A hAF
    exact ⟨hb.1.trans (root_code_bound forms F hF),hb.2.trans (root_threshold_bound forms F hF)⟩

private theorem maximum_code_primrec : Primrec (fun codes : List Nat => codes.foldr max 0) := by
  have hh : Primrec₂ (fun (_ : List Nat) (p : Nat × Nat) => max p.1 p.2) :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (f := fun codes : List Nat => codes)
    (g := fun _ : List Nat => (0 : Nat))
    (h := fun (_ : List Nat) (p : Nat × Nat) => max p.1 p.2) Primrec.id (Primrec.const 0) hh

theorem encodedCollectedZeroBoundPrimitiveRecursive : Targets.EncodedCollectedZeroBoundPrimitiveRecursive :=
  Primrec.nat_max.comp encodedCollectedThresholdPrimitiveRecursive.2
    (Primrec.nat_max.comp (Primrec.const 4)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) maximum_code_primrec) (Primrec.const 1)))

private theorem mapped_code_max (forms : List CollectedPositiveNF) :
    (forms.map collectedPositiveEncode).foldr max 0=collectedRootCodeBound forms := by
  induction forms with
  | nil => rfl
  | cons A forms ih =>
    change max (collectedPositiveEncode A) ((forms.map collectedPositiveEncode).foldr max 0)=_
    rw [ih]
    rfl

theorem encodedCollectedZeroBoundCorrect : Targets.EncodedCollectedZeroBoundCorrect := by
  intro forms
  unfold encodedCollectedZeroBound collectedFiniteZeroBound
  rw [encodedCollectedFamilyThresholdCorrect forms,mapped_code_max forms]

end LogicLineages.OrdinalComparison
