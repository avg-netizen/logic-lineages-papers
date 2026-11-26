module
public import LogicLineages.PermittedControl.InitialCodeListSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem initial_exception_list_iff (delta : Ordinal.{0}) (hd : delta < epsilonZero) (hpos : delta ≠ 0)
    (c d : Nat) :
    ((((3 : Ordinal) ≤ Ordinal.log Ordinal.omega0 delta ∧ ∃ n : Nat,
      (originalGapUnits delta).tail=(2 : Ordinal)::List.replicate n 1) ∨
      (Ordinal.log Ordinal.omega0 delta=2 ∧ ∃ n : Nat,
      (originalGapUnits delta).tail=(2 : Ordinal)::List.replicate n 1)) ∧
      (min c d+actualOrdinalNorm (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)))%2=1) ↔
    ((3 ≤ Ordinal.log Ordinal.omega0 delta ∧ ∃ n : Nat,
      delta=Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) ∧
      (min c d+actualOrdinalNorm (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)))%2=1) ∨
     (∃ n : Nat, delta=Ordinal.omega0^(2 : Ordinal)*2+Ordinal.omega0*(n : Ordinal) ∧
      (min c d+actualOrdinalNorm (Ordinal.omega0^(2 : Ordinal)))%2=1)) := by
  obtain ⟨l,hl⟩ := original_units_head delta hd hpos
  have htail : (originalGapUnits delta).tail=l := by rw [hl]; rfl
  have hdouble : Ordinal.omega0^(2 : Ordinal)*2=Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0^(2 : Ordinal) := by
    simpa only [one_add_one_eq_two,mul_one] using (mul_add_one (Ordinal.omega0^(2 : Ordinal)) (1 : Ordinal))
  constructor
  · rintro ⟨hcase,hodd⟩
    rcases hcase with ⟨hE,n,hn⟩ | ⟨hE,n,hn⟩
    · left
      refine ⟨hE,n,?_,hodd⟩
      apply original_quadratic_list_eval delta _ hd n
      rw [hl,←htail,hn]
    · right
      have he := original_quadratic_list_eval delta _ hd n (by rw [hl,←htail,hn])
      exact ⟨n,by simpa only [hE,←hdouble] using he,by simpa only [hE] using hodd⟩
  · intro hcase
    rcases hcase with ⟨hE,n,hshape,hodd⟩ | ⟨n,hshape,hodd⟩
    · have hlist := original_units_quadratic_shape (Ordinal.log Ordinal.omega0 delta) hE n
      rw [←hshape] at hlist
      exact ⟨Or.inl ⟨hE,n,by rw [hlist]; rfl⟩,hodd⟩
    · have hlist := original_units_double_quadratic n
      rw [←hshape] at hlist
      have hE : Ordinal.log Ordinal.omega0 delta=2 := by
        rw [hl] at hlist
        exact (List.cons.inj hlist).1
      exact ⟨Or.inr ⟨hE,n,by rw [hlist]; rfl⟩,by simpa only [hE] using hodd⟩

end LogicLineages.PermittedControl
