module

public import LogicLineages.ModelsAlgebra.PGroups.ShiftGroupTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimeSquare
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem shift_coordinates : Targets.groupShiftCoordinates := by
  intro p x
  have hz : Finsupp.mapDomain Nat.succ x.2 0 = 0 :=
    Finsupp.mapDomain_notin_range x.2 0 (by rintro ⟨i, hi⟩; exact Nat.succ_ne_zero i hi)
  constructor
  · rfl
  constructor
  · simpa [shiftHom] using congrArg (fun z => primeSquareInclusion p x.1 + z) hz
  · intro i
    simp [shiftHom, Finsupp.mapDomain_apply Nat.succ_injective]

theorem shift_injective : Targets.groupShiftInjective := by
  intro p _ x y h
  apply Prod.ext
  · apply prime_square_inclusion_injective p
    simpa only [(shift_coordinates p x).2.1, (shift_coordinates p y).2.1] using
      congrArg (fun z : ShiftGroup p => z.2 0) h
  · apply Finsupp.ext
    intro i
    simpa only [(shift_coordinates p x).2.2 i, (shift_coordinates p y).2.2 i] using
      congrArg (fun z : ShiftGroup p => z.2 (i + 1)) h

theorem square_finsupp_socle_roots : Targets.groupSquareFinsuppSocleRoots := by
  classical
  intro p _ v hv
  let root : ZMod (p ^ 2) → ZMod (p ^ 2) := fun a =>
    if h0 : a = 0 then 0 else
      if ha : p • a = 0 then Classical.choose (prime_square_socle_roots p a ha) else 0
  have hzero : root 0 = 0 := by simp [root]
  have hroot (a : ZMod (p ^ 2)) (ha : p • a = 0) : p • root a = a := by
    by_cases h0 : a = 0
    · simp [root, h0]
    · simp only [root, dif_neg h0, dif_pos ha]
      exact Classical.choose_spec (prime_square_socle_roots p a ha)
  refine ⟨v.mapRange root hzero, ?_⟩
  apply Finsupp.ext
  intro i
  change p • root (v i) = v i
  apply hroot
  simpa using congrArg (fun w : ℕ →₀ ZMod (p ^ 2) => w i) hv

theorem shift_socle_roots : Targets.groupShiftSocleRoots := by
  intro p _ x hx
  have hv : p • x.2 = 0 := congrArg Prod.snd hx
  obtain ⟨w, hw⟩ := square_finsupp_socle_roots p x.2 hv
  have hu : primeSquareInclusion p x.1 ∈ multipleImage (ZMod (p ^ 2)) p := by
    rw [← prime_square_inclusion_range p]
    exact ⟨x.1, rfl⟩
  obtain ⟨r, hr⟩ := hu
  change p • r = primeSquareInclusion p x.1 at hr
  let tail : (ℕ →₀ ZMod (p ^ 2)) →+ (ℕ →₀ ZMod (p ^ 2)) :=
    Finsupp.mapDomain.addMonoidHom Nat.succ
  refine ⟨(0, Finsupp.single 0 r + tail w), ?_⟩
  apply Prod.ext
  · simp [shiftHom]
  · change p • (Finsupp.single 0 r + tail w) =
      Finsupp.single 0 (primeSquareInclusion p x.1) + tail x.2
    have hs : p • Finsupp.single 0 r = Finsupp.single 0 (primeSquareInclusion p x.1) := by
      simpa only [map_nsmul, Finsupp.singleAddHom_apply] using
        congrArg (Finsupp.singleAddHom 0 : ZMod (p ^ 2) →+ (ℕ →₀ ZMod (p ^ 2))) hr
    have ht : p • tail w = tail x.2 := by
      simpa only [map_nsmul] using congrArg tail hw
    rw [nsmul_add, hs, ht]

theorem shift_short_no_root : Targets.groupShiftShortNoRoot := by
  intro p _
  constructor
  · apply Prod.ext
    · exact ZModModule.char_nsmul_eq_zero p (1 : ZMod p)
    · simp
  · rintro ⟨y, hy⟩
    have hfirst : p • y.1 = 1 := congrArg Prod.fst hy
    rw [ZModModule.char_nsmul_eq_zero p y.1] at hfirst
    exact zero_ne_one hfirst

theorem shift_countable : Targets.groupShiftCountable := by
  intro p _
  infer_instance

theorem shift_infinite : Targets.groupShiftInfinite := by
  intro p _
  letI : Fact (1 < p ^ 2) := ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt (by decide)⟩
  infer_instance

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
