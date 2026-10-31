module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem independent_pruefer_infinite_socles : Targets.independentPrueferInfiniteSocles := by
  intro p _ ι G _ _ e he
  classical
  have hP := genuine_pruefer_model p
  have hsum : ∀ n : ℕ, n ≠ 0 → ∀ x : DirectSum ι (fun _ => PrueferModel p),
      ∃ y, n • y = x := by
    intro n hn x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0,by simp⟩
    | of i x =>
      obtain ⟨y,hy⟩ := hP.2.1 n hn x
      exact ⟨DirectSum.of _ i y,by rw [← map_nsmul,hy]⟩
    | add x y hx hy =>
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := hy
      exact ⟨a+b,by rw [nsmul_add,ha,hb]⟩
  have hrange : SubgroupDivisible e.range := by
    intro n hn x
    obtain ⟨a,ha⟩ := x.property
    obtain ⟨b,hb⟩ := hsum n hn a
    refine ⟨⟨e b,⟨b,rfl⟩⟩,Subtype.ext ?_⟩
    change n • e b = (x:G)
    rw [← map_nsmul,hb,ha]
  have hle := (actual_divisible_part G).2 e.range hrange
  obtain ⟨t,ht,hpt⟩ := hP.2.2
  let a : ι → G := fun i => e (DirectSum.of _ i t)
  have hainj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have h := congrArg (fun z : DirectSum ι (fun _ => PrueferModel p) => z i) (he hij)
    rw [DirectSum.of_eq_same,DirectSum.of_eq_of_ne _ _ _ hne] at h
    exact ht h
  have hamem : ∀ i, a i ∈ divisiblePart G := fun i => hle ⟨_,rfl⟩
  have hpa : ∀ i, p • a i = 0 := by
    intro i
    change p • e (DirectSum.of _ i t) = 0
    rw [← map_nsmul,← map_nsmul,hpt,map_zero,map_zero]
  have hinf (S : AddSubgroup G) (hS : ∀ i, a i ∈ S) : Infinite (pSocle p S) := by
    let j : ι → pSocle p S := fun i => ⟨a i,hS i,hpa i⟩
    apply Infinite.of_injective j
    intro i k h
    apply hainj
    exact congrArg (fun z : pSocle p S => (z:G)) h
  refine ⟨hrange,hle,hinf _ hamem,?_⟩
  intro α
  have hcut := p_divisible_in_every_stage G p (divisiblePart G)
    ((actual_divisible_part G).1 p (Fact.out : p.Prime).ne_zero) α
  exact hinf _ (fun i => hcut (hamem i))

end LogicLineages.ModelsAlgebra.PGroups
