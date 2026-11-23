module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticLeastClassTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationPrimaryProof
public import Init.Data.List.MinMax

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassSpecProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryClassList NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassTargets

theorem literalInj {Q R : NTerm} (h : encodeTerm Q = encodeTerm R) : Q = R := by
  have hq := NumberedWindowArithmeticTermCodeComplete.termRound Q
  rw [h] at hq
  exact Option.some.inj (hq.symm.trans (NumberedWindowArithmeticTermCodeComplete.termRound R))

theorem specification : LeastCodeSpecification := by
  intro S K Γ τ Q hk hQ
  have member (X : NTerm) : X ∈ finiteClassList S K Γ τ Q ↔
      Primary S K (finiteC Γ) τ Q X :=
    NumberedWindowPrimaryClassListChecks.exact_FinitePrimaryClassList S K Γ τ Q X hk hQ
  have hMem : encodeTerm Q ∈ (finiteClassList S K Γ τ Q).map encodeTerm :=
    List.mem_map_of_mem ((member Q).mpr (.refl hQ.1))
  have existsMin : ∃ c, leastCode S K Γ τ Q = some c :=
    Option.isSome_iff_exists.mp (List.isSome_min?_of_mem hMem)
  obtain ⟨c,hc⟩ := existsMin
  have hMinEq : ((finiteClassList S K Γ τ Q).map encodeTerm).min? = some c := hc
  obtain ⟨hm,hl⟩ := List.min?_eq_some_iff.mp hMinEq
  obtain ⟨R,hRL,hEnc⟩ := List.mem_map.mp hm
  have hPR := (member R).mp hRL
  have hR := (NumberedWindowPreservationPrimaryProof.primary hk hPR).mp hQ
  have hDecode := NumberedWindowArithmeticTermCodeComplete.termRound R
  rw [hEnc] at hDecode
  have hRep : representative S K Γ τ Q = some R := by
    simp only [representative,hc,Option.bind_some,hDecode]
  refine ⟨c,R,hc,hRep,hEnc,hR,hPR,?_,?_⟩
  · intro X hp
    exact hl _ (List.mem_map_of_mem ((member X).mpr hp))
  · intro X _ he
    exact literalInj (he.trans hEnc.symm)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassSpecProof
