module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeProof
public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableProof
open PredictionTapeRuntimeComputable PredictionTapeRuntimeComputableTargets PredictionTapeRuntime

private theorem pr_all {α β : Type} [Primcodable α] [Primcodable β]
    (l : α → List β) (p : α → β → Bool) (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec (fun a => (l a).all (p a)) := by
  have h := Primrec.list_foldr hl (Primrec.const true)
    (Primrec.to₂ (Primrec.and.comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)))
  apply h.of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih => simp [List.all_cons, ih]

theorem exactFiniteTest : ExactFiniteTest := by
  intro code n fuel
  simp only [allHalting,List.all_eq_true,Option.isSome_iff_exists]
  constructor
  · intro h xs hx
    exact h xs ((PredictionCommonFuelProof.booleanHistoriesExact n xs).2 hx)
  · intro h xs hx
    exact h xs ((PredictionCommonFuelProof.booleanHistoriesExact n xs).1 hx)

theorem effectiveRuntimeSearch : EffectiveRuntimeSearch := by
  have hs : Primrec (fun z : Nat × Nat × List Bool => PredictionFiniteAlphabet.simulate z.1 z.2.1 z.2.2) :=
    PredictionFiniteAlphabetProof.effectiveBoundedSimulation
  have harg : Primrec (fun z : (Nat × Nat × Nat) × List Bool => (z.1.1,z.1.2.2,z.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  have hone : Primrec (fun z : (Nat × Nat × Nat) × List Bool =>
      (PredictionFiniteAlphabet.simulate z.1.1 z.1.2.2 z.2).isSome) :=
    Primrec.option_isSome.comp (Primrec.comp
      (f := fun z : Nat × Nat × List Bool => PredictionFiniteAlphabet.simulate z.1 z.2.1 z.2.2)
      (g := fun z : (Nat × Nat × Nat) × List Bool => (z.1.1,z.1.2.2,z.2)) hs harg)
  have htest : Primrec (fun z : Nat × Nat × Nat => allHalting z.1 z.2.1 z.2.2) :=
    pr_all _ _ (PredictionCommonFuelProof.booleanHistoriesPrimrec.comp (Primrec.fst.comp Primrec.snd)) hone.to₂
  refine ⟨htest,?_⟩
  have hinput : Computable (fun z : (Nat × Nat) × Nat => (z.1.1,z.1.2,z.2)) :=
    (Computable.fst.comp Computable.fst).pair ((Computable.snd.comp Computable.fst).pair Computable.snd)
  exact Partrec.rfind (htest.to_comp.comp hinput).partrec.to₂

theorem exactPartialRuntime : ExactPartialRuntime := by
  intro code n t
  constructor
  · intro ht
    have hh := Nat.mem_rfind.mp ht
    have hall := (exactFiniteTest code n t).1 (Part.mem_some_iff.mp hh.1).symm
    have hdom : ∀ xs : List Bool, xs.length=n → ∃ fuel, Successful code xs fuel :=
      fun xs hx => ⟨t,hall xs hx⟩
    obtain ⟨s,hs⟩ := (worstTimeDomain code n).2 hdom
    have hst : s ≤ t := ((worstTimeThreshold code n s).1 hs t).1 hall
    have hts : t ≤ s := by
      by_contra hn
      have hf : allHalting code n s = false := (Part.mem_some_iff.mp (hh.2 (by omega))).symm
      have ha : allHalting code n s = true := (exactFiniteTest code n s).2
        (((worstTimeThreshold code n s).1 hs s).2 le_rfl)
      rw [ha] at hf
      contradiction
    have : s=t := by omega
    simpa [this] using hs
  · intro ht
    apply Nat.mem_rfind.mpr
    constructor
    · have hh := (exactFiniteTest code n t).2 (((worstTimeThreshold code n t).1 ht t).2 le_rfl)
      simp [hh]
    · intro s hs
      have hn : allHalting code n s ≠ true := by
        intro hh
        have := ((worstTimeThreshold code n t).1 ht s).1 ((exactFiniteTest code n s).1 hh)
        omega
      cases hv : allHalting code n s <;> simp_all

theorem totalProgramComputableRuntime : TotalProgramComputableRuntime := by
  intro code hp
  choose time htime using totalBinaryWorstExists code hp
  have hpart : Partrec (partialWorstTime code) := effectiveRuntimeSearch.2.comp (Computable.const code) Computable.id
  refine ⟨time,hpart.of_eq_tot (fun n => (exactPartialRuntime code n (time n)).2 (htime n)),htime⟩

end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableProof
