module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletionTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion.Proof
open RankedParse ProfileAutomatonEncoding

theorem productiveExact : Targets.ProductiveExact := by
  intro M _ q
  constructor
  · intro h
    obtain ⟨t, _, ht⟩ := (ProfileLanguageEmpty.StatementChecks.reachableHeightExact M _ q).mp h
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    exact ProfileLanguageEmpty.Proof.allRunsReachable M t

theorem runExact : Targets.RunExact := by
  intro M _ t q
  constructor
  · intro h
    induction h with
    | atom => exact ⟨.atom, .atom, rfl⟩
    | node o _ _ _ _ ihl ihr =>
        obtain ⟨l, hl, rfl⟩ := ihl
        obtain ⟨r, hr, rfl⟩ := ihr
        exact ⟨.node o l r, .couple o hl hr, rfl⟩
    | epsilon _ he ih =>
        obtain ⟨u, hu, hrun⟩ := ih
        obtain ⟨_, o, z, hz, he | he⟩ := he
        · obtain ⟨v, hv⟩ := (productiveExact M z).mp hz
          exact ⟨.node o u v, .left o hu, by simp only [machineRun, hrun, hv, he]⟩
        · obtain ⟨v, hv⟩ := (productiveExact M z).mp hz
          exact ⟨.node o v u, .right o hu, by simp only [machineRun, hrun, hv, he]⟩
  · rintro ⟨u, h, rfl⟩
    induction h with
    | atom => exact .atom
    | @left s l r o h ih =>
        exact .epsilon ih ⟨(productiveExact M _).mpr ⟨l, rfl⟩,
          o, machineRun M r, (productiveExact M _).mpr ⟨r, rfl⟩, Or.inl rfl⟩
    | @right s l r o h ih =>
        exact .epsilon ih ⟨(productiveExact M _).mpr ⟨r, rfl⟩,
          o, machineRun M l, (productiveExact M _).mpr ⟨l, rfl⟩, Or.inr rfl⟩
    | @couple s₁ s₂ t₁ t₂ o h₁ h₂ ih₁ ih₂ =>
        exact .node o ih₁ ih₂ ((productiveExact M _).mpr ⟨t₁, rfl⟩)
          ((productiveExact M _).mpr ⟨t₂, rfl⟩)

theorem acceptanceExact : Targets.AcceptanceExact := by
  intro M _ t
  constructor
  · rintro ⟨q, hr, ha⟩
    obtain ⟨u, hu, he⟩ := (runExact M t q).mp hr
    exact ⟨u, hu, he ▸ ha⟩
  · rintro ⟨u, hu, ha⟩
    exact ⟨machineRun M u, (runExact M t _).mpr ⟨u, hu, rfl⟩, ha⟩

theorem runProductive : Targets.RunProductive := by
  intro M _ t q hr
  obtain ⟨u, _, hu⟩ := (runExact M t q).mp hr
  exact (productiveExact M q).mpr ⟨u, hu⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion.Proof
