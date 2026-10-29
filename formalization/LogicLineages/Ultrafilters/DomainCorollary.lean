module
public import LogicLineages.Ultrafilters.DomainCorollaryTargets
public import LogicLineages.Ultrafilters.DomainSubfield
public import LogicLineages.Ultrafilters.UltrapowerProperness
@[expose] public section
namespace LogicLineages.Ultrafilters

theorem domain_corollary : Targets.DomainCorollary := by
  intro p hp
  obtain ⟨K, hK, hc⟩ := domain_subfield p hp
  obtain ⟨f, hf, hs, hd, hpos, hsmall, hout, hproper⟩ :=
    universal_ultrapower_properness p hp
  refine ⟨K, hK, hc, ?_, ?_⟩
  · simpa only [hK] using hproper
  · intro hconv
    have hzero : (0 : RealUltrapower p) ∈ (K : Set _) := hc 0
    have hone : (1 : RealUltrapower p) ∈ (K : Set _) := hc 1
    have hmem := hconv.out' hzero hone
      (show classOf p f ∈ Set.Icc (0 : RealUltrapower p) 1 from
        ⟨hpos.le, (hsmall 1 (by norm_num)).le⟩)
    rw [hK] at hmem
    exact hout hmem

end LogicLineages.Ultrafilters
