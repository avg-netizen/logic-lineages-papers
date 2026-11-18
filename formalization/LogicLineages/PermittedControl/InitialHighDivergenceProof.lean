module
public import LogicLineages.PermittedControl.OriginalSensitiveSplitProof
public import LogicLineages.PermittedControl.InitialPassProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem initial_high_divergence (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hc : relativeProfile mu (Ordinal.log Ordinal.omega0 delta)<relativeProfile nu (Ordinal.log Ordinal.omega0 delta))
    (hx : ∃ x ∈ initialPeelingUnits delta, (2 : Ordinal) < x) :
    Targets.OrientedUnitDivergence f mu nu (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) A A' := by
  obtain ⟨P,a,r,hPpos,ha,ha2,hdiv,hr,heq⟩ := original_high_unit_split delta hd hdl hx
  have hap : 0 < a := (by norm_num : (0 : Ordinal) < 2).trans ha2
  have hb := original_split_certificate delta P a r hd hdl hPpos ha hap hdiv hr heq
  have hR := initial_radius_bounds mu nu delta
  have hs : Targets.SensitiveUnitSetup f B mu nu P a r A A' (initialPeelingRadius mu nu delta) t := by
    refine ⟨hf,hmu,hnu,hb.1,ha,hA,hA',hmud,hnud,hPpos,ha2.le,hdiv,hr,hb.2.2.2.1,
      hR.1,hR.2.1,hR.2.2.1,hb.2.1.trans hR.2.2.2,hb.2.2.1.trans hR.2.2.2,ht,?_,?_,hN,hN',?_⟩
    · rwa [← heq]
    · rwa [← heq]
    · rwa [← hb.2.2.2.2.1]
  obtain ⟨i,hi,hkeep,hkeep'⟩ := higherSensitiveUnit f B mu nu P a r A A' _ t hs ha2
  exact ⟨i,hi,hb.2.2.2.2.2.trans hkeep,hb.2.2.2.2.2.trans hkeep'⟩

end LogicLineages.PermittedControl
