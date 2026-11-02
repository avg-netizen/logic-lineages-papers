module
public import LogicLineages.OrdinalComparison.GroundCarrierTransportStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Proof
open GroundClosing ScalarCarrierAccounting ActiveScalarAnnotation HeadFiniteSurplus

theorem exactAccountTransport : Targets.ExactAccountTransport := by
  intro k Γ Δ r q xs c hq
  induction hq with
  | free inactive =>
    exact .free (fun ha => inactive ((active_map r _).mp ha))
  | tracked => exact .tracked
  | add active left right ihl ihr =>
    exact .add ((active_map r _).mpr active) ihl ihr
  | @finite h t xs c n active hfinite tail ih =>
    rw [← surplus_map r h]
    exact .finite ((active_map r _).mpr active)
      ((exactUnitValue _ _ r.lift h).trans hfinite) ih
  | @nonfinite h t xs c label active hnonfinite exactHead tail ih =>
    rw [← surplus_map r h]
    exact .nonfinite label ((active_map r _).mpr active)
      (by
        have he := exactUnitValue _ _ r.lift h
        exact he.symm ▸ hnonfinite)
      (exactHead.trans (exactUnitValue _ _ r.lift h).symm) ih

end LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Proof
