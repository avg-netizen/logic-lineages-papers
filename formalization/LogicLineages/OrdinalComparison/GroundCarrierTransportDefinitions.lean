module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport

/-- Actual source substitution lifted below the retained tracked head binder.
Old functional names map to old typed names, never to tracked here. Ground
names may become literal source zero; its assignment is ordinal one. -/
def close {Γ Δ : List Ty} {σ τ : Ty} (r : GroundClosing.GroundMap Γ Δ)
    (t : OriginalTerm (σ :: Γ) τ) : OriginalTerm (σ :: Δ) τ :=
  t.substitute (GroundClosing.GroundMap.source r.lift)
end LogicLineages.OrdinalComparison.Source.GroundCarrierTransport
