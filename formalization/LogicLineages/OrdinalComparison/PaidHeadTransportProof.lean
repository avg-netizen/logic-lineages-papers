module
public import LogicLineages.OrdinalComparison.PaidHeadTransportAlgebraProof
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeProof
public import LogicLineages.OrdinalComparison.ActualUnaryRayAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.PaidHeadTransport.Proof
open Arithmetic ArithmeticCode FormulaConstruction ForwardTranslation OriginalDomain

theorem actualPaidGraph : Targets.ActualPaidGraph := by
  intro Γ K
  obtain ⟨u,a,c,q,hconst,hs,hbuild,hcodes,hgraph⟩ := GraphCode.Proof.actualEffectiveWholeGraph Γ K
  obtain ⟨u',a',c',v,hconst',hv,hhead,hscalar,hray⟩ := ActualUnaryRay.Proof.actualSourceRay Γ K
  have hu : u'=u := Option.some.inj (hconst'.1.symm.trans hconst.1)
  subst u'
  have ha : a'=a := Option.some.inj (hconst'.2.1.symm.trans hconst.2.1)
  subst a'
  refine ⟨u,hconst.1,?_⟩
  intro δ paid μ hpaid t y
  have hxi : paidHead paid = shiftedHead a δ := by
    rw [hhead μ] at hpaid
    rw [paidHead,hpaid,exactOmegaFiniteTail a.evaluate.1.repr (normalRepresentationSound a.evaluate) δ]
    rfl
  refine ⟨graph (UnitElimination.realize q) a c δ t y,(hgraph δ t y).1,?_⟩
  intro ν
  rw [hxi]
  exact (hgraph δ t y).2 ν
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.PaidHeadTransport.Proof
