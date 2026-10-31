module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealFinite RankedIdealCompletion
open RankedIdealContext.Proof

theorem reachLanguageInclusion : Targets.ReachLanguageInclusion := by
  intro M _ x y h t ht
  have hc := (RankedIdealFinite.StatementChecks.closureExact M {x} y).mp h
  clear h
  induction hc with
  | seed hs =>
      have he := Finset.mem_singleton.mp hs
      subst he
      exact ht
  | edge _ he ih => exact Run.epsilon ih he

theorem componentLanguageEquality : Targets.ComponentLanguageEquality := by
  intro M _ x y h t
  exact ⟨reachLanguageInclusion M x y h.1 t, reachLanguageInclusion M y x h.2 t⟩

theorem stateLanguageDownward : Targets.StateLanguageDownward := by
  intro M _ q s t hst ht
  obtain ⟨u, htu, hu⟩ := (RankedIdealCompletion.StatementChecks.runExact M t q).mp ht
  exact (RankedIdealCompletion.StatementChecks.runExact M s q).mpr
    ⟨u, embeddingTransitive hst htu, hu⟩

theorem nonlinearIdeal : Targets.NonlinearIdeal := by
  intro M _ q h
  obtain ⟨o, x, y, hx, hy, hqx, hqy, hqp⟩ := h
  constructor
  · obtain ⟨t, ht⟩ := (RankedIdealCompletion.StatementChecks.productiveExact M x).mp hx
    have hr : Run M t x := (RankedIdealCompletion.StatementChecks.runExact M t x).mpr
      ⟨t, embeddingReflexive t, ht⟩
    exact ⟨t, reachLanguageInclusion M x q hqx.2 t hr⟩
  · exact stateLanguageDownward M q
  · intro s t hs ht
    have hsx := reachLanguageInclusion M q x hqx.1 s hs
    have hty := reachLanguageInclusion M q y hqy.1 t ht
    have hn : Run M (.node o s t) (M.node o x y) := .node o hsx hty hx hy
    exact ⟨.node o s t, reachLanguageInclusion M _ q hqp.2 _ hn,
      .left o (embeddingReflexive s), .right o (embeddingReflexive t)⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents.Proof
