module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerConnectedTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerConnected.Proof
open CotreeGrammarFlow CotreeGrammarConnected CotreePresburger CotreeGrammarRanks

theorem formulaWordExact : Targets.FormulaWordExact := by
  intro Q _ _ δ root w
  rw [CotreePresburger.StatementChecks.formulaExact]
  constructor
  · rintro ⟨c,rank,hs,ht,hb,hr⟩
    exact ⟨c, ⟨hs,ht,hb⟩,
      (CotreeGrammarRanks.StatementChecks.rankReachabilityExact Q δ root c).mp ⟨rank,hr⟩⟩
  · rintro ⟨c,hreal,hconn⟩
    rcases (CotreeGrammarRanks.StatementChecks.rankReachabilityExact Q δ root c).mpr hconn with
      ⟨rank,hr⟩
    exact ⟨c,rank,hreal.1,hreal.2.1,hreal.2.2,hr⟩

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerConnected.Proof
