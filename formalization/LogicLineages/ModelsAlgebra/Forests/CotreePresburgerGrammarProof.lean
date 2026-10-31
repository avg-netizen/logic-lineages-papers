module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammarTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammar.Proof
open CotreeGrammarFlow CotreeGrammarConnected CotreeGrammarForest CotreeGrammarInitialForest

theorem formulaGrammarExact : Targets.FormulaGrammarExact := by
  intro Q _ _ δ root w
  rw [CotreePresburgerConnected.StatementChecks.formulaWordExact]
  constructor
  · rintro ⟨c,hreal,hconn⟩
    have hF := CotreeGrammarInitialForest.StatementChecks.initialForestExact Q δ c hreal.1
    obtain ⟨v,hv,hperm⟩ := CotreeGrammarReconstruct.StatementChecks.wordReconstruction
      Q δ root w (initialForest δ c) (by simpa only [hF] using hreal)
      (by simpa only [hF] using hconn)
    exact ⟨v, (CotreeGrammar.StatementChecks.grammarLanguageExact Q δ root v).mpr hv, hperm⟩
  · rintro ⟨v,hv,hperm⟩
    obtain ⟨c,hreal,hconn⟩ := CotreeGrammarConnected.StatementChecks.connectedFlowNecessary
      Q δ root v hv
    refine ⟨c, ⟨hreal.1, ?_, hreal.2.2⟩, hconn⟩
    intro B
    rw [hreal.2.1 B, hperm.count_eq B]

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammar.Proof
