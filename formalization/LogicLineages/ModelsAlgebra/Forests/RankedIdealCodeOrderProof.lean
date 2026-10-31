module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrderTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutableStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder.Proof
open RankedIdealRegularCode CotreePresburgerBoolean
 theorem stateOrderExact : Targets.StateOrderExact := by intro C x y; rfl
 theorem inclusionExact : Targets.InclusionExact := by
  intro C D
  letI := stateOrder C
  letI := stateOrder D
  rw [inclusion, CotreePresburgerExecutable.StatementChecks.sourceInclusionExact C.machine D.machine]
  constructor
  · intro h T hT
    exact (CotreePresburgerBoolean.StatementChecks.sourceLanguageExact D.machine T).mp
      (h T ((CotreePresburgerBoolean.StatementChecks.sourceLanguageExact C.machine T).mpr hT))
  · intro h T hT
    exact (CotreePresburgerBoolean.StatementChecks.sourceLanguageExact D.machine T).mpr
      (h T ((CotreePresburgerBoolean.StatementChecks.sourceLanguageExact C.machine T).mp hT))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder.Proof
