module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationPredicateProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem startFor_computable : Computable₂ Code.startFor := by
  have hmax : Primrec (fun xs : List Nat => xs.foldr max 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.succ.to_comp.comp (hmax.to_comp.comp
    (Computable.list_cons.comp Computable.fst (matrixVariables_computable.comp Computable.snd)))

theorem names_computable : Computable₂ Code.names :=
  ExpandedGraphCodeProof.allocated_computable.comp startFor_computable
    (forest_computable.comp Computable.snd)

theorem bound_computable : Computable₂ Code.bound :=
  Computable.list_cons.comp Computable.fst names_computable

theorem graphFormula_computable : Computable₂ Code.graphFormula :=
  SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp
    (ExpandedGraphCodeProof.graph_computable.comp startFor_computable
      (forest_computable.comp Computable.snd))
    (predicate_computable.comp startFor_computable Computable.snd)

theorem program_computable : Computable₂ Code.program :=
  bound_computable.pair (WholeBoundInitializationCodeProof.actualFormulaProgram.comp
    bound_computable graphFormula_computable)

theorem programs : HFreeGraphNormalizationTargets.Programs :=
  ⟨termVariables_computable,matrixVariables_computable,forest_computable,predicate_computable,
    names_computable,graphFormula_computable,program_computable⟩
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
