module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open MixedSameRankResidue (encodeWeighted)
open MixedRankNamedResidueRow (RawArgs rawArgs)
open StatementChecks (fixed_mixedRankResidueCodeExact fixed_rankResidueLayoutAndChoices)

theorem commonLayoutPrimitive : Primrec commonLayoutCode := by
  have terms : Primrec (fun p : List RawArgs × RawArgs => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have allTerms := Primrec.list_flatMap (Primrec.id : Primrec (id : List RawArgs → List RawArgs)) terms.to₂
  exact fixed_rankResidueLayoutAndChoices.1.comp (fixed_mixedRankResidueCodeExact.1.comp allTerms)

private theorem literalOperands (rows : List SourceRow) :
    (rows.map encodeRow).flatMap (fun r => r.2.2) =
      (rows.flatMap (fun r => r.2.2)).map encodeWeighted := by
  induction rows with
  | nil => rfl
  | cons r tail ih =>
    change r.2.2.map encodeWeighted ++ (tail.map encodeRow).flatMap (fun t => t.2.2) =
      (r.2.2 ++ tail.flatMap (fun t => t.2.2)).map encodeWeighted
    rw [List.map_append,ih]

theorem commonLayoutLiteral (rows : List SourceRow) :
    commonLayoutCode (rows.map encodeRow) = commonLayout rows := by
  unfold commonLayoutCode commonLayout
  rw [literalOperands,fixed_mixedRankResidueCodeExact.2.2.1]

end LogicLineages.PermittedControl.SharedRankResidueRow
