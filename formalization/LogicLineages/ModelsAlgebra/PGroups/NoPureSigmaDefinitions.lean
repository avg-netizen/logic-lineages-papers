module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
/-- A genuine Scott description at a strictly lower ORDINAL index, with
its ordinary syntax and full raw categoricity witness. This records the
stronger conclusion used to exclude exact pure Sigma, not a substitute
definition of exactness or a same-level opposite-polarity condition. -/
def LowerRawScottDescription (G:Type) [AddCommGroup G] (α:Ordinal.{0}) : Prop :=
  ∃β:Ordinal.{0},β<α ∧
    ((∃φ:Formula 0,Complexity .sigma β φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∨
      (∃φ:Formula 0,Complexity .pi β φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∨
        ∃d:DifferenceFormula 0,d.AtLevel β ∧ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d)
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
