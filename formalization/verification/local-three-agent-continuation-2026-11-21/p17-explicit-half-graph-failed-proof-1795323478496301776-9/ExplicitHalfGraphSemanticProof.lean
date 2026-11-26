module
public import LogicLineages.PermittedControl.ExplicitHalfGraphTargets
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ExplicitHalfGraph
open PreparedProjection FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

theorem naturalGraph : NaturalGraph := by
  intro full half ν
  simp only [graph,NormalForm.Formula.eval,NormalForm.Atom.eval,NormalForm.rowValue,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NormalForm.Summand.term,
    OrdinalComparison.LayeredComparison.SnyatkovCompletion.Term.value,one_mul,add_zero,zero_add]
  omega

theorem actualHalfExtension : ActualHalfExtension := by
  intro f B chosen rank full half ρ distinct
  let value := f (ρ rank)
  have actual : LowerOperandActual f ρ (.ordinary rank (.iterate 1)) value := by
    simp [LowerOperandActual,ClosedOrdinaryValueDomain,FieldValue,value]
  have read : lowerOperandRead f ρ (.ordinary rank (.iterate 1)) = some (some value) :=
    (preparedTiedProjection.1 f ρ (.ordinary rank (.iterate 1)) value).mpr actual
  refine ⟨value,rfl,actual,read,?_⟩
  intro ν readFull
  obtain ⟨k,even⟩ := selected_even f B chosen (ρ rank)
  have double : 2 * (value / 2) = value := by
    change 2 * (f (ρ rank) / 2) = f (ρ rank)
    omega
  have exactAt (h : Nat) : (graph full half).eval (Function.update ν half h) ↔ h = value / 2 := by
    rw [naturalGraph,Function.update_self,Function.update_of_ne distinct,readFull]
    omega
  refine ⟨exactAt,⟨value/2,(exactAt _).mpr rfl,fun h hGraph => (exactAt h).mp hGraph⟩,?_⟩
  intro h name outside
  exact Function.update_of_ne outside h ν

end LogicLineages.PermittedControl.ExplicitHalfGraph
