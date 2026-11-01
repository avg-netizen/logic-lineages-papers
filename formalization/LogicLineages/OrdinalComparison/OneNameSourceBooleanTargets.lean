module
public import LogicLineages.OrdinalComparison.OneNameSourceBooleanDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualOneNameSourceBooleanPrograms : Prop := Computable encodedOneNameSourceBooleanProgram ∧
  Computable₂ encodedOneNameSourceBooleanValue ∧ Computable encodedOneNameSourceBooleanClosures

def ActualOneNameSourceBooleanValue : Prop := ∀ formula : OneNameSourceBooleanExpr,∀ x : Nat,0<x →
  encodedOneNameSourceBooleanValue (oneNameSourceBooleanCompile formula) x=actualOneNameSourceBooleanValue formula x

/-- ENTIRE original07 final corollary, arbitrary actual original-T types and
output levels, one shared ground free name, literal default-policy assignment
and zero padding, pointwise equality/weak/WW-strict Boolean atoms and one
positive-coordinate existential OR universal quantifier. No supplied assignment,
compiler success, finite type bound, coordinate guard or scalar translation. -/
def FullActualOneNameSourceBooleanClosures : Prop := ActualOneNameSourceBooleanPrograms ∧
  ActualOneNameSourceBooleanValue ∧ ∀ formula : OneNameSourceBooleanExpr,
    let flags := encodedOneNameSourceBooleanClosures (oneNameSourceBooleanCompile formula)
    (flags.1=true ↔ ∃ x : Nat,0<x ∧ actualOneNameSourceBooleanValue formula x=true) ∧
    (flags.2=true ↔ ∀ x : Nat,0<x → actualOneNameSourceBooleanValue formula x=true)

end LogicLineages.OrdinalComparison.Targets
