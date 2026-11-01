module
public import LogicLineages.OrdinalComparison.OneInputBooleanDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualOneInputBooleanPrograms : Prop := Computable₂ encodedOneInputBooleanValue ∧
  Computable encodedOneInputBooleanTail ∧ Computable encodedOneInputBooleanClosures

def ActualOneInputBooleanValue : Prop := ∀ formula : OneInputBooleanExpr,oneInputBooleanValid formula →
  ∀ x : Nat,encodedOneInputBooleanValue (oneInputBooleanCompile formula) x=actualOneInputBooleanValue formula x

def ActualOneInputBooleanTail : Prop := ∀ formula : OneInputBooleanExpr,oneInputBooleanValid formula →
  let N := encodedOneInputBooleanTail (oneInputBooleanCompile formula)
  1≤N ∧ ∀ x : Nat,N≤x → actualOneInputBooleanValue formula x=actualOneInputBooleanValue formula N

/-- ENTIRE original paper07 cor:boolean, literal finite Boolean formulas with
equality/weak/strict P1 atoms, one shared positive natural input, genuine total
uniform Computable decisions for BOTH closures, and actual original-source
prefix evaluation before any auxiliary kernel's raised domain. -/
def FullActualOneInputBooleanClosures : Prop := ActualOneInputBooleanPrograms ∧ ActualOneInputBooleanValue ∧
  ActualOneInputBooleanTail ∧ ∀ formula : OneInputBooleanExpr,oneInputBooleanValid formula →
    let flags := encodedOneInputBooleanClosures (oneInputBooleanCompile formula)
    (flags.1=true ↔ ∃ x : Nat,0<x ∧ actualOneInputBooleanValue formula x=true) ∧
    (flags.2=true ↔ ∀ x : Nat,0<x → actualOneInputBooleanValue formula x=true)

end LogicLineages.OrdinalComparison.Targets
