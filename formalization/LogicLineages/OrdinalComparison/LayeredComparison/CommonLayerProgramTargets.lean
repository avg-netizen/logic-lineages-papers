module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Targets
/-- Exact all-code equation of the ACTUAL nested compiler: finite instruction
children strictly reduce layer count and their assembly equals literal BASE
formula output. No semantic-equivalence surrogate or supplied recursion law. -/
def ExactFiniteCallEquation:Prop:=
  (∀a b,b∈children a→measure b<measure a)∧
  ∀a,recursiveCode a=assemble a ((children a).map recursiveCode)
/-- Actual numeric child/assembly interfaces required by the proved uniform
finite graph algorithm. They must be constructed, not supplied as premises. -/
def NumericalInterfaces:Prop:=Computable children∧Computable₂ assemble∧Computable measure
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Targets
