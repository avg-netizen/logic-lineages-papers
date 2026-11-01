module
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateSourceBridge
open Source.ForwardTranslation

/-- An actual hereditary-CNF expression with no exponent-zero monomial.
Zero itself is included; positive source heads will separately exclude it. -/
def RawWithoutFinitePart : ONote → Prop
  | .zero => True
  | .oadd e _ t => e≠0 ∧ RawWithoutFinitePart t

def scalarVariablesBelow {ι : Type} (index : ι → Nat) (d : Nat) : Scalar ι → Prop
  | .one => True
  | .var x => index x<d
  | .add a b => scalarVariablesBelow index d a ∧ scalarVariablesBelow index d b
  | .shift _ a => scalarVariablesBelow index d a

/-- Same literal scalar output and SAME variable indices as the already
checked source frontend. No fresh variable, head, reassociation or change of
the canonical source assignment is made. -/
def scalarToMultivariate {ι : Type} (index : ι → Nat) : Scalar ι → MultivariatePositiveExpr
  | .one => .constant 1
  | .var x => .input (index x)
  | .add a b => .add (scalarToMultivariate index a) (scalarToMultivariate index b)
  | .shift c a => .head (scalarHeadNote c) (scalarToMultivariate index a)

end LogicLineages.OrdinalComparison.MultivariateSourceBridge
