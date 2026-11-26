module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl

/-- Literal source retained CNF block; ordinary addition and multiplication. -/
noncomputable def thickBlock (P a : Ordinal.{0}) (q : Nat) : Ordinal :=
  P + Ordinal.omega0^a * (q : Ordinal)

/-- Source large-growth, moving-residue modulus and control-tail threshold.
Dynamic prefix costs are paid separately by actual starting-state norm. -/
def thickBlockTail (R B : Nat) : Nat :=
  max (100*(R+2)^4) (max (initialLcm (R+1)) B)

end LogicLineages.PermittedControl
