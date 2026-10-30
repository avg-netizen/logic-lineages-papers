module
public import LogicLineages.OrdinalComparison.ControlDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- An explicit residue witness using the literal variable-seed F1, not an
uncomputed CRT choice. Its common-residue property is proved separately. -/
def fastControlResidue (m : Nat) : Nat := fastControl 1 m % m

end LogicLineages.OrdinalComparison
