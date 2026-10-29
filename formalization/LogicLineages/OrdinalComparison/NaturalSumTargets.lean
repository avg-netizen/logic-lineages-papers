module
public import LogicLineages.OrdinalComparison.Definitions

@[expose] public section

/-! Independent Cantor-coefficient specification of natural sum. The source
defines natural sum by collecting equal Cantor monomials; ordinary ordinal
addition is not a substitute for this statement. -/

namespace LogicLineages.OrdinalComparison

/-- Multiplicity of one exponent in the top-level Cantor-monomial list. -/
def cantorCoefficient : ONote → ONote → Nat
  | .zero, _ => 0
  | .oadd e c t, q => (if e = q then (c : Nat) else 0) + cantorCoefficient t q

namespace Targets

def NaturalSumCoefficients (add : NONote → NONote → NONote) : Prop :=
  ∀ (a b : NONote) (q : ONote),
    cantorCoefficient (add a b).1 q =
      cantorCoefficient a.1 q + cantorCoefficient b.1 q

def NaturalSumNormAdditive (add : NONote → NONote → NONote) : Prop :=
  ∀ a b : NONote,
    Vendor.R1.treeWeight (add a b).1 =
      Vendor.R1.treeWeight a.1 + Vendor.R1.treeWeight b.1

end Targets
end LogicLineages.OrdinalComparison
