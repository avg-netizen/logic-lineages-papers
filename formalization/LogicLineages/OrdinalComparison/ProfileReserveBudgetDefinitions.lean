module
public import LogicLineages.OrdinalComparison.ProfileHeadDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Actual outer leading monomial; zero is only the total raw zero convention. -/
noncomputable def actualProfileLeadingMonomial (rho : NONote) : Ordinal :=
  match rho.1 with
  | .zero => 0
  | .oadd e _ _ => Ordinal.omega0 ^ e.repr

/-- Executable norm of that leading monomial, with correspondence proved separately. -/
def profileLeadingWeight (rho : NONote) : Nat :=
  match rho.1 with
  | .zero => 0
  | .oadd e _ _ => 1 + Vendor.R1.treeWeight e

def profileReserveBlocks (word : List NONote) : Nat :=
  (word.map fun rho => Vendor.R1.treeWeight rho.1 + 1).sum

/-- Empty maximum is explicitly zero; the final compiler word is nonempty. -/
def profileReserveLeadingBound (word : List NONote) : Nat :=
  (word.map profileLeadingWeight).foldr max 0

end LogicLineages.OrdinalComparison
