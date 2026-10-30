module
public import LogicLineages.OrdinalComparison.PrincipalBlocksDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Executable right-to-left principal word, with literal retained prefix mass.
Only finite syntax and natural arithmetic are evaluated by this compiler. -/
def principalKernelWord : List ONote → Nat → List (ONote × Nat)
  | [], _ => []
  | e :: es, c => principalKernelWord es (c + (1 + Vendor.R1.treeWeight e)) ++ [(e, c)]

end LogicLineages.OrdinalComparison
