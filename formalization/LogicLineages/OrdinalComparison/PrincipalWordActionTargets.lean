module
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:peakword (409–425): actual compiled word/control calibration.
All prefixes, states, and counts are literal; every dynamic domain is proved. -/
def ActualPrincipalWordRunCorrect : Prop :=
  ∀ es : List ONote, GenuinePrincipalBlocks es → ∀ c n : Nat,
    let t := c + principalBlocksWeight es + n
    let C := actualControlledCount (compensatedPrefixControl c)
      (principalBlockSum es + (n : Ordinal))
    actualPrincipalWordRun (principalKernelWord es c) t = ((Phi^[C]) t, C)

def ActualPrincipalWordInputsGenuine : Prop :=
  ∀ es : List ONote, GenuinePrincipalBlocks es → ∀ c n : Nat,
    actualPrincipalWordGenuine (principalKernelWord es c) (c + principalBlocksWeight es + n)

end LogicLineages.OrdinalComparison.Targets
