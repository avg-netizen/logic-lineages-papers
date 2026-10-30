module
public import LogicLineages.OrdinalComparison.PrincipalKernelWordDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:peakword (409–425): literal compiler order and prefix masses.
Statements are syntactic and do not identify a noncomputable evaluator as code. -/
def ActualPrincipalKernelWordPositions : Prop :=
  ∀ es : List ONote, ∀ c : Nat,
    principalKernelWord es c =
      (es.zipIdx.map fun p => (p.1, c + principalBlocksWeight (es.take p.2))).reverse

def ActualPrincipalKernelWordAppend : Prop :=
  ∀ es fs : List ONote, ∀ c : Nat,
    principalKernelWord (es ++ fs) c =
      principalKernelWord fs (c + principalBlocksWeight es) ++ principalKernelWord es c

end LogicLineages.OrdinalComparison.Targets
