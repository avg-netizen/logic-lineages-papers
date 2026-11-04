module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets

/-- Proposed exact dynamic-mass cut/cocycle supporting the frozen full
uniform theorem. At the original input only the FIRST BUDGET must pay one
block. The lower child is evaluated at the genuine total entry K. -/
def BroadUnsignedBlockCut : Prop :=
  (∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    c+d ≤ Phi t ∧ e+d ≤ Phi t) ∧
  ∀ n c t : Nat, c+n+2 ≤ Phi t →
  let d := n+2
  let theta := Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)
  let E := sourceCount d (c+n+2) t
  let K := sourceValue d (c+n+2) t
  c+n+2 ≤ K ∧ c+actualOrdinalNorm theta ≤ K ∧
  (∀ i : Nat, 1 ≤ i → i ≤ E →
    sourceState d c t i = theta+sourceState d (c+n+2) t i) ∧
  E < sourceCount d c t ∧
  sourceState d c t E = actualSuffixKernelInitial theta c K ∧
  sourceCount d c t = actualSuffixKernelCount theta c K+E ∧
  sourceValue d c t = actualSuffixKernel theta c K

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets
