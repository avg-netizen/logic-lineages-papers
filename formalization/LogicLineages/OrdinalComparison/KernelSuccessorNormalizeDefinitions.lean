module
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Normalize one outer successor-exponent chain toward a lower principal.
The returned word runs inside-to-outside; the second component is a literal
computed genuine-input bound. A limit exponent stops, even if still above the
requested exponent. This is not the full comparison algorithm. -/
def rawKernelSuccessorNormalize : ONote → ONote → Nat → List (ONote × Nat) × Nat
  | eta, mu, c =>
    if ONote.cmp eta mu ≠ Ordering.gt then ([(eta,c)], c+1+Vendor.R1.treeWeight eta)
    else match ONote.fundamentalSequence eta, ONote.fundamentalSequence_has_prop eta with
    | Sum.inl none, _ => ([(eta,c)], c+1+Vendor.R1.treeWeight eta)
    | Sum.inl (some pred), h =>
      have : pred < eta := by rw [ONote.lt_def, h.1]; exact Order.lt_succ _
      let child := rawKernelSuccessorNormalize pred mu c
      ((eta,c+(1+Vendor.R1.treeWeight pred)) :: child.1,
        max (c+(1+Vendor.R1.treeWeight pred)+(1+Vendor.R1.treeWeight eta)) child.2)
    | Sum.inr _, _ => ([(eta,c)], c+1+Vendor.R1.treeWeight eta)
  termination_by eta mu c => eta

def kernelSuccessorNormalize (eta mu : NONote) (c : Nat) : List (ONote × Nat) × Nat :=
  rawKernelSuccessorNormalize eta.1 mu.1 c

end LogicLineages.OrdinalComparison
