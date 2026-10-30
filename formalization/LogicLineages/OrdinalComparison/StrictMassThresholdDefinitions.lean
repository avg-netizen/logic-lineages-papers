module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal effective threshold recursion (7.6), using the executable notation
fundamental sequence solely to distinguish zero/successor/limit and obtain the
actual predecessor. Malformed notes still have a total raw algorithm; source
calibration is restricted to faithful normal forms. -/
def rawStrictMassThreshold : ONote → Nat
  | o =>
    match ONote.fundamentalSequence o, ONote.fundamentalSequence_has_prop o with
    | Sum.inl none, _ => 0
    | Sum.inl (some a), h =>
      have : a < o := by rw [ONote.lt_def, h.1]; exact Order.lt_succ _
      max 4 (max (1+Vendor.R1.treeWeight o)
        (max (2*(1+Vendor.R1.treeWeight a))
          (max (max 8 (1+Vendor.R1.treeWeight a))
            (if a=ONote.ofNat 2 then 0 else rawStrictMassThreshold a))))
    | Sum.inr _, _ => max 7 (2+Vendor.R1.treeWeight o)
  termination_by o => o

def actualStrictMassThreshold (eta : NONote) : Nat := rawStrictMassThreshold eta.1

end LogicLineages.OrdinalComparison
