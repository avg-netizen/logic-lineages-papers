module
public import LogicLineages.OrdinalComparison.ProfileReserveBudgetDefinitions
public import LogicLineages.OrdinalComparison.ProfileCompilerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Executable coefficient-one outer leading note; proof fields certify only
normal syntax and are erased, never an assumed semantic comparison. -/
def profileLeadingNote : NONote → NONote
  | ⟨.zero, _⟩ => 0
  | ⟨.oadd e _ _, ho⟩ => ⟨ONote.oadd e 1 0, by
      letI : ONote.NF e := ho.fst
      infer_instance⟩

/-- Existing NONote max is implemented by its structural comparator.
The empty list deliberately returns omega. -/
def profilePrincipalDominator (word : List NONote) : NONote :=
  (word.map profileLeadingNote).foldr max profileOmegaNote

/-- Source direct-growth threshold, entirely on faithful finite syntax. -/
def profileDirectThreshold (L : NONote) (E : FixedLimitPositiveExpr) : Nat :=
  max (fixedLimitProfileThreshold E)
    (max (profileReserveBlocks (profileBoundWord E) *
      Vendor.R1.treeWeight (profilePrincipalDominator (profileBoundWord E)).1)
      (max 4 (Vendor.R1.treeWeight L.1)))

end LogicLineages.OrdinalComparison
