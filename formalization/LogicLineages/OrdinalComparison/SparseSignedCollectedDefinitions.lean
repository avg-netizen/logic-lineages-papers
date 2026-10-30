module
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceDefinitions
public import LogicLineages.OrdinalComparison.CollectedPeakDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

noncomputable def actualCollectedTagPeakIndex (rho : NONote) (A : CollectedPositiveNF) (x : Nat) : Nat :=
  (Phi^[actualReplacementCount (actualCollectedTagInput rho A x)-1])
    (actualOrdinalNorm (actualCollectedTagInput rho A x))

def signedCollectedRowBound (row : SignedCollectedRow) (p q : Int) : Nat :=
  max 4 (2*(row.map (fun entry => entry.2.natAbs)).sum+p.natAbs+q.natAbs)

end LogicLineages.OrdinalComparison
