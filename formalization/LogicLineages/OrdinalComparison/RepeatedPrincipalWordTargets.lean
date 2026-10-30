module
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 strict-mass proof718–745: the literal finite child-block word,
with descending actual retained masses and own-control finite exit. The word
compiler is executable; no computability of its semantic kernel evaluator is
claimed. Empty word and finite zero tail are included. -/
def ActualRepeatedPrincipalWordPositions : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ q c : Nat,
    let w := actualOrdinalNorm (Ordinal.omega0^eta.1.repr)
    principalKernelWord (List.replicate q eta.1) c =
      (List.range q).reverse.map (fun j => (eta.1, c+j*w))

def ActualRepeatedPrincipalWordRun : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ q c n : Nat,
    let theta := Ordinal.omega0^eta.1.repr
    let w := actualOrdinalNorm theta
    let initial := theta*(q : Ordinal)+(n : Ordinal)
    let g := compensatedPrefixControl c
    let C := actualControlledCount g initial
    let word := principalKernelWord (List.replicate q eta.1) c
    let t := c+q*w+n
    actualPrincipalWordRun word t =
      (c+actualOrdinalNorm (actualControlledStateAfter g initial C), C) ∧
      actualPrincipalWordGenuine word t

end LogicLineages.OrdinalComparison.Targets
