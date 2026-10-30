module

public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingDefinitions

@[expose] public section

/-! Actual Sigma_2 conjunction by pairing countable existential branches and
joining their finite witness blocks without capturing free variables. Matrices
are normalized at Pi_1 and conjoined by genuine branch flattening. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Free variables stay fixed; left witnesses occupy the first bound block. -/
def joinLeft (n m l : ℕ) : Fin (n + m) → Fin (n + (m + l)) :=
  Fin.addCases (Fin.castAdd (m + l)) (fun i => Fin.natAdd n (Fin.castAdd l i))

/-- Free variables stay fixed; right witnesses occupy the second bound block. -/
def joinRight (n m l : ℕ) : Fin (n + l) → Fin (n + (m + l)) :=
  Fin.addCases (Fin.castAdd (m + l)) (fun i => Fin.natAdd n (Fin.natAdd m i))

noncomputable def sigmaTwoConjunction {n : ℕ} : Formula n → Formula n → Formula n
  | .disjEx s m matrix, .disjEx t l other =>
      countableDisjEx (ι := s × t) (fun k => m k.1 + l k.2)
        (fun k => piConjunction
          (piOneNormalize (renameFormula (joinLeft n (m k.1) (l k.2)) (matrix k.1)))
          (piOneNormalize (renameFormula (joinRight n (m k.1) (l k.2)) (other k.2))))
  | φ, ψ => ordinaryConjunction φ ψ

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
