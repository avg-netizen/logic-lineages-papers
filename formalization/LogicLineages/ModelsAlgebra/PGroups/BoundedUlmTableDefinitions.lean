module

public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlmDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDimensionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunctionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.AnnihilationDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- `none` specifies genuine infinite dimension, `some m` the finite cardinal m. -/
noncomputable def ulmRankEntry (p : ℕ) [Fact p.Prime] (j n : ℕ) : Option ℕ → Formula n
  | none => infiniteUlmFormula p j n
  | some m => piConjunction (piWrap (ulmLowerFormula p j n m)) (ulmUpperFormula p j n m)

/-- Literal bounded invariant table, not a categoricity oracle. -/
noncomputable def boundedUlmTable (p : ℕ) [Fact p.Prime] (N : ℕ)
    (entries : Fin N → Option ℕ) : Formula 0 :=
  piTwoAll (annihilationFormula (p ^ N) 0 ::
    List.ofFn (fun i : Fin N => ulmRankEntry p i.val 0 (entries i)))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
