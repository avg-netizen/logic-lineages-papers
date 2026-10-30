module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunctionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDimensionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.SocleRootDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.AnnihilationDefinitions

@[expose] public section

/-! Literal bounded source descriptors. These assemble algebraic criteria;
no categoricity, cyclic decomposition, or Scott-sentence claim is made. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def purePiDifference {n : ℕ} (φ : Formula n) : DifferenceFormula n :=
  ⟨sigmaQF (.neg .falsum), φ⟩

noncomputable def boundedDescriptor (K : Type*) [AddCommGroup K] [Fintype K]
    (p : ℕ) [Fact p.Prime] (k N : ℕ) (a : Fin (k - 1) → ℕ) : DifferenceFormula 0 :=
  differenceTwoAll ([finiteImageIsomorphismFormula K (p ^ k),
    purePiDifference (infiniteMultipleImage (p ^ (k - 1))),
    purePiDifference (annihilationFormula (p ^ N) 0)] ++
      List.ofFn (fun i : Fin (k - 1) => ulmExactFormula p i.val 0 (a i)))

noncomputable def zeroLowerDescriptor (K : Type*) [AddCommGroup K] [Fintype K]
    (p k N : ℕ) : Formula 0 :=
  piTwoAll [piWrap (finiteImageTableFormula K (p ^ k) 0),
    boundedMultipleImage (p ^ k) (Fintype.card K),
    infiniteMultipleImage (p ^ (k - 1)), socleRootFormula p (k - 1) 0,
    annihilationFormula (p ^ N) 0]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
