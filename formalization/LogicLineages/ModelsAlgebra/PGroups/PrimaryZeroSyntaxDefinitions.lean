module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteMembershipDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth

noncomputable def primaryWitness (p : ℕ) : Formula 1 :=
  countableDisjEx (fun _ : ℕ => 0)
    (fun k => .qf (.equal (multipleTerm (p^k) (.var 0)) .zero))

noncomputable def primarySentence (p : ℕ) : Formula 0 :=
  countableConjAll (fun _ : Unit => 1) (fun _ => primaryWitness p)
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
