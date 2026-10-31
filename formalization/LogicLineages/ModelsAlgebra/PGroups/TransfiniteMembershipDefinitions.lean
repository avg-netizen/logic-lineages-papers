module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth

/-- Genuine normal-form conjunction with a QF condition, including rank zero. -/
noncomputable def piAndQF {n : ℕ} : Formula n → QF n → Formula n
  | .qf q, r => .qf (.and q r)
  | φ, r => piConjunction φ (piQF r)

/-- The finite-root equation uses the old free term and the fresh root variable. -/
def rootEquation (p r n : ℕ) (t : GroupTerm n) : QF (n+1) :=
  .equal (multipleTerm (p^r) (.var (Fin.natAdd n 0))) (renameTerm (Fin.castAdd 1) t)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
