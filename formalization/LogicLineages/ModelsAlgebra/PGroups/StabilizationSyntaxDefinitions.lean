module
public import LogicLineages.ModelsAlgebra.PGroups.StableStageDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
/-- Every p^N multiple is a p^(N+1) multiple, in the original group language. -/
def stabilizationRoot (p N:ℕ) : Formula (0+1) :=
  .disjEx {0} (fun _=>1) (fun _=>.qf
    (.equal (multipleTerm (p^N) (.var (Fin.castAdd 1 (Fin.natAdd 0 (0:Fin 1)))))
      (multipleTerm (p^(N+1)) (.var (Fin.natAdd (0+1) (0:Fin 1))))))
def stabilizationSentence (p N:ℕ) : Formula 0 :=
  .conjAll {0} (fun _=>1) (fun _=>stabilizationRoot p N)
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
