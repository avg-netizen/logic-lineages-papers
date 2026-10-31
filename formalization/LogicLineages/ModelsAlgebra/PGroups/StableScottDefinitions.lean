module
public import LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.StabilizationSyntaxDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTableDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
noncomputable def stableGroupTable (p:ℕ) [Fact p.Prime] (N:ℕ)
    (entries:Fin N→Option ℕ) (socleEntry:Option ℕ) : Formula 0 :=
  piTwoAll ([primarySentence p,stabilizationSentence p N,socleRankEntry p N 0 socleEntry] ++
    List.ofFn (fun i:Fin N=>ulmRankEntry p i.val 0 (entries i)))
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
