module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningMarkProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningRenameProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening

def packedRename {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (rho : Renaming Gamma Delta) (p : Packed Symbol arity Gamma) : Packed Symbol arity Delta :=
  ⟨p.1,renameTerm p.2 rho⟩

theorem listRename {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : Arguments Symbol arity Gamma types) (rho : Renaming Gamma Delta) :
    argumentList (renameArguments args rho)=(argumentList args).map (packedRename rho) := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih =>
    cases args with
    | cons q rest => exact congrArg (List.cons (packedRename rho ⟨tau,q⟩)) (ih rest)

theorem rename {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    {q u : MarkedTerm Symbol arity Gamma tau} (h : Sharp Symbol arity Gamma q u) :
    ∀ Delta (rho : Renaming Gamma Delta),Sharp Symbol arity Delta (renameTerm q rho) (renameTerm u rho) := by
  induction h using Sharp.rec
    (motive_2 := fun Gamma types ss ts _ => ∀ Delta (rho : Renaming Gamma Delta),
      ArgumentsSharp Symbol arity Delta (renameArguments ss rho) (renameArguments ts rho))
    (motive_3 := fun Gamma f base types extras p _ => ∀ Delta (rho : Renaming Gamma Delta),
      ExtraSharp Symbol arity Delta f (renameArguments base rho) types (renameArguments extras rho) (packedRename rho p))
    (motive_4 := fun Gamma f base types extras targetTypes target _ => ∀ Delta (rho : Renaming Gamma Delta),
      ExtrasSharp Symbol arity Delta f (renameArguments base rho) types (renameArguments extras rho) (renameArguments target rho))
  case var v => intro Delta rho; exact .var (rho v)
  case lam s t hs ih => intro Delta rho; exact .lam _ _ (ih _ rho.lift)
  case ordinary f ss ts hs ih => intro Delta rho; exact .ordinary f _ _ (ih Delta rho)
  case marked f tau ss ts sourceTypes sourceExtras targetTypes targetExtras hb he ihb ihe =>
    intro Delta rho
    exact .marked f tau _ _ sourceTypes _ targetTypes _ (ihb Delta rho) (ihe Delta rho)
  case nil => intros; exact .nil
  case cons s t ss ts hs hr ihs ihr Delta rho =>
    exact .cons _ _ _ _ (ihs Delta rho) (ihr Delta rho)
  case existing f base types extras tau s t hm hs ih Delta rho =>
    apply ExtraSharp.existing f (renameArguments base rho) types (renameArguments extras rho)
      tau (renameTerm s rho) (renameTerm t rho)
    · rw [listRename]
      exact List.mem_map.mpr ⟨⟨tau,s⟩,hm,rfl⟩
    · exact ih Delta rho
  case whole f base types extras tau t hs ih Delta rho =>
    exact .whole f (renameArguments base rho) types (renameArguments extras rho) tau (renameTerm t rho) (ih Delta rho)
  case nil => intros; exact .nil _ _ _ _
  case cons f base sourceTypes sourceExtras tau types t ts he hr ihe ihr =>
    intro Delta rho
    exact .cons f (renameArguments base rho) sourceTypes (renameArguments sourceExtras rho) tau types
      (renameTerm t rho) (renameArguments ts rho) (ihe Delta rho) (ihr Delta rho)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningRenameProof
