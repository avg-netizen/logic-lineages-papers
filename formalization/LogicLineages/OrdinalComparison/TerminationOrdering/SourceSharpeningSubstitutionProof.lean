module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningRenameProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningSubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening

def packedSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : MarkedSubstitution Symbol arity Gamma Delta) (p : Packed Symbol arity Gamma) : Packed Symbol arity Delta :=
  ⟨p.1,substituteTerm p.2 theta⟩

theorem listSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : Arguments Symbol arity Gamma types) (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    argumentList (substituteArguments args theta)=(argumentList args).map (packedSubstitute theta) := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih =>
    cases args with
    | cons q rest => exact congrArg (List.cons (packedSubstitute theta ⟨tau,q⟩)) (ih rest)

theorem relatedSubstitution : SourceSharpeningTargets.RelatedSubstitution := by
  intro Symbol arity Gamma Delta tau q u theta eta h H
  induction h using Sharp.rec
    (motive_2 := fun Gamma types ss ts _ => ∀ Delta
      (theta eta : MarkedSubstitution Symbol arity Gamma Delta),
      (∀ sigma (v : Variable Gamma sigma),Sharp Symbol arity Delta (theta v) (eta v)) →
      ArgumentsSharp Symbol arity Delta (substituteArguments ss theta) (substituteArguments ts eta))
    (motive_3 := fun Gamma f base types extras p _ => ∀ Delta
      (theta eta : MarkedSubstitution Symbol arity Gamma Delta),
      (∀ sigma (v : Variable Gamma sigma),Sharp Symbol arity Delta (theta v) (eta v)) →
      ExtraSharp Symbol arity Delta f (substituteArguments base theta) types
        (substituteArguments extras theta) (packedSubstitute eta p))
    (motive_4 := fun Gamma f base types extras targetTypes target _ => ∀ Delta
      (theta eta : MarkedSubstitution Symbol arity Gamma Delta),
      (∀ sigma (v : Variable Gamma sigma),Sharp Symbol arity Delta (theta v) (eta v)) →
      ExtrasSharp Symbol arity Delta f (substituteArguments base theta) types
        (substituteArguments extras theta) (substituteArguments target eta))
    generalizing Delta
  case var v => exact H _ v
  case lam s t hs ih =>
    apply Sharp.lam
    apply ih _ (liftSubstitution theta) (liftSubstitution eta)
    intro sigma v
    cases v with
    | here => exact .var .here
    | there v => exact SourceSharpeningRenameProof.rename (H _ v) _ (Renaming.weaken Delta _)
  case ordinary f ss ts hs ih => exact .ordinary f _ _ (ih Delta theta eta H)
  case marked f tau ss ts sourceTypes sourceExtras targetTypes targetExtras hb he ihb ihe =>
    exact .marked f tau _ _ sourceTypes _ targetTypes _ (ihb Delta theta eta H) (ihe Delta theta eta H)
  case nil => intros; exact .nil
  case cons s t ss ts hs hr ihs ihr Delta theta eta H =>
    exact .cons _ _ _ _ (ihs Delta theta eta H) (ihr Delta theta eta H)
  case existing f base types extras tau s t hm hs ih Delta theta eta H =>
    apply ExtraSharp.existing f (substituteArguments base theta) types (substituteArguments extras theta)
      tau (substituteTerm s theta) (substituteTerm t eta)
    · rw [listSubstitute]
      exact List.mem_map.mpr ⟨⟨tau,s⟩,hm,rfl⟩
    · exact ih Delta theta eta H
  case whole f base types extras tau t hs ih Delta theta eta H =>
    exact .whole f (substituteArguments base theta) types (substituteArguments extras theta) tau
      (substituteTerm t eta) (ih Delta theta eta H)
  case nil => intros; exact .nil _ _ _ _
  case cons =>
    intros
    rename_i Gamma f base sourceTypes sourceExtras tau types t ts he hr ihe ihr Delta theta eta H
    exact .cons f (substituteArguments base theta) sourceTypes (substituteArguments sourceExtras theta) tau types
      (substituteTerm t eta) (substituteArguments ts eta) (ihe Delta theta eta H) (ihr Delta theta eta H)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningSubstitutionProof
