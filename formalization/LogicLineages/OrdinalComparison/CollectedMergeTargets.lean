module
public import LogicLineages.OrdinalComparison.CollectedMergeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedTagInsertValue : Prop :=
  ∀ (rho : NONote) (A : CollectedPositiveNF) (a : Nat) (tags : CollectedPositiveTags) (x : Nat),
    actualCollectedTagsEval (collectedTagInsert rho A a tags) x =
      a * actualProfileHead rho (actualCollectedPositiveEval A x) + actualCollectedTagsEval tags x

def CollectedTagInsertValid : Prop :=
  ∀ (rho : NONote) (A : CollectedPositiveNF) (a : Nat) (tags : CollectedPositiveTags),
    Order.IsSuccLimit rho.1.repr → rho.1.repr < epsilonZero →
    CollectedPositiveValid A → collectedPositiveSupport A=true → CollectedTagsValid tags →
    CollectedTagsValid (collectedTagInsert rho A a tags)

def CollectedTagsMergeCorrect : Prop :=
  ∀ (left right : CollectedPositiveTags), CollectedTagsValid left → CollectedTagsValid right →
    CollectedTagsValid (collectedTagsMerge left right) ∧
    collectedTagsSupport (collectedTagsMerge left right)=
      (collectedTagsSupport left || collectedTagsSupport right) ∧
    ∀ x : Nat, actualCollectedTagsEval (collectedTagsMerge left right) x=
      actualCollectedTagsEval left x + actualCollectedTagsEval right x

def CollectedPositiveAddCorrect : Prop :=
  ∀ (A B : CollectedPositiveNF), CollectedPositiveValid A → CollectedPositiveValid B →
    CollectedPositiveValid (collectedPositiveAdd A B) ∧
    collectedPositiveSupport (collectedPositiveAdd A B)=
      (collectedPositiveSupport A || collectedPositiveSupport B) ∧
    ∀ x : Nat, actualCollectedPositiveEval (collectedPositiveAdd A B) x=
      actualCollectedPositiveEval A x + actualCollectedPositiveEval B x

end LogicLineages.OrdinalComparison.Targets
