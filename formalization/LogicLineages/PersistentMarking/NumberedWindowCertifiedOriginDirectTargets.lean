module
public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectTargets
open NumberedWindowDirectAlgorithm (Witness directLists)

/-- At least one side must pass the literal strict direct checker. An
unchanged side is the identical ordered source tape, not a chosen permutation. -/
def SideOutcomes (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (left right target : List Nat) : Prop :=
  (∃ left' wLeft,
    directLists scalar positive left left' wLeft = true ∧
    target.Perm (left' ++ right)) ∨
  (∃ right' wRight,
    directLists scalar positive right right' wRight = true ∧
    target.Perm (left ++ right')) ∨
  (∃ left' right' wLeft wRight,
    directLists scalar positive left left' wLeft = true ∧
    directLists scalar positive right right' wRight = true ∧
    target.Perm (left' ++ right'))

def ExactNumericOriginDirectCases : Prop :=
  ∀ (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
      (left right source target : List Nat) (w : Witness),
    source.Perm (left ++ right) →
    directLists scalar positive source target w = true →
    SideOutcomes scalar positive left right target

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectTargets
