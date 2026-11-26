module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDStages

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorTargets
open Spine NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticDirectCodeTargets
open NumberedWindowExternalIDOperators NumberedWindowExternalIDStages
universe u

def ExactDisjointOperatorTags : Prop :=
  Function.Injective tagScalar ∧ Function.Injective tagMultiset ∧
    ∀ a b, tagScalar a ≠ tagMultiset b

def ExactTaggedClauseProjection : Prop :=
  ∀ S K P n,
    (taggedStep S K P (tagScalar n) ↔ scalarStep S K (fun x => P (tagScalar x)) n) ∧
    (taggedStep S K P (tagMultiset n) ↔ multisetStep S K (fun x => P (tagMultiset x)) n)

def ActualOperatorsMonotone : Prop :=
  ∀ S K, IsMonotone (scalarStep S K) ∧
    IsMonotone (multisetStep S K) ∧ IsMonotone (taggedStep S K)

def ActualLeastPredicatesFixed : Prop :=
  ∀ S K n,
    (scalarStep S K (Least (scalarStep S K)) n ↔ Least (scalarStep S K) n) ∧
    (multisetStep S K (Least (multisetStep S K)) n ↔ Least (multisetStep S K) n) ∧
    (taggedStep S K (Least (taggedStep S K)) n ↔ Least (taggedStep S K) n)

def ActualLeastTagProjection : Prop :=
  ∀ S K n,
    (Least (taggedStep S K) (tagScalar n) ↔ Least (scalarStep S K) n) ∧
    (Least (taggedStep S K) (tagMultiset n) ↔ Least (multisetStep S K) n)

/-- Exact mathematical semantics of the two guarded predicates.
This equivalence does not discharge any particular accessibility. -/
def ActualGuardedAccessibilitySemantics : Prop :=
  ∀ S K n,
    (Least (scalarStep S K) n ↔
      AdmittedAddress S K n ∧ Acc (fun target source => AddressPositive S K source target) n) ∧
    (Least (multisetStep S K) n ↔
      AdmittedAddressListCode S K n ∧ Acc (fun target source => DirectAtCode S K source target) n)

def ActualStageTagProjection : Prop :=
  ∀ {ι : Type u} (r : ι → ι → Prop) (wf : WellFounded r) S K a n,
    (stage r wf (taggedStep S K) a (tagScalar n) ↔ stage r wf (scalarStep S K) a n) ∧
    (stage r wf (taggedStep S K) a (tagMultiset n) ↔ stage r wf (multisetStep S K) a n)

def StageStartsAtOperatorEmpty : Prop :=
  ∀ {ι : Type u} (r : ι → ι → Prop) (wf : WellFounded r) (F : Operator) a,
    (∀ b, ¬ r b a) → ∀ n, stage r wf F a n ↔ F (fun _ => False) n

end LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorTargets
