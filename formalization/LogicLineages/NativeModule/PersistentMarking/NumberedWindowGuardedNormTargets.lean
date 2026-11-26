module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperatorTargets
public import LogicLineages.PersistentMarking.OrdinalGuardedStageRankTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowGuardedNormTargets
open Spine NumberedWindowExternalIDOperators NumberedWindowArithmeticAllContextTargets

abbrev ordinalStage :=
  NumberedWindowExternalIDStages.stage ((· < ·) : Ordinal.{0} → Ordinal.{0} → Prop) Ordinal.lt_wf

def AddressBelow (S : Signature) (K : List Ty) (target source : Nat) : Prop :=
  AddressPositive S K source target

def ActualScalarStageRank : Prop :=
  ∀ S K n (a : Ordinal.{0}),
    (ordinalStage (scalarStep S K) a n ↔
      AdmittedAddress S K n ∧ ∃ h : Acc (AddressBelow S K) n, h.rank ≤ a) ∧
    (ordinalStage (taggedStep S K) a (tagScalar n) ↔
      AdmittedAddress S K n ∧ ∃ h : Acc (AddressBelow S K) n, h.rank ≤ a)

def ActualScalarOrdinalNorm : Prop :=
  ∀ S K n (h : Acc (AddressBelow S K) n), AdmittedAddress S K n →
    IsLeast {a : Ordinal.{0} | ordinalStage (scalarStep S K) a n} h.rank ∧
    IsLeast {a : Ordinal.{0} | ordinalStage (taggedStep S K) a (tagScalar n)} h.rank

def IsolatedAdmittedAddressStarts : Prop :=
  ∀ S K n, AdmittedAddress S K n → (∀ t, ¬ AddressBelow S K t n) →
    ordinalStage (scalarStep S K) 0 n ∧ ordinalStage (taggedStep S K) 0 (tagScalar n)

end LogicLineages.PersistentMarking.NumberedWindowGuardedNormTargets
