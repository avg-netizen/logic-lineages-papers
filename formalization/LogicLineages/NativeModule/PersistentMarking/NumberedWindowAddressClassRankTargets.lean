module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowCanonicalAddressMapTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowGuardedNormTargets
public import LogicLineages.PersistentMarking.OrdinalRankMapEqualityTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowAddressClassRankTargets
open Spine NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowCanonicalAddressMap NumberedWindowGuardedNormTargets NumberedWindowExternalIDOperators

def ClassBelow (S : Signature) (K Γ : List Ty) (τ : Ty)
    (target source : Class S K (finiteC Γ) τ) : Prop :=
  RS S K (finiteC Γ) τ source target

def ActualAddressClassRankEquality : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ),
    ∀ (classAcc : Acc (ClassBelow S K Γ τ) q)
      (addressAcc : Acc (AddressBelow S K) (classAddress hk q)),
      classAcc.rank = addressAcc.rank

def ActualClassStageNormAtAddress : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ),
    ∃ classAcc : Acc (ClassBelow S K Γ τ) q,
      IsLeast {a : Ordinal.{0} | ordinalStage (scalarStep S K) a (classAddress hk q)} classAcc.rank ∧
      IsLeast {a : Ordinal.{0} | ordinalStage (taggedStep S K) a (tagScalar (classAddress hk q))} classAcc.rank

end LogicLineages.PersistentMarking.NumberedWindowAddressClassRankTargets
