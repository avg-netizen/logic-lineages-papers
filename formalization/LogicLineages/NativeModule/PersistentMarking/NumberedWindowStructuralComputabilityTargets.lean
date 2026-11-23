module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorComputabilityTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowArithmeticLeastClass
open NumberedWindowSimulationData NumberedWindowExternalComputability NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticClassAddress NumberedWindowExternalIDOperators

def TypedComputable (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (τ : Ty) (q : NTerm) : Prop :=
  ∃ hw : InWindow S K (finiteC Γ) τ q, ComputableClass S K Γ hk τ (classOf ⟨q,hw⟩)

def Environment (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (C : Spine.BoundContext) (values : NArgs) : Prop :=
  ∀ i τ, C i = some τ → τ ∈ K → TypedComputable S K Γ hk τ (substitute values 0 (.bound τ i))

def StructuralComputableSubstitution : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) C values τ q,
    InWindow S K C τ q → Environment S K Γ hk C values →
    TypedComputable S K Γ hk τ (substitute values 0 q)

def EveryAdmittedTermComputable : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) τ q,
    InWindow S K (finiteC Γ) τ q → TypedComputable S K Γ hk τ q

def EveryActualAddressInExternalI : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (x : Class S K (finiteC Γ) τ) i,
    ActualCodeAt S K Γ τ i x → Least (scalarStep S K) (encodeAddress ⟨Γ,τ,i⟩)

end LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityTargets
