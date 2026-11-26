import LogicLineages.PersistentMarking.NumberedWindowExternalApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalScalarClassProof
open Spine NumberedWindowSimulationData NumberedWindowExternalIDOperators
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticLeastClass
open NumberedWindowPathWitnessTargets NumberedWindowArithmeticAllContextTargets
open NumberedWindowExternalApplicationTargets NumberedWindowPathWitnessChecks

private theorem address_injective {a b : ClassAddress} (h : encodeAddress a = encodeAddress b) :
    a = b := by
  have he := congrArg decodeAddress h
  simpa only [NumberedWindowArithmeticClassAddressProof.round, Option.some.injEq] using he

private theorem codedTarget {S K Γ τ i n} (hk : DecisionSourceUniverse.Closed K)
    {q : Class S K (finiteC Γ) τ} (hi : ActualCodeAt S K Γ τ i q)
    (step : AddressPositive S K (encodeAddress ⟨Γ,τ,i⟩) n) :
    ∃ (r : Class S K (finiteC Γ) τ) (j : Nat), encodeAddress ⟨Γ,τ,j⟩ = n ∧
      ActualCodeAt S K Γ τ j r ∧ RS S K (finiteC Γ) τ q r := by
  obtain ⟨Δ,υ,k,j,x,y,hsrc,hdst,hx,hy,hpath⟩ := step
  have eq := address_injective hsrc
  cases eq
  have eqClass := (exact_ActualClassCodeFibers S K Γ τ hk).2.1 x q i hx hi
  subst x
  exact ⟨y,j,hdst,hy,hpath⟩

private theorem toCode {S K Γ τ} (hk : DecisionSourceUniverse.Closed K)
    {q : Class S K (finiteC Γ) τ} (h : Acc (fun r q => RS S K (finiteC Γ) τ q r) q) :
    ∀ i, ActualCodeAt S K Γ τ i q →
      Acc (fun d s => AddressPositive S K s d) (encodeAddress ⟨Γ,τ,i⟩) := by
  induction h with
  | intro q _ ih =>
    intro i hi
    constructor
    intro n step
    obtain ⟨r,j,rfl,hj,path⟩ := codedTarget hk hi step
    exact ih r path j hj

private theorem fromCode {S K Γ τ n} (hk : DecisionSourceUniverse.Closed K)
    (h : Acc (fun d s => AddressPositive S K s d) n) :
    ∀ (q : Class S K (finiteC Γ) τ) i, ActualCodeAt S K Γ τ i q →
      encodeAddress ⟨Γ,τ,i⟩ = n → Acc (fun r q => RS S K (finiteC Γ) τ q r) q := by
  induction h with
  | intro n _ ih =>
    intro q i hi hn
    constructor
    intro r path
    obtain ⟨j,hj⟩ := (exact_ActualClassCodeFibers S K Γ τ hk).1 r
    exact ih (encodeAddress ⟨Γ,τ,j⟩) ⟨Γ,τ,i,j,q,r,hn,rfl,hi,hj,path⟩ r j hj rfl

theorem scalarClass : ScalarClassAccessibility := by
  intro S K Γ τ hk q i hi
  rw [(NumberedWindowExternalIDOperatorChecks.exact_ActualGuardedAccessibilitySemantics
    S K (encodeAddress ⟨Γ,τ,i⟩)).1]
  constructor
  · intro h
    exact fromCode hk h.2 q i hi rfl
  · intro h
    exact ⟨⟨Γ,τ,i,q,rfl,hi⟩,toCode hk h i hi⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalScalarClassProof
