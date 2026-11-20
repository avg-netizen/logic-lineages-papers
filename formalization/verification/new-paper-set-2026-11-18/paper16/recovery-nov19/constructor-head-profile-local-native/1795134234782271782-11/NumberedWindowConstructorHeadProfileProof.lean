import LogicLineages.PersistentMarking.NumberedWindowConstructorHeadProfileTargets
import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryProof

import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceComplete
import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceArgsTrace

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorHeadProfileProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowArithmeticLeastClass
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorHeadProfileTargets
open NumberedWindowPreservationGuardProof NumberedWindowNumberedDomainProof
open NumberedWindowSimulationData NumberedWindowExternalComputability
open NumberedWindowArithmeticLeastClassChecks NumberedWindowArithmeticClassAddress

theorem bagExact : AddressBagExact := fun _ _ => ⟨Quotient.exact, Quotient.sound⟩

private theorem profile {S K C τ q r} (hk : DecisionSourceUniverse.Closed K)
    (h : Primary S K C τ q r) :
    ∀ Γ, C = finiteC Γ → InWindow S K C τ q → headProfile S K Γ q = headProfile S K Γ r := by
  induction h using Primary.rec (motive_2 := fun C types qs rs _ =>
    ∀ Γ, C = finiteC Γ → BaseTyped C qs types → ArgsGuard S K qs →
      qs.toList.map (slot S K Γ) = rs.toList.map (slot S K Γ)) with
  | refl => intros; rfl
  | symm h ih =>
    intro Γ e hw
    exact (ih Γ e ((NumberedWindowPreservationPrimaryProof.primary hk h).mpr hw)).symm
  | trans h _ ih jh =>
    intro Γ e hw
    exact (ih Γ e hw).trans (jh Γ e ((NumberedWindowPreservationPrimaryProof.primary hk h).mp hw))
  | ordinary _ _ heq e _ _ hp =>
    intro Γ _ _
    obtain ⟨n,hf,hg⟩ := heq
    simp only [headProfile,hf,hg,e]
    rw [(bagExact _ _).mpr (hp.map (slot _ _ Γ))]
  | numbered _ _ heq _ _ _ hp =>
    intro Γ _ _
    obtain ⟨n,hf,hg⟩ := heq
    simp only [headProfile,hf,hg]
    rw [(bagExact _ _).mpr (hp.map (slot _ _ Γ))]
  | lam | appFunction | appArgument => intros; rfl
  | ordinaryArguments _ ih =>
    intro Γ e hw
    obtain ⟨hb,_,hg⟩ := ordinaryParts hw
    simp only [headProfile,ih Γ e hb hg]
  | numberedBase _ _ ih =>
    intro Γ e hw
    obtain ⟨hb,_,_,hg,_⟩ := parts hw
    simp only [headProfile,ih Γ e hb hg]
  | numberedExtras _ original ih =>
    intro Γ e hw
    obtain ⟨_,_,_,_,hg⟩ := parts hw
    obtain ⟨trace⟩ := NumberedWindowPrimarySequenceComplete.args original
    simp only [headProfile,ih Γ e (NumberedWindowPrimarySequenceArgsTrace.argsFirst trace) hg]
  | nil => intros; rfl
  | cons h _ _ ih =>
    rintro Γ rfl ht hg
    cases ht with
    | cons hq htail =>
      obtain ⟨g,gs⟩ := consParts hg
      have hw := And.intro hq g
      have hr := (NumberedWindowPreservationPrimaryProof.primary hk h).mp hw
      have eq := NumberedWindowConstructorArgumentAddressChecks.exact_PrimaryArgumentAddress _ _ Γ _ _ _ hk hw hr h
      simp only [NArgs.toList,List.map_cons,eq,ih Γ rfl htail gs]

theorem primary : PrimaryHeadProfile := fun _ _ Γ _ _ _ hk hw hp => profile hk hp Γ rfl hw

private theorem atAddress {S K Γ σ τ i j} (hk : DecisionSourceUniverse.Closed K)
    (Q : WindowCarrier S K (finiteC Γ) σ) (R : WindowCarrier S K (finiteC Γ) τ)
    (hq : leastCode S K Γ σ Q.val = some i) (hr : leastCode S K Γ τ R.val = some j)
    (e : encodeAddress ⟨Γ,σ,i⟩ = encodeAddress ⟨Γ,τ,j⟩) :
    ComputableClass S K Γ hk σ (classOf Q) ↔ ComputableClass S K Γ hk τ (classOf R) := by
  have ee := congrArg decodeAddress e
  simp only [NumberedWindowArithmeticClassAddressProof.round, Option.some.injEq, ClassAddress.mk.injEq] at ee
  obtain ⟨_,rfl,rfl⟩ := ee
  have hc := (exact_LeastCodeReflectsActualQuotient S K Γ _ Q R hk).mp (hq.trans hr.symm)
  rw [hc]

theorem sameSlot : SameSlotComputable := by
  intro S K Γ hk q r hq hr e
  obtain ⟨i,_,hi,_⟩ := exact_LeastCodeSpecification S K Γ q.type q hk hq
  obtain ⟨j,_,hj,_⟩ := exact_LeastCodeSpecification S K Γ r.type r hk hr
  simp only [slot,hi,hj,Option.map_some,Option.some.injEq] at e
  have hc := atAddress hk ⟨q,hq⟩ ⟨r,hr⟩ hi hj e
  exact ⟨fun ⟨_,h⟩ => ⟨hr,hc.mp h⟩, fun ⟨_,h⟩ => ⟨hq,hc.mpr h⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowConstructorHeadProfileProof
