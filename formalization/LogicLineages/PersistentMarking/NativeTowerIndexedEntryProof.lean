import LogicLineages.PersistentMarking.NativeTowerIndexedEntryTargets
import LogicLineages.PersistentMarking.NativeTowerBetaPathProof
import LogicLineages.PersistentMarking.NativeOrdinalExponentialChecks
import LogicLineages.PersistentMarking.NativeIteratorChecks
import LogicLineages.PersistentMarking.NativeIteratorStrictChecks

namespace LogicLineages.PersistentMarking.NativeTowerIndexedEntryProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets
open NativeOrdinalExponentialTargets NativeIteratorTargets NativeTowerWitnessPrefixTargets
open NativeTowerWitnessPrefixProof NativeTowerWitnessFamilyProof NativeTowerBetaPathTargets NativeTowerBetaPathProof
open NativeTowerIndexedEntryTargets

private theorem applicationTyping (h : Typed EmptyContext (app σ τ f a) τ) :
    Typed EmptyContext f (.arrow σ τ) ∧ Typed EmptyContext a σ := by
  cases h with
  | head argsTyped =>
    cases argsTyped with
    | cons hf tail =>
      cases tail with
      | cons ha _ => exact ⟨hf,ha⟩

/-- Invert the actual original application, not an externally asserted
closure or a code-level surrogate for the two original children. -/
theorem closedAppChildren (h : ClosedNative S (app σ τ f a) τ) :
    ClosedNative S f (.arrow σ τ) ∧ ClosedNative S a σ := by
  have typing := applicationTyping h.1.1.1
  have valid : Valid S f ∧ Valid S a := ⟨h.1.1.2.2.1,h.1.1.2.2.2.1⟩
  have ord : Ordinary f ∧ Ordinary a := ⟨h.1.2.1.1,h.1.2.1.2.1⟩
  have free (n : Name) : freeOccurs n f = false ∧ freeOccurs n a = false := by
    simpa [app,freeOccurs,freeOccursArgs,Bool.or_eq_false_iff] using h.1.2.2 n
  have fn : Native f := by
    intro name arity hit
    apply h.2 name arity
    simp [app,DecisionInventory.heads,DecisionInventory.headsArgs,hit]
  have an : Native a := by
    intro name arity hit
    apply h.2 name arity
    simp [app,DecisionInventory.heads,DecisionInventory.headsArgs,hit]
  exact ⟨⟨⟨⟨typing.1,valid.1⟩,ord.1,fun n => (free n).1⟩,fn⟩,
    ⟨⟨⟨typing.2,valid.2⟩,ord.2,fun n => (free n).2⟩,an⟩⟩

private theorem consumedMapClosed (S : Signature) (l : Nat)
    (before : ClosedNativeTerm S indexType) (named : before.val = beforeFix l) :
    ClosedNative S (innerMap l) endo := by
  have whole : ClosedNative S (app indexType indexType (app endo endo ordinalFix (innerMap l)) t0)
      indexType := by
    rw [← show before.val = app indexType indexType (app endo endo ordinalFix (innerMap l)) t0 from named]
    exact before.property
  exact (closedAppChildren (closedAppChildren whole).1).2

private theorem prependBeta {S : Signature} {n m : Nat}
    {before middle after : ClosedNativeTerm S indexType}
    (head : StrictBetaPath S indexType n before middle) (tail : StrictRun S m middle after) :
    StrictRun S (m+n) before after := by
  revert tail
  induction head with
  | nil q => intro tail; exact tail
  | cons one _ ih =>
    intro tail
    exact .cons one.reduction one.strict (ih tail)

theorem exact_NativeTowerIndexedEntry : ExactNativeTowerIndexedEntry := by
  intro S l
  obtain ⟨before,beforeValue,initial⟩ := exact_PrintedTowerBetaPath S l
  let mapping : ClosedNativeTerm S endo := ⟨innerMap l,consumedMapClosed S l before beforeValue⟩
  let base := closedT0 S
  let seed := applyClosed ⟨ordinalSuccessor,NativeOrdinalBasisProof.successorClosed S⟩ base
  let omegaValue := nativeOmega S
  obtain ⟨p,q,r,hp,hq,hr,fix1,fix2,sfix1,sfix2⟩ :=
    NativeOrdinalExponentialChecks.exact_NativeOrdinalFixBeta S mapping base
  obtain ⟨start,atIndex,atMap,finish,hs,hi,hf,he,si,sm,su⟩ :=
    NativeIteratorStrictChecks.exact_IteratorNativeStrictChain S .base
      omegaValue.val mapping.val seed.val omegaValue.property mapping.property seed.property
  obtain ⟨ri,rm,ru⟩ := NativeIteratorChecks.exact_IteratorNativeBetaTransport S .base
    omegaValue.val mapping.val seed.val omegaValue.property mapping.property seed.property
  have pSame : p = before := Subtype.ext (hp.trans beforeValue.symm)
  have rSame : r = start := Subtype.ext (hr.trans hs.symm)
  have e₁ : Reduction S start.val atIndex.val := by rw [hs,hi]; exact ri
  have e₂ : Reduction S atIndex.val atMap.val := by rw [hi,hf]; exact rm
  have e₃ : Reduction S atMap.val finish.val := by rw [hf,he]; exact ru
  have it : StrictRun S 3 start finish :=
    .cons e₁ si (.cons e₂ sm (.cons e₃ su (.nil finish)))
  rw [← rSame] at it
  have suffix : StrictRun S 5 p finish := .cons fix1 sfix1 (.cons fix2 sfix2 it)
  rw [pSame] at suffix
  have run := prependBeta initial suffix
  have length : 5+(l+1) = l+6 := by omega
  rw [length] at run
  exact ⟨mapping,seed,finish,rfl,rfl,he,run⟩

#print axioms closedAppChildren
#print axioms exact_NativeTowerIndexedEntry
end LogicLineages.PersistentMarking.NativeTowerIndexedEntryProof
