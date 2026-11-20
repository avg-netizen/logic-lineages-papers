import LogicLineages.PersistentMarking.NativeClosedBetaTargets
import LogicLineages.PersistentMarking.NativeBetaProof
import LogicLineages.PersistentMarking.FreeVariableRawSupport
import LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof

namespace LogicLineages.PersistentMarking.NativeClosedBetaProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeClosedBetaTargets DecisionInventory DecisionSourceUniverse

theorem beta : ClosedNativeBeta := by
  intro S σ τ body hl a
  let start : ClosedNativeTerm S τ := applyClosed ⟨.lam σ body, hl⟩ a
  let values := Args.cons a.val .nil
  let result := substitute values 0 body
  have bodyTyped : Typed (EmptyContext.push σ) body τ := by
    have typed := hl.1.1.1
    cases typed with
    | lam typed => exact typed
  have bodyClosed : Closed body := hl.1.2.2
  have edge : ConfinedPair.Strict S start.val result :=
    NativeBetaProof.beta S σ τ body a.val bodyTyped hl.1.1.2 hl.1.2.1
      a.property.1.1 a.property.1.2.1
  obtain ⟨υ, sourceTyped, targetTyped, _, targetOrdinary⟩ := edge.1
  have sameType : υ = τ :=
    (SpineShiftProof.annotationExact _ _ _ sourceTyped.1).symm.trans
      (SpineShiftProof.annotationExact _ _ _ start.property.1.1.1)
  subst υ
  have targetClosed : Closed result := fun name =>
    FreeVariableRawSupport.substituteAbsent name values 0 body (bodyClosed name)
      (FreeVariableRawSupport.consAbsent (a.property.1.2.2 name) rfl)
  let K := auxiliarySupport body ++ auxiliarySupport a.val
  let H := heads body ++ heads a.val
  have bodyUniverse : Universe K [] H [] body :=
    ⟨fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h,
      fun n h => by rw [bodyClosed n] at h; cases h⟩
  have argUniverse : Universe K [] H [] a.val :=
    ⟨fun _ h => List.mem_append_right _ h, fun _ h => List.mem_append_right _ h,
      fun n h => by rw [a.property.1.2.2 n] at h; cases h⟩
  have resultUniverse : Universe K [] H [] result :=
    DecisionSourceSubstitutionProof.boundSubstitution K [] H [] [σ] values body τ bodyTyped
      (.cons a.property.1.1.1 .nil) bodyUniverse ⟨argUniverse, True.intro⟩
  have resultNative : Native result := by
    intro name arity bad
    rcases List.mem_append.mp (resultUniverse.2.1 _ bad) with hb | ha
    · exact hl.2 name arity hb
    · exact a.property.2 name arity ha
  refine ⟨⟨result, ⟨targetTyped, targetOrdinary, targetClosed⟩, resultNative⟩, ?_, ?_, ?_⟩
  · change result = substitute (.cons a.val .nil) 0 body
    rfl
  · change Reduction S (app σ τ (.lam σ body) a.val) result
    exact .primitive (.beta bodyTyped hl.1.1.2 hl.1.2.1 a.property.1.1 a.property.1.2.1)
  · change ConfinedPair.Strict S start.val result
    exact edge

end LogicLineages.PersistentMarking.NativeClosedBetaProof
