import LogicLineages.PersistentMarking.NativeTowerNumericCodeTargets
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof

namespace LogicLineages.PersistentMarking.NativeTowerNumericCodeApplicationProof
open Spine NativeReduction NativeIteratorStrictTargets NativeClosedApplication
open NativeSyntaxCountabilityTargets
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation NumberedWindowArithmeticTermCode
open NumberedWindowOrdinaryDomainProof NativeTowerNumericCodeTargets

theorem ordinaryAppRead (σ τ : Ty) (f a : Expr) (F A : NTerm)
    (hf : tr f = some F) (ha : tr a = some A) :
    tr (app σ τ f a) = some (appNode σ τ F A) := by
  simp [app, appNode, tr, trArgs, hf, ha]

theorem applicationCodeLiteral (σ τ : Ty) (F A : NTerm) :
    encodeTerm (appNode σ τ F A) = appCode σ τ (encodeTerm F) (encodeTerm A) := rfl

theorem readOrdinaryCode (q : Expr) (ordinary : Ordinary q) : ReadAt q (rawCode q) := by
  obtain ⟨Q,read⟩ := (termDomain q).mpr ordinary
  exact ⟨Q,read,by simp only [rawCode,read,Option.map_some,Option.getD_some]⟩

theorem combineReads (σ τ : Ty) (f a : Expr) (u v : Nat)
    (fRead : ReadAt f u) (aRead : ReadAt a v) : ReadAt (app σ τ f a) (appCode σ τ u v) := by
  obtain ⟨F,hF,kF⟩ := fRead
  obtain ⟨A,hA,kA⟩ := aRead
  refine ⟨appNode σ τ F A,ordinaryAppRead σ τ f a F A hF hA,?_⟩
  rw [applicationCodeLiteral,kF,kA]

theorem exact_ClosedNativeApplicationCode {S σ τ} (f : ClosedNativeTerm S (.arrow σ τ))
    (a : ClosedNativeTerm S σ) :
    nativeCode (applyClosed f a) = appCode σ τ (nativeCode f) (nativeCode a) := by
  obtain ⟨F,read,coded⟩ := combineReads σ τ f.val a.val (rawCode f.val) (rawCode a.val)
    (readOrdinaryCode f.val f.property.1.2.1) (readOrdinaryCode a.val a.property.1.2.1)
  change rawCode (app σ τ f.val a.val) = appCode σ τ (rawCode f.val) (rawCode a.val)
  simpa only [rawCode,read,Option.map_some,Option.getD_some] using coded

#print axioms ordinaryAppRead
#print axioms applicationCodeLiteral
#print axioms exact_ClosedNativeApplicationCode
end LogicLineages.PersistentMarking.NativeTowerNumericCodeApplicationProof
