import LogicLineages.PersistentMarking.NativeTowerNumericCodeApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryQuoteProof
import LogicLineages.PersistentMarking.NumberedWindowRealizationTypingProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

namespace LogicLineages.PersistentMarking.NativeTowerNumericCodeProof
open Spine NativeReduction NativeIndexedCarrierTargets NativeOrdinalBasisTargets
open NativeOrdinalArithmeticTargets NativeTowerExtractorTargets
open NativeTowerExtractorGeneralTargets NativeTowerExtractorGeneralProof
open NativeTowerWitnessPrefixTargets NativeTowerWitnessPrefixProof
open NativeTowerWitnessFamilyTargets NativeTowerWitnessFamilyProof
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticFields NativeSyntaxCountabilityTargets
open NativeTowerNumericCodeTargets NativeTowerNumericCodeApplicationProof

theorem exact_PrintedLowerCode (S : Signature) (l : Nat) :
    ∀ (q : Expr) (k : Nat), ReadAt q k → ReadAt (printedLower l q) (lowerCode l k) := by
  induction l with
  | zero => intro q k h; exact h
  | succ l ih =>
    intro q k h
    have arg := readOrdinaryCode (extractor l) (extractorClosed S l).1.2.1
    exact ih _ _ (combineReads (ty (l+2)) (ty (l+2)) q (extractor l) k _ h arg)

private theorem zeroRead (S : Signature) : ReadAt t0 zeroCode :=
  combineReads indexType indexType nativeNB omegaCarrier _ _
    (readOrdinaryCode nativeNB (nativeNb S).property.1.2.1)
    (readOrdinaryCode omegaCarrier (nativeOmega S).property.1.2.1)

theorem towerRead (S : Signature) (n : Nat) : ReadAt (towerTerm n) (towerCode n) := by
  have nb := readOrdinaryCode nativeNB (nativeNb S).property.1.2.1
  cases n with
  | zero => exact zeroRead S
  | succ n =>
    cases n with
    | zero => exact combineReads indexType indexType nativeNB t0 _ _ nb (zeroRead S)
    | succ l =>
      rw [exact_PrintedNativeTowerSyntax.2.2.2.2 l]
      have first := readOrdinaryCode (extractor l) (extractorClosed S l).1.2.1
      have head := exact_PrintedLowerCode S l _ _ first
      exact combineReads indexType indexType _ t0 _ _
        (combineReads endo endo _ nativeNB _ _ head nb) (zeroRead S)

private theorem towerOuter (n : Nat) :
    towerTerm n = app indexType indexType (finalHead n) (finalOperand n) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ l => exact exact_PrintedNativeTowerSyntax.2.2.2.2 l

private theorem appCodePositive (σ τ : Ty) (f a : Nat) : 0 < appCode σ τ f a := by
  unfold appCode encodeNode
  exact Nat.succ_pos _

theorem codePositive (n : Nat) : 0 < towerCode n := by
  cases n with
  | zero =>
    simpa only [towerCode,zeroCode] using
      (appCodePositive indexType indexType (rawCode nativeNB) (rawCode omegaCarrier))
  | succ n =>
    cases n with
    | zero =>
      simpa only [towerCode] using
        (appCodePositive indexType indexType (rawCode nativeNB) zeroCode)
    | succ l =>
      simpa only [towerCode] using
        (appCodePositive indexType indexType
          (appCode endo endo (lowerCode l (rawCode (extractor l))) (rawCode nativeNB)) zeroCode)

theorem exact_PrintedTowerCodeRead : ExactPrintedTowerCodeRead := by
  intro S n
  have rawClosed := exact_ClosedNativeTowerFamily S n
  have ordinary : Ordinary (app indexType indexType (finalHead n) (finalOperand n)) := by
    rw [← towerOuter n]
    exact rawClosed.1.2.1
  obtain ⟨F,hF⟩ := (NumberedWindowOrdinaryDomainProof.termDomain (finalHead n)).mpr ordinary.1
  obtain ⟨A,hA⟩ := (NumberedWindowOrdinaryDomainProof.termDomain (finalOperand n)).mpr ordinary.2.1
  let Q := appNode indexType indexType F A
  have translated : tr (towerTerm n) = some Q := by
    rw [towerOuter n]
    exact ordinaryAppRead indexType indexType (finalHead n) (finalOperand n) F A hF hA
  obtain ⟨found,seen,hCode⟩ := towerRead S n
  have same : Q = found := Option.some.inj (translated.symm.trans seen)
  have coded : encodeTerm Q = towerCode n := by
    rw [same]
    exact hCode
  have decoded : decodeTerm (towerCode n) = some Q := by
    rw [← coded]
    exact NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.2.1 Q
  have realized := ((NumberedWindowOrdinaryQuoteProof.term (towerTerm n) Q translated).2 0).1
  have typed := NumberedWindowRealizationTypingProof.typed realized EmptyContext indexType rawClosed.1.1.1
  have native : nativeCode (closedTower S n) = towerCode n := by
    simp only [nativeCode,closedTowerLiteral,translated,Option.map_some,Option.getD_some,coded]
  exact ⟨F,A,hF,hA,translated,coded,decoded,typed,native,codePositive n⟩

#print axioms exact_PrintedLowerCode
#print axioms towerRead
#print axioms exact_PrintedTowerCodeRead
end LogicLineages.PersistentMarking.NativeTowerNumericCodeProof
