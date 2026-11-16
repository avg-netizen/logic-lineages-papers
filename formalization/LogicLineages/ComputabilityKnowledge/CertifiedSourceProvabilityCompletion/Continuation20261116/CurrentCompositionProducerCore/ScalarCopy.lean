module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.ScalarCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem term {arity n depth inputs ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (e : FixedFormulaSubstitution.Environment n depth inputs) (f : Term n)
 (raw other : List.Vector (Term ctx) inputs)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (raw.get i) (other.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (FixedFormulaSubstitution.termValue J.ctag J.atag e raw f) (FixedFormulaSubstitution.termValue K.ctag K.atag e other f))) := by
 obtain ⟨hc⟩ := CurrentCompositionCertificate.TermCopiesProof.term p J.ctag J.atag K.ctag K.atag H.hc H.ha L.hc L.ha e raw f
 obtain ⟨hr⟩ := FormulaRaw.term p K.ctag K.atag L.hc L.ha raw other hraw e f
 exact ⟨Logic.trans _ _ _ hc hr⟩

theorem reflexivity {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (a b : Term ctx) (h : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (reflexivityCertificate J a) (reflexivityCertificate K b))) := by
 have hargs : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal ((a ::ᵥ nil).get i) ((b ::ᵥ nil).get i)) := by
  intro i
  cases i using Fin.cases with
  | zero => exact h
  | succ i => exact Fin.elim0 i
 obtain ⟨hl⟩ := CallTransport.callCopy p RawReflexivity.lineConstructor J.reflexivityTag K.reflexivityTag H.hr L.hr _ _ hargs
 exact CallTransport.singleton p J.rctag K.rctag H.hrc L.hrc _ _ hl

theorem ordinary {arity n inputs ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (raw other : List.Vector (Term ctx) inputs) (a b code a' b' code' : Term ctx)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (raw.get i) (other.get i)))
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a a'))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b b'))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code code')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag e f raw a b code)
   (PrescribedRuntimeEquality.unaryCertificate K.mtag K.ctag K.atag K.constructorTag K.rctag K.reflexivityTag e f other a' b' code'))) := by
 have hcons (x y : Term ctx) (hxy : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal x y)) :
  ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal ((x ::ᵥ raw).get i) ((y ::ᵥ other).get i)) := by
  intro i
  cases i using Fin.cases with
  | zero => exact hxy
  | succ i => exact hraw i
 obtain ⟨hft⟩ := term p J K H L (UniformRuntimeEnvironmentAgreement.specialize e) f (a ::ᵥ raw) (a' ::ᵥ other) (hcons a a' ha)
 obtain ⟨hfu⟩ := term p J K H L (UniformRuntimeEnvironmentAgreement.specialize e) f (b ::ᵥ raw) (b' ::ᵥ other) (hcons b b' hb)
 obtain ⟨hopen⟩ := term p J K H L e f raw other hraw
 obtain ⟨hq⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha L.hc L.ha _ _ _ _ hft hft
 obtain ⟨hr⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha L.hc L.ha _ _ _ _ hft hfu
 obtain ⟨hmatrix⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha L.hc L.ha _ _ _ _ hft hopen
 obtain ⟨himp⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7 H.hc H.ha L.hc L.ha _ _ _ _ hq hr
 obtain ⟨hseed⟩ := EqualityCopy.rule12 p J.ctag J.constructorTag K.ctag K.constructorTag H.hc H.h12 L.hc L.h12 _ _ _ _ _ _ hmatrix ha hb
 obtain ⟨hfirst⟩ := CallTransport.mp p J.mtag K.mtag H.hm L.hm _ _ _ _ _ _ himp hseed hh
 obtain ⟨href⟩ := reflexivity p J K H L _ _ hft
 exact CallTransport.mp p J.mtag K.mtag H.hm L.hm _ _ _ _ _ _ hr hfirst href

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.ScalarCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.ScalarCopy
