module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.ScalarCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.BinaryCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem operation {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (multiply : Bool) (a b c d : Term ctx)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a c))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b d)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (binaryValue J multiply a b) (binaryValue K multiply c d))) :=
 CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag (if multiply then 4 else 3) H.hc H.ha L.hc L.ha _ _ _ _ ha hb

theorem certificate {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (multiply : Bool) (a b c d hac hbd a' b' c' d' hac' hbd' : Term ctx)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a a'))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b b'))
 (hc : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c c'))
 (hd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal d d'))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hac hac'))
 (hk : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hbd hbd')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCertificate J multiply a b c d hac hbd) (binaryCertificate K multiply a' b' c' d' hac' hbd'))) := by
 obtain ⟨hp⟩ := ScalarCopy.ordinary p J K H L binaryEnvironment (binaryTerm multiply (.var 0) (.var 1))
  (b ::ᵥ nil) (b' ::ᵥ nil) a c hac a' c' hac' (fun i => Fin.cases hb (fun j => Fin.elim0 j) i) ha hc hh
 obtain ⟨hq⟩ := ScalarCopy.ordinary p J K H L binaryEnvironment (binaryTerm multiply (.var 1) (.var 0))
  (c ::ᵥ nil) (c' ::ᵥ nil) b d hbd b' d' hbd' (fun i => Fin.cases hc (fun j => Fin.elim0 j) i) hb hd hk
 obtain ⟨hx⟩ := operation p J K H L multiply a b a' b' ha hb
 obtain ⟨hy⟩ := operation p J K H L multiply c b c' b' hc hb
 obtain ⟨hz⟩ := operation p J K H L multiply c d c' d' hc hd
 exact TransitivityCopy.certificate p J.mtag J.ctag J.atag J.constructorTag K.mtag K.ctag K.atag K.constructorTag
  H.hm H.hc H.ha H.h12 L.hm L.hc L.ha L.h12 _ _ _ _ _ _ _ _ _ _ hx hy hz hp hq

theorem pair {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (a b c d hac hbd a' b' c' d' hac' hbd' : Term ctx)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a a'))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b b'))
 (hc : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c c'))
 (hd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal d d'))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hac hac'))
 (hk : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hbd hbd')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (pairCertificate J a b c d hac hbd) (pairCertificate K a' b' c' d' hac' hbd'))) := by
 obtain ⟨hs⟩ := certificate p J K H L false _ _ _ _ _ _ _ _ _ _ _ _ ha hb hc hd hh hk
 obtain ⟨hab⟩ := operation p J K H L false _ _ _ _ ha hb
 obtain ⟨hcd⟩ := operation p J K H L false _ _ _ _ hc hd
 obtain ⟨hm⟩ := certificate p J K H L true _ _ _ _ _ _ _ _ _ _ _ _ hab hab hcd hcd hs hs
 obtain ⟨hab2⟩ := operation p J K H L true _ _ _ _ hab hab
 obtain ⟨hcd2⟩ := operation p J K H L true _ _ _ _ hcd hcd
 exact certificate p J K H L false _ _ _ _ _ _ _ _ _ _ _ _ hab2 ha hcd2 hc hm hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.BinaryCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.BinaryCopy
