import LogicLineages.PersistentMarking.ProtectedSpineCompletenessPortProof
import LogicLineages.PersistentMarking.PortNormalizationProof

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessChecks
open Spine NameBridge DecisionPorts RefinementRenameSupport
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open MarkedConstructorOperator (leastFixedPoint)

theorem exact_CompleteObservation : CompleteObservation := by
  intro S F Γ q t σ hw hSource hObs hq ht
  let M := leastFixedPoint S (domain F) F.data.sourceHeads
  obtain ⟨hm,hfix⟩ := fixed S F
  have hTypes := ProtectedSpineAdequacyTypingProof.ends S q t σ hq ht
  have hBits := rootBits S F M Γ q t hm hw hSource hTypes.1.1 hObs hTypes.2.2
  constructor
  · intro h
    have hp' := PortNormalizationProof.weak S F q t h (fun _ x => x) Γ
      (fun _ _ _ he => he) hw (by simpa only [renameIdentity] using hSource)
      (by simpa only [renameIdentity] using hObs)
    have hp : PortComparison.Weak S F.data.types F.data.names Γ q t := by
      simpa only [renameIdentity] using hp'
    exact hBits.1.trans (ProtectedSpineCompletenessPortProof.weak S F M hm hfix Γ q t hp ⟨hw,hSource,hObs⟩)
  · intro h
    have hp' := PortNormalizationProof.strict S F q t h (fun _ x => x) Γ
      (fun _ _ _ he => he) hw (by simpa only [renameIdentity] using hSource)
      (by simpa only [renameIdentity] using hObs)
    have hp : PortComparison.Strict S F.data.types F.data.names Γ q t := by
      simpa only [renameIdentity] using hp'
    exact hBits.2.trans (ProtectedSpineCompletenessPortProof.strict S F M hm hfix Γ q t hp ⟨hw,hSource,hObs⟩)

#print axioms exact_CompleteObservation
end LogicLineages.PersistentMarking.ProtectedSpineCompletenessChecks
