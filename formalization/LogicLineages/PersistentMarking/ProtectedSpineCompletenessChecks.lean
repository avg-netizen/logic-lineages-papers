import LogicLineages.PersistentMarking.ProtectedSpineCompletenessPortProof
import LogicLineages.PersistentMarking.PortNormalizationProof

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessChecks
open Spine NameBridge DecisionPorts RefinementRenameSupport
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open MarkedConstructorOperator (leastFixedPoint)

private theorem freeIdentity (q : Expr) :
    ∀ d, freeSub (fun σ x => .free σ x) d q = q := by
  apply @Expr.rec (fun q => ∀ d, freeSub (fun σ x => .free σ x) d q = q)
    (fun qs => ∀ d, freeSubArgs (fun σ x => .free σ x) d qs = qs)
  · intro σ x d
    rfl
  · intro σ i d
    rfl
  · intro σ body h d
    simp only [freeSub,h]
  · intro f base h d
    simp only [freeSub,h]
  · intro f σ base extras hb he d
    simp only [freeSub,hb,he]
  · intro d
    rfl
  · intro a tail ha ht d
    simp only [freeSubArgs,ha,ht]

private theorem renameIdentity (q : Expr) :
    RefinementRenamingTargets.rename (fun _ x => x) q = q :=
  freeIdentity q 0

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
