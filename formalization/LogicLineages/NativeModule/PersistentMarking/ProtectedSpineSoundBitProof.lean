module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundRelationProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionObservationProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorParameterProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundBitProof
open Spine DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation PortNormalization

theorem observedPaper (F : Inputs S) (Γ : Context) (σ : Ty) (t : Expr)
    (h : t ∈ observations F.data.names F.data.ports Γ F.target σ) : PaperTerm S t σ :=
  (DecisionObservationProof.paper S F.data.names F.data.ports Γ F.target F.targetType σ t
    F.targetPaper F.targetOrdinary h).1

theorem bits (F : Inputs S) (Γ : Context) (σ : Ty) (q t : Expr) (c : Code)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (ho : t ∈ observations F.data.names F.data.ports Γ F.target σ)
    (h : Related F σ Γ c (some q)) :
    ((decode (domain F) σ Γ c).weak Γ t = true → Weak S q t) ∧
    ((decode (domain F) σ Γ c).strict Γ t = true → Strict S q t) := by
  rw [Related.eq_def] at h
  exact (h.2 Γ hw (DecisionPortsProof.extensionRefl Γ)).1 t ho

theorem tagged (F : Inputs S) (Γ : Context) (q t : Expr) (a : MarkedExtras.Tagged)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (ho : Observed F Γ t) (hr : Related F a.1 Γ a.2 (some q)) (strict : Bool)
    (h : MarkedConstructorTests.bit strict (domain F) Γ a t = true) :
    if strict then Strict S q t else Weak S q t := by
  simp only [MarkedConstructorTests.bit,Bool.and_eq_true,decide_eq_true_eq] at h
  have hs := bits F Γ a.1 q t a.2 hw (h.1.symm ▸ ho) hr
  cases strict
  · exact hs.1 h.2
  · exact hs.2 h.2

theorem undefinedWeak (F : Inputs S) (Γ : Context) (σ : Ty) (t : Expr) (c : Code)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (ho : t ∈ observations F.data.names F.data.ports Γ F.target σ)
    (h : Related F σ Γ c none) : (decode (domain F) σ Γ c).weak Γ t = false := by
  rw [ProtectedSpineSoundRelationProof.undefined F σ Γ c h]
  exact ((StructuralWholeBottomProof.wholeBottom (domain F) σ Γ hw).2 Γ hw
    (DecisionPortsProof.extensionRefl Γ)).2.1 t ho |>.1

end LogicLineages.PersistentMarking.ProtectedSpineSoundBitProof
