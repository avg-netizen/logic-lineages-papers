import LogicLineages.PersistentMarking.ProtectedSpineSoundStageTargets
import LogicLineages.PersistentMarking.ProtectedSpineSoundRelationProof
import LogicLineages.PersistentMarking.MarkedConstructorParameterProof
import LogicLineages.PersistentMarking.PortTermStateProof
import LogicLineages.PersistentMarking.MarkedConstructorInventoryProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundOwnerProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open MarkedFamilyParameters (Parameter)

theorem zipRestriction (E : Environment) (Γ Δ : Context) (ds : List Ty) (cs : List Code) :
    ds.zip (MarkedBaseTuples.restrictTuple E Γ Δ ds cs) = (ds.zip cs).map (MarkedExtras.restricted E Γ Δ) := by
  induction ds generalizing cs with
  | nil => rfl
  | cons d ds ih =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      change (d,(descriptor E d).restrict Γ Δ c)::ds.zip (MarkedBaseTuples.restrictTuple E Γ Δ ds cs) =
        (d,(descriptor E d).restrict Γ Δ c)::(ds.zip cs).map (MarkedExtras.restricted E Γ Δ)
      rw [ih cs]

theorem restrictBase (F : Inputs S) (Γ Δ : Context) (hw : WellFormed F.data.types F.data.ports Γ)
    (hd : WellFormed F.data.types F.data.ports Δ) (he : Extends Γ Δ)
    {xs : List MarkedExtras.Tagged} {bs : Args} (h : BaseRelated F Γ xs bs) :
    BaseRelated F Δ (xs.map (MarkedExtras.restricted (domain F) Γ Δ)) bs := by
  induction h with
  | nil => exact .nil
  | cons hq _ ih =>
    exact .cons (ProtectedSpineSoundRelationProof.exact_Restriction S F _ _ _ _ _ hw hd he hq) ih

theorem downTag (F : Inputs S) (Γ : Context) (a b : MarkedExtras.Tagged) (q : Expr)
    (hw : WellFormed F.data.types F.data.ports Γ) (ha : a ∈ MarkedExtras.«universe» (domain F) Γ)
    (h : MarkedExtras.le (domain F) Γ a b = true) (hr : Related F b.1 Γ b.2 (some q)) :
    a.1 = b.1 ∧ Related F a.1 Γ a.2 (some q) := by
  have he := (Bool.and_eq_true.mp h).1
  have ht : a.1 = b.1 := of_decide_eq_true he
  have ha' : a.2 ∈ (descriptor (domain F) a.1).carriers Γ :=
    ((MarkedExtrasFoundationProof.universeExact (domain F) Γ a.1 a.2).mp ha).2
  exact ⟨ht,ProtectedSpineSoundRelationProof.exact_Downward S F a.1 Γ a.2 b.2 (some q)
    hw ha' (Bool.and_eq_true.mp h).2 (ht.symm ▸ hr)⟩

theorem restrictExtras (F : Inputs S) (Γ Δ : Context) (es : Args) (xs : List MarkedExtras.Tagged)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (hd : WellFormed F.data.types F.data.ports Δ) (he : Extends Γ Δ)
    (h : ExtrasRelated F Γ es xs) : ExtrasRelated F Δ es (MarkedExtras.weaken (domain F) Γ Δ xs) := by
  intro a ha
  obtain ⟨ham,b,hb,hle⟩ := (MarkedExtrasWeakeningProof.weakeningMember (domain F) Γ Δ xs a).mp ha
  obtain ⟨i,q,hi,ht,hr⟩ := h b hb
  have hs := ProtectedSpineSoundRelationProof.exact_Restriction S F b.1 Γ Δ b.2 (some q) hw hd he hr
  obtain ⟨ht',hq⟩ := downTag F Δ a (MarkedExtras.restricted (domain F) Γ Δ b) q hd ham hle hs
  exact ⟨i,q,hi,ht'.trans ht,hq⟩

theorem weaken (F : Inputs S) (p : Parameter) (Δ : Context) (bs es : Args)
    (ho : OwnerRelated F p bs es) (hw : WellFormed F.data.types F.data.ports Δ) (he : Extends p.2.2.1 Δ) :
    OwnerRelated F (MarkedFamilyCoherence.weakenParameter (domain F) p Δ) bs es := by
  rcases p with ⟨f,τ,Γ,cs,xs⟩
  obtain ⟨hp,hPaper,hSource,hb,hx⟩ := ho
  have hW := MarkedFamilyCoherenceFoundationProof.destinationValid (domain F) F.data.sourceHeads
    (f,τ,Γ,cs,xs) Δ hp hw he
  have hs := DecisionSourceBasicProof.weakening _ _ _ Γ Δ _ he hSource
  have hb' := restrictBase F Γ Δ hp.2.2.1 hw he hb
  rw [←zipRestriction] at hb'
  exact ⟨hW,hPaper,hs,hb',restrictExtras F Γ Δ es xs hp.2.2.1 hw he hx⟩

theorem retype (F : Inputs S) (f : Head) (τ ρ : Ty) (Γ : Context) (cs : List Code)
    (xs : List MarkedExtras.Tagged) (bs es : Args) (ho : OwnerRelated F (f,τ,Γ,cs,xs) bs es)
    (hρ : ρ ∈ F.data.types) :
    OwnerRelated F (f,ρ,Γ,cs,xs) bs es := by
  obtain ⟨hp,hPaper,hSource,hb,he⟩ := ho
  have valid : MarkedFamilyParameters.Valid (domain F) F.data.sourceHeads (f,ρ,Γ,cs,xs) :=
    ⟨hp.1,hρ,hp.2.2.1,hp.2.2.2⟩
  have hu := PortTermStateProof.owner S F Γ f τ bs es hSource ρ hρ
  have ht : PaperTerm S (.marked f ρ bs es) ρ := by
    cases hPaper.1 with
    | marked hBase hExtras => exact ⟨.marked hBase hExtras,hPaper.2⟩
  exact ⟨valid,ht,hu,hb,he⟩

end LogicLineages.PersistentMarking.ProtectedSpineSoundOwnerProof
