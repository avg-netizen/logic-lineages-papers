import LogicLineages.PersistentMarking.ProtectedSpineArgumentProof
import LogicLineages.PersistentMarking.MarkedConstructorAppendProof

namespace LogicLineages.PersistentMarking.ProtectedSpineHeadParameterProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineInterpreterCore ProtectedSpineLaws
open MarkedFamilyCoherence (InputLE weakenParameter)

def parameterAt (E : Environment) (f : Head) (τ : Ty) (base extras : Arguments) (Γ : Context)
    (a : Assignments) : MarkedFamilyParameters.Parameter :=
  parameter E f τ Γ (argumentValues base Γ a) (argumentValues extras Γ a)

theorem valid (E : Environment) (heads : List Head) (f : Head) (τ : Ty) (base extras : Arguments)
    (types : List Ty) (hl : ArgumentLaws E base f.arguments) (hx : ArgumentLaws E extras types)
    (hf : f ∈ heads) (hτ : τ ∈ E.types) (ht : ∀ σ, σ ∈ types → σ ∈ E.types)
    (Γ : Context) (a : Assignments) (ha : InputValid E Γ a) :
    MarkedFamilyParameters.Valid E heads (parameterAt E f τ base extras Γ a) :=
  ⟨hf,hτ,ha.1,hl.valid Γ a ha,MarkedExtrasDownProof.downExtra E Γ _ ha.1
    (ProtectedSpineArgumentProof.tags E Γ extras types a hx ha ht)⟩

theorem restrictBase (E : Environment) (Γ Δ : Context) (as : BoundValues) :
    MarkedBaseTuples.restrictTuple E Γ Δ (as.map Prod.fst) (as.map Prod.snd) =
      (weakenBound E Γ Δ as).map Prod.snd := by
  rw [MarkedBaseTuples.restrictTuple,ProtectedSpineArgumentProof.zipProjections]
  simp [weakenBound,List.map_map,Function.comp_def]

theorem restrictDown (E : Environment) (Γ Δ : Context) (xs : BoundValues)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hx : ∀ a, a ∈ xs → a ∈ MarkedExtras.«universe» E Γ) :
    MarkedExtras.weaken E Γ Δ (MarkedExtras.down E Γ xs) =
      MarkedExtras.down E Δ (weakenBound E Γ Δ xs) := by
  have hdown : MarkedExtras.down E Γ [] = [] := by simp [MarkedExtras.down]
  have hempty : MarkedExtras.Extra E Γ [] := by
    rw [← hdown]
    exact MarkedExtrasDownProof.downExtra E Γ [] hw (by simp)
  have h := StructuralExtraInsertionProof.natural E Γ Δ [] xs hw hd he hempty hx
  have hnil : MarkedExtras.weaken E Γ Δ [] = [] := by simp [MarkedExtras.weaken,MarkedExtras.down]
  rw [hnil] at h
  exact h

theorem natural (E : Environment) (f : Head) (τ : Ty) (base extras : Arguments)
    (types : List Ty) (hl : ArgumentLaws E base f.arguments) (hx : ArgumentLaws E extras types)
    (ht : ∀ σ, σ ∈ types → σ ∈ E.types) (Γ Δ : Context) (a : Assignments)
    (ha : InputValid E Γ a) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    weakenParameter E (parameterAt E f τ base extras Γ a) Δ =
      parameterAt E f τ base extras Δ (a.restrict E Γ Δ) := by
  let bs := argumentValues base Γ a
  let es := argumentValues extras Γ a
  change (f,τ,Δ,MarkedBaseTuples.restrictTuple E Γ Δ f.arguments (bs.map Prod.snd),
      MarkedExtras.weaken E Γ Δ (MarkedExtras.down E Γ es)) =
    (f,τ,Δ,(argumentValues base Δ (a.restrict E Γ Δ)).map Prod.snd,
      MarkedExtras.down E Δ (argumentValues extras Δ (a.restrict E Γ Δ)))
  have hDecl : bs.map Prod.fst = f.arguments := hl.types_eq Γ a
  rw [← hDecl,restrictBase E Γ Δ bs,hl.natural Γ Δ a ha hd he,
    restrictDown E Γ Δ es ha.1 hd he (ProtectedSpineArgumentProof.tags E Γ extras types a hx ha ht),
    hx.natural Γ Δ a ha hd he]

theorem ordered (E : Environment) (f : Head) (τ : Ty) (base extras : Arguments)
    (types : List Ty) (hl : ArgumentLaws E base f.arguments) (hx : ArgumentLaws E extras types)
    (ht : ∀ σ, σ ∈ types → σ ∈ E.types) (Γ : Context) (a b : Assignments)
    (ha : InputValid E Γ a) (hb : InputValid E Γ b) (hab : ProtectedSpineLaws.InputLE E Γ a b) :
    InputLE E (parameterAt E f τ base extras Γ a) (parameterAt E f τ base extras Γ b) := by
  refine ⟨rfl,rfl,rfl,hl.monotone Γ a b ha hb hab,?_⟩
  refine MarkedConstructorTagOrderProof.downMonotone E Γ _ _ ha.1
    (ProtectedSpineArgumentProof.tags E Γ extras types a hx ha ht)
    (ProtectedSpineArgumentProof.tags E Γ extras types b hx hb ht) ?_
  have hA : types.zip ((argumentValues extras Γ a).map Prod.snd) = argumentValues extras Γ a := by
    rw [← hx.types_eq Γ a,ProtectedSpineArgumentProof.zipProjections]
  have hB : types.zip ((argumentValues extras Γ b).map Prod.snd) = argumentValues extras Γ b := by
    rw [← hx.types_eq Γ b,ProtectedSpineArgumentProof.zipProjections]
  rw [← hA,← hB]
  exact MarkedConstructorTagOrderProof.zipOrder E Γ types _ _ (hx.valid Γ a ha).1
    (hx.valid Γ b hb).1 (hx.monotone Γ a b ha hb hab)

end LogicLineages.PersistentMarking.ProtectedSpineHeadParameterProof
