import LogicLineages.PersistentMarking.HereditaryDomainSemantics
namespace LogicLineages.PersistentMarking.HereditaryDomainTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def ConstructionEquation : Prop := ∀ E σ,
  descriptor E σ = build E σ (canonicalLower E σ)
def EffectiveCarrier : Prop := ∀ E σ Γ c,
  c ∈ (descriptor E σ).carriers Γ ↔
    Fits ((layout E σ (canonicalLower E σ) Γ).map Prod.snd) c ∧
    monotone E σ (canonicalLower E σ) Γ c = true ∧ natural E σ (canonicalLower E σ) Γ c = true

def CarrierDistinct : Prop := ∀ E σ Γ, ((descriptor E σ).carriers Γ).Pairwise (· ≠ ·)
def CarrierNonempty : Prop := ∀ E σ Γ, WellFormed E.types E.ports Γ →
  ∃ c, c ∈ (descriptor E σ).carriers Γ

def DecodeEncode : Prop := ∀ E σ Γ c,
  WellFormed E.types E.ports Γ → c ∈ (descriptor E σ).carriers Γ →
  Valid E σ Γ (decode E σ Γ c) ∧ encode E σ Γ (decode E σ Γ c) = c

def EncodeDecode : Prop := ∀ E σ Γ v,
  WellFormed E.types E.ports Γ → Valid E σ Γ v →
  encode E σ Γ v ∈ (descriptor E σ).carriers Γ ∧
  ValueEq E σ Γ (decode E σ Γ (encode E σ Γ v)) v

def PartialOrder : Prop := ∀ E σ Γ, WellFormed E.types E.ports Γ →
  (∀ a, a ∈ (descriptor E σ).carriers Γ → (descriptor E σ).le Γ a a = true) ∧
  (∀ a b c, a ∈ (descriptor E σ).carriers Γ → b ∈ (descriptor E σ).carriers Γ →
    c ∈ (descriptor E σ).carriers Γ → (descriptor E σ).le Γ a b = true →
    (descriptor E σ).le Γ b c = true → (descriptor E σ).le Γ a c = true) ∧
  (∀ a b, a ∈ (descriptor E σ).carriers Γ → b ∈ (descriptor E σ).carriers Γ →
    (descriptor E σ).le Γ a b = true → (descriptor E σ).le Γ b a = true → a=b)

def Join : Prop := ∀ E σ Γ xs, WellFormed E.types E.ports Γ →
  (∀ x, x ∈ xs → x ∈ (descriptor E σ).carriers Γ) →
  (descriptor E σ).join Γ xs ∈ (descriptor E σ).carriers Γ ∧
  (∀ x, x ∈ xs → (descriptor E σ).le Γ x ((descriptor E σ).join Γ xs) = true) ∧
  (∀ b, b ∈ (descriptor E σ).carriers Γ →
    (∀ x, x ∈ xs → (descriptor E σ).le Γ x b = true) →
    (descriptor E σ).le Γ ((descriptor E σ).join Γ xs) b = true)

def Meet : Prop := ∀ E σ Γ xs, WellFormed E.types E.ports Γ →
  (∀ x, x ∈ xs → x ∈ (descriptor E σ).carriers Γ) →
  (descriptor E σ).meet Γ xs ∈ (descriptor E σ).carriers Γ ∧
  (∀ x, x ∈ xs → (descriptor E σ).le Γ ((descriptor E σ).meet Γ xs) x = true) ∧
  (∀ b, b ∈ (descriptor E σ).carriers Γ →
    (∀ x, x ∈ xs → (descriptor E σ).le Γ b x = true) →
    (descriptor E σ).le Γ b ((descriptor E σ).meet Γ xs) = true)

def Restriction : Prop := ∀ E σ Γ Θ,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  ∀ c, c ∈ (descriptor E σ).carriers Γ →
  (descriptor E σ).restrict Γ Θ c ∈ (descriptor E σ).carriers Θ ∧
  ValueEq E σ Θ (decode E σ Θ ((descriptor E σ).restrict Γ Θ c)) (decode E σ Γ c)

def RestrictionIdentityComposition : Prop := ∀ E σ,
  (∀ Γ c, WellFormed E.types E.ports Γ → c ∈ (descriptor E σ).carriers Γ →
    (descriptor E σ).restrict Γ Γ c = c) ∧
  (∀ Γ Δ Θ c, WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ →
    WellFormed E.types E.ports Θ → Extends Γ Δ → Extends Δ Θ →
    c ∈ (descriptor E σ).carriers Γ →
    (descriptor E σ).restrict Δ Θ ((descriptor E σ).restrict Γ Δ c) = (descriptor E σ).restrict Γ Θ c)

def RestrictionJoinsMeets : Prop := ∀ E σ Γ Θ xs,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  (∀ x, x ∈ xs → x ∈ (descriptor E σ).carriers Γ) →
  (descriptor E σ).restrict Γ Θ ((descriptor E σ).join Γ xs) =
    (descriptor E σ).join Θ (xs.map ((descriptor E σ).restrict Γ Θ)) ∧
  (descriptor E σ).restrict Γ Θ ((descriptor E σ).meet Γ xs) =
    (descriptor E σ).meet Θ (xs.map ((descriptor E σ).restrict Γ Θ))

/- Arbitrary subsets of the explicitly enumerated finite carrier, including
empty subsets. The actual algorithms above operate on finite lists. -/
def Complete : Prop := ∀ E σ Γ, WellFormed E.types E.ports Γ → ∀ P : Code → Prop,
  ∃ sup inf, sup ∈ (descriptor E σ).carriers Γ ∧ inf ∈ (descriptor E σ).carriers Γ ∧
  (∀ x, x ∈ (descriptor E σ).carriers Γ → P x →
    (descriptor E σ).le Γ x sup = true ∧ (descriptor E σ).le Γ inf x = true) ∧
  (∀ b, b ∈ (descriptor E σ).carriers Γ →
    (∀ x, x ∈ (descriptor E σ).carriers Γ → P x → (descriptor E σ).le Γ x b = true) →
    (descriptor E σ).le Γ sup b = true) ∧
  (∀ b, b ∈ (descriptor E σ).carriers Γ →
    (∀ x, x ∈ (descriptor E σ).carriers Γ → P x → (descriptor E σ).le Γ b x = true) →
    (descriptor E σ).le Γ b inf = true)

def FullFiniteLattices : Prop := ConstructionEquation ∧ EffectiveCarrier ∧ CarrierDistinct ∧
  CarrierNonempty ∧ DecodeEncode ∧ EncodeDecode ∧ PartialOrder ∧ Join ∧ Meet ∧
  Restriction ∧ RestrictionIdentityComposition ∧ RestrictionJoinsMeets ∧ Complete
end LogicLineages.PersistentMarking.HereditaryDomainTargets
