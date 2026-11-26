import LogicLineages.PersistentMarking.StructuralCoverageTargets
namespace LogicLineages.PersistentMarking.TypeSupport
open Spine NameBridge StructuralContext

def subtypes : Ty → List Ty
  | .ground => [.ground]
  | .arrow σ τ => .arrow σ τ :: (subtypes σ ++ subtypes τ)

/- Ordinary literal node/binder support. The marked branch is merely a total
raw convention, NOT the later auxiliary declaration-retaining universe. -/
mutual
 def support : Expr → List Ty
   | .free σ _ | .bound σ _ => subtypes σ
   | .lam σ body => subtypes (.arrow σ body.type) ++ subtypes σ ++ support body
   | .head f base => subtypes f.result ++ supportArgs base
   | .marked _ τ base extras => subtypes τ ++ supportArgs base ++ supportArgs extras
 def supportArgs : Args → List Ty
   | .nil => []
   | .cons q qs => support q ++ supportArgs qs
end
mutual
 def namedSupport : Term → List Ty
   | .var σ _ => subtypes σ
   | .lam σ _ body => subtypes (.arrow σ body.type) ++ subtypes σ ++ namedSupport body
   | .head f base => subtypes f.result ++ namedSupportArgs base
   | .marked _ τ base extras => subtypes τ ++ namedSupportArgs base ++ namedSupportArgs extras
 def namedSupportArgs : List Term → List Ty
   | [] => []
   | q::qs => namedSupport q ++ namedSupportArgs qs
end

def Included (small large : Expr) : Prop := ∀ ρ, ρ ∈ support small → ρ ∈ support large

def ImageSupport (θ : FreeMap) (q : Expr) (ρ : Ty) : Prop :=
  ∃ σ x, freeOccurs (σ,x) q = true ∧ ρ ∈ support (θ σ x)

abbrev NamedMap := Ty → Nat → Term
def encodeMap (η : NamedMap) : FreeMap := fun σ x => encode [] (η σ x)
/- Canonical named representative of the source-permitted typed de Bruijn
capture-avoiding substitution, not a beta/eta normalizer. -/
def namedSubstitute (η : NamedMap) (q : Term) : Term := decode [] (freeSub (encodeMap η) 0 (encode [] q))
def NamedOrdinaryMap (S : Signature) (η : NamedMap) : Prop := ∀ σ x,
  NamedTyped (η σ x) σ ∧ NamedValid S (η σ x) ∧ StructuralCoverageTargets.NamedOrdinary (η σ x)
end LogicLineages.PersistentMarking.TypeSupport
