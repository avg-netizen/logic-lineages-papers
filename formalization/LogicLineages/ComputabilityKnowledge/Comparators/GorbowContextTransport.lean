module

public import LogicLineages.ComputabilityKnowledge.GorbowContextTransport

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowContextTransport
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding
open LogicLineages.ComputabilityKnowledge.GorbowContextTransport

def ExactDomain : Prop :=
  (∀ n m (t : Term n), (∃ u, term m t=some u) ↔ ∀ i∈termSupport t, i<m) ∧
  (∀ n m (φ : Formula n), (∃ ψ, formula m φ=some ψ) ↔ ∀ i∈formulaSupport φ, i<m)

def EncodingPreservation : Prop :=
  (∀ n m (t : Term n) (u : Term m), term m t=some u → GorbowTermPrefixCode.encode t=GorbowTermPrefixCode.encode u) ∧
  (∀ n m (φ : Formula n) (ψ : Formula m), formula m φ=some ψ → GorbowFormulaPrefixCode.encode φ=GorbowFormulaPrefixCode.encode ψ)

def SupportPreservation : Prop :=
  (∀ n m (t : Term n) (u : Term m), term m t=some u → termSupport t=termSupport u) ∧
  (∀ n m (φ : Formula n) (ψ : Formula m), formula m φ=some ψ → formulaSupport φ=formulaSupport ψ)

def Semantics : Prop :=
  (∀ n m (t : Term n) (u : Term m), term m t=some u → ∀ I ρ τ,
    (∀ (i : Fin n) (j : Fin m), i.val=j.val → i.val∈termSupport t → ρ i=τ j) →
    t.realize I ρ=u.realize I τ) ∧
  (∀ n m (φ : Formula n) (ψ : Formula m), formula m φ=some ψ → ∀ I ρ τ,
    (∀ (i : Fin n) (j : Fin m), i.val=j.val → i.val∈formulaSupport φ → ρ i=τ j) →
    (φ.realize I ρ ↔ ψ.realize I τ))

def ExactRejection : Prop :=
  (∀ n m (t : Term n), term m t=none ↔ ∃ i∈termSupport t, m≤i) ∧
  (∀ n m (φ : Formula n), formula m φ=none ↔ ∃ i∈formulaSupport φ, m≤i)

def NamedClosure : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  ∃ σ τ : Sentence, formula 0 (bindAll v φ)=some σ ∧ formula 0 (bindEx v φ)=some τ ∧
    GorbowFormulaPrefixCode.encode σ=GorbowFormulaPrefixCode.encode (bindAll v φ) ∧
    GorbowFormulaPrefixCode.encode τ=GorbowFormulaPrefixCode.encode (bindEx v φ) ∧
    ∀ I ρ, (σ.realize I Fin.elim0 ↔ ∀ x, φ.realize I (assignAt ρ v x)) ∧
      (τ.realize I Fin.elim0 ↔ ∃ x, φ.realize I (assignAt ρ v x))

def Target : Prop := ExactDomain ∧ EncodingPreservation ∧ SupportPreservation ∧ Semantics ∧ ExactRejection ∧ NamedClosure
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowContextTransport
