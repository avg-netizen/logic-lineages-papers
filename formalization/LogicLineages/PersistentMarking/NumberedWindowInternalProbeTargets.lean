module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowInternalPullbackTargets (Pullback)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
abbrev OTerm := OrdinaryArithmetic.Term

def typeCode : Ty → Nat
  | .ground => 0
  | .arrow σ τ => NumberedWindowPairAlgorithm.pair (typeCode σ) (typeCode τ) + 1

def typedAt {α : Type} (h : Program 2) (τ : Ty) (q : OTerm α) : Formula α :=
  programGraph h (numeral 1) ![numeral (typeCode τ),q]

def freshAt {α : Type} (a : Program 1) (q u : OTerm α) : Formula α :=
  programGraph a (OrdinaryArithmetic.succTerm u) ![q]

def witnesses {α : Type} (p : Program 3) (h : Program 2) (a : Program 1) (τ : Ty) (q : OTerm α) : Formula α :=
  let qp := (q.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  let up : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let vp : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  existsOne (existsOne (freshAt a qp up ⊓ (accepts p qp up vp ⊓ typedAt h τ vp)))

def TypedProbeTotal (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat) : Prop :=
  ∀ (σ τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (typedAt h (.arrow σ τ) q)) →
    Nonempty (Derivation (sourceBody d c) Γ (witnesses p h a τ q))

def FreshVariablesComputable (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat) : Prop :=
  ∀ (σ τ : Ty) (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (typedAt h (.arrow σ τ) q)) →
    Nonempty (Derivation (sourceBody d c) Γ (freshAt a q u)) →
    Nonempty (Derivation (sourceBody d c) Γ (formula p σ u))

def TypedComputabilityImpliesMembership : Prop :=
  ∀ (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat),
    Pullback d p c → TypedProbeTotal d p h a c → FreshVariablesComputable d p h a c →
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      Nonempty (Derivation (sourceBody d c) Γ (typedAt h τ q)) →
      Nonempty (Derivation (sourceBody d c) Γ (formula p τ q)) →
      Nonempty (Derivation (sourceBody d c) Γ (membership false q))
end LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
