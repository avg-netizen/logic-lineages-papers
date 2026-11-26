module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.SourcePresentation (Data)
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt freshAt TypedProbeTotal)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
open NumberedWindowInternalFreshProbeParsedTyped
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual typed acceptance by the chosen h and a genuine rawResult
report imply that report equals the very requested type numeral. -/
def ExactOpenRequestedResultField : Prop :=
  ∀ (i : Inputs) (W : List ProbeTy) (τ : ProbeTy)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q r : OTerm α),
      Nonempty (Derivation body Γ (typedAt (chosenH i W) τ q)) →
      Nonempty (Derivation body Γ (programGraph rawResult r ![q])) →
      Nonempty (Derivation body Γ (equal r (numeral (typeCode τ))))

/-- This is the same six-slot parsed emitter matrix, with genuine
equations identifying its two reported arrow components to the
requested literal domain and codomain. No context is substituted. -/
def literalParsedAt {α : Type} (bound : Program 1) (σ τ : ProbeTy) (q u : OTerm α) : Formula α :=
  let q' := q.relabel (Sum.inl : α → α ⊕ Fin 6)
  let u' := u.relabel (Sum.inl : α → α ⊕ Fin 6)
  let c : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let r : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let d : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let e : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let k : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let n : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  block (addressReports q' c r k ⊓ (arrowReports q' d e ⊓
    (sourceShape q' c r d e k ⊓ (programGraph bound n ![k] ⊓
      (equal u' (packedFreeTerm c d n) ⊓
        (equal d (numeral (typeCode σ)) ⊓ equal e (numeral (typeCode τ))))))))

def OpenLiteralParsed (i : Inputs) (W : List ProbeTy) : Prop :=
  ∀ (σ τ : ProbeTy) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (q u : OTerm α),
      Nonempty (Derivation body Γ (typedAt (chosenH i W) (.arrow σ τ) q)) →
      Nonempty (Derivation body Γ (freshAt (chosenA i) q u)) →
      Nonempty (Derivation body Γ (literalParsedAt i.freshBound σ τ q u))

def ExactOpenLiteralParsedFresh : Prop :=
  ∀ (i : Inputs) (W : List ProbeTy), OpenLiteralParsed i W

/-- Actual #611 totality for this specific h, a and preserved p. This
uses the already pinned syntactic child condition, not any numerical
typing truth inside ID1. -/
def ExactSameParsedTypedProbeTotal : Prop :=
  ∀ (i : Inputs) (W : List ProbeTy), ChildClosed W →
    ∀ (d : Data) (c : Nat),
      TypedProbeTotal d i.applicationGuard (chosenH i W) (chosenA i) c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
