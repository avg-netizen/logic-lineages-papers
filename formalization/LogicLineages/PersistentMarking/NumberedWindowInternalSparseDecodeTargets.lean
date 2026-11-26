module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecode
public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
public import Mathlib.Data.Nat.Sqrt

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparseDecode

def CandidateValues : Prop :=
  ∀ n, let s := Nat.sqrt n
    evaluate leftCandidate (n ::ᵥ nil) = n - s*s ∧
    evaluate rightCandidate (n ::ᵥ nil) = s - (n - s*s)

def GuardValue : Prop :=
  ∀ n, let s := Nat.sqrt n
    evaluate good (n ::ᵥ nil) = if n - s*s ≤ s then 1 else 0

/-- Exact whole optional output, not only the right inverse at image codes.
The source bounded search remains its own literal existing definition. -/
def AllInputDecoder : Prop := ∀ n, chosenDecode n = NumberedWindowPairAlgorithm.decode n

def certifiedOutputs {α : Type} (n x y : OTerm α) : Formula α :=
  programGraph good (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![n] ⊓
    (programGraph leftCandidate x ![n] ⊓ programGraph rightCandidate y ![n])

/-- Genuine graph recognition for arbitrary free terms in the retained
object calculus; the standard-natural calibration is not a proof rule. -/
def OpenSuccess : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n x y : OTerm α),
    let g := programGraph NumberedWindowInternalSparsePair.pair n ![x,y]
    let s := certifiedOutputs n x y
    Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def hasPreimage {α : Type} (n : OTerm α) : Formula α :=
  let nn := (n.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  let x : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let y : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  existsOne (existsOne (programGraph NumberedWindowInternalSparsePair.pair nn ![x,y]))

/-- Sparse failures are arithmetic proof obligations rather than impossible
inputs; every rejecting code is shown internally to have no pair preimage. -/
def OpenFailure : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α),
    let g := programGraph good OrdinaryArithmetic.zeroTerm ![n]
    let s := (hasPreimage n).not
    Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeTargets
