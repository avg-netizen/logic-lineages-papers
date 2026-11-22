module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)

/-- The three arguments supplied by the original unary cover adapter. -/
def callbackTape {α : Type} (s : Settings) (seed : OTerm α) : Fin 3 → OTerm α :=
  ![numeral (Encodable.encode s.window.2), numeral (Encodable.encode s.types), seed]

def callbackAt {α : Type} (C : Program 3) (s : Settings) (value seed : OTerm α) : Formula α :=
  programGraph C value (callbackTape s seed)

def ExactCoverOptionGraph : Prop :=
  ∀ (C : Program 3) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (value seed : OTerm α),
    let callback := callbackAt C s value seed
    let option := unary (coverOption C s) value seed
    Nonempty (Derivation body Γ ((callback.imp option) ⊓ (option.imp callback)))

def ExactScratchCallbackZero : Prop :=
  ∀ (C : Program 3) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (seed : OTerm α),
    Nonempty (Derivation body Γ
      ((callbackAt C s z seed).imp (unary (scratchVertices C s) z seed)))

def ExactScratchCallbackSuccessor : Prop :=
  ∀ (C : Program 3) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (value seed : OTerm α),
    Nonempty (Derivation body Γ
      ((callbackAt C s (suc value) seed).imp (unary (scratchVertices C s) value seed)))

def ExactSameCoverOptionOutput : Prop :=
  ∀ (C : Program 3) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (tag left right leftVertices rightVertices : OTerm α),
    let options := unary (coverOption C s) tag left ⊓ unary (coverOption C s) tag right
    let vertices :=
      unary (scratchVertices C s) leftVertices left ⊓ unary (scratchVertices C s) rightVertices right
    Nonempty (Derivation body Γ ((options ⊓ vertices).imp (eqn leftVertices rightVertices)))

def ExactSameCallbackOutput : Prop :=
  ∀ (C : Program 3) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (tag left right leftVertices rightVertices : OTerm α),
    let callbacks := callbackAt C s tag left ⊓ callbackAt C s tag right
    let vertices :=
      unary (scratchVertices C s) leftVertices left ⊓ unary (scratchVertices C s) rightVertices right
    Nonempty (Derivation body Γ ((callbacks ⊓ vertices).imp (eqn leftVertices rightVertices)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets
