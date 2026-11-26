module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCoverBoundsAlgorithm (Measure bounds)
open NumberedWindowCoverAlgorithm (grammar)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)

def TermMeasureCalibrated (M : Program 1) : Prop := ∀ n,
  evaluate M (n ::ᵥ nil) = Encodable.encode (bounds n).1

/-- The third argument is the ordered original pair (nodes, maximum numeral). -/
def GrammarOptionCalibrated (G : Program 3) : Prop := ∀ (H K : List Nat) (m : Measure),
  evaluate G (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ Encodable.encode m ::ᵥ nil) =
    Encodable.encode (some (grammar H K m.2 m.1).1)

def rawCall (p : Program 1) : Program 3 :=
  .composition p (fun _ : Fin 1 => .projection (2 : Fin 3))

def generatorCall (M : Program 1) (G : Program 3) : Program 3 :=
  .composition G (Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (rawCall M) Fin.elim0)))

def factoredCover (V M : Program 1) (G : Program 3) : Program 3 :=
  branch (rawCall V) (constantZero 3) (generatorCall M G)

def ExactFactoredCoverCalibration : Prop :=
  ∀ (V M : Program 1) (G : Program 3), TermSyntaxCalibrated V → TermMeasureCalibrated M →
    GrammarOptionCalibrated G → ActualSelectedCoverOutput (factoredCover V M G)

def ExactSelectedFactoredCover : Prop :=
  ∃ (V M : Program 1) (G : Program 3), TermSyntaxCalibrated V ∧ TermMeasureCalibrated M ∧
    GrammarOptionCalibrated G ∧ ActualSelectedCoverOutput (factoredCover V M G)

/-- The actual raw exchange bit preserves the value of any correctly selected term-measure program. -/
def ExactMeasureExchangeInvariance : Prop := ∀ (M : Program 1), TermMeasureCalibrated M →
  ∀ (hp : HeadPairs) a b, (bits hp a b).1 = true →
    evaluate M (a ::ᵥ nil) = evaluate M (b ::ᵥ nil)

/-- Supplying the same genuine measure graph output gives genuine equality
of the original optional cover reports. The chosen syntax permits the true branch. -/
def ExactOpenFactoredCoverEquality : Prop :=
  ∀ (V M : Program 1) (G : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (a b m x y : OTerm α),
    let C := factoredCover V M G
    let inputs := (unary V (suc z) a ⊓ unary V (suc z) b) ⊓ (unary M m a ⊓ unary M m b)
    let outputs := unary (coverOption C s) x a ⊓ unary (coverOption C s) y b
    Nonempty (Derivation body Γ ((inputs ⊓ outputs).imp (eqn x y)))

end LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
