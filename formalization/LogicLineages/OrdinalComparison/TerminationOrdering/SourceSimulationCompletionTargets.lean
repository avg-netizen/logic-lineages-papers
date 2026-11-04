module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedOriginalSourcePresentation
open NumberedOriginalStructuralTranslation NumberedOrdinaryWindow NumberedConfinedSourceSimulation
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths LiteralContexts
open SourceSimulationCompletion

/-- Joint effectivity in the type window and the actual typed source. -/
def FixedUniverseTranslationPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : List Ty × PackedSource (Fin n) arity Gamma => tr p.1 p.2)

/-- Ordinary numerical decoding is separate from the typed-source endpoint. -/
def NumericTranslationPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : List Ty × Nat => numericTr n arity Gamma p.1 p.2)

def NumericTranslationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (S : List Ty)
    (source : PackedSource (Fin n) arity Gamma),
    numericTr n arity Gamma S (packedSourceNumber source) = some (tr S source)

/-- The literal source window is fixed for both translations. The conclusion is
the positive quotient closure, with both actual auxiliary endpoints in `S`. -/
def FixedUniverseSimulation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (tau : Ty) (s t : Term (Fin n) arity Gamma tau),
    ConfinedStrict above s t →
    let S := sourceWindow s
    SubtypeClosed (fun u => u ∈ S) ∧
    InUniverse (symbols n) S (translateOriginal s) ∧
    InUniverse (symbols n) S (translateOriginal t) ∧
    PositivePath (QuotientEdge n arity (symbols n) S above Gamma)
      (tr S ⟨tau,s⟩) (tr S ⟨tau,t⟩)

/-- Whole paper06 `lem:simulation`, at the source's fixed-family parameter scope.
One effective family is chosen before either endpoint or the precedence is
given. For a comparison its one universe is exactly `Ty(s)`; there is no ID1,
accessibility, ordinal, semantic-supplier, or effectiveness premise. -/
def ArithmeticSimulation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    ∃ translation : List Ty → PackedSource (Fin n) arity Gamma → Nat,
      Primrec (fun p : List Ty × PackedSource (Fin n) arity Gamma =>
        translation p.1 p.2) ∧
      (∀ S : List Ty, Computable (translation S)) ∧
      (∀ (S : List Ty) (source : PackedSource (Fin n) arity Gamma),
        translation S source =
          representativeCode (symbols n) S (packedTranslation source)) ∧
      (∀ (above : Fin n → Fin n → Prop) (tau : Ty)
        (s t : Term (Fin n) arity Gamma tau),
        ConfinedStrict above s t →
        let S := sourceWindow s
        SubtypeClosed (fun u => u ∈ S) ∧
        InUniverse (symbols n) S (translateOriginal s) ∧
        InUniverse (symbols n) S (translateOriginal t) ∧
        PositivePath (QuotientEdge n arity (symbols n) S above Gamma)
          (translation S ⟨tau,s⟩) (translation S ⟨tau,t⟩))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionTargets
