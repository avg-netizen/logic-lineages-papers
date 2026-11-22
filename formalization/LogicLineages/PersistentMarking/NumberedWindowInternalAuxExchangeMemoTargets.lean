module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

/-- The original four fields of a literal auxiliary application. -/
def auxFields (n : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match unpackNode n with
  | some (6,[dom,cod,fn,arg]) => some (dom,cod,fn,arg)
  | _ => none

/-- Use only the original function position and retain one identical
argument and both annotations. Raw term validity is checked on both sides. -/
def guardedAuxChildren (a b : Nat) : Option (Nat × Nat) := do
  let (dom,cod,fn,arg) ← auxFields a
  let (dom',cod',fn',arg') ← auxFields b
  if dom = dom' ∧ cod = cod' ∧ arg = arg' ∧
      (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true then
    some (fn,fn')
  else none

/-- Row at key `i+1`; the complete previous scratch table ends with row
`i`. A malformed key is rejected. The extra branch consults the same
recursive table strictly below the current key. -/
def stepValue (base : Program 2) (i old : Nat) : Nat :=
  match decode (i+1) with
  | none => 0
  | some (a,b) =>
    let original := evaluate base (a ::ᵥ b ::ᵥ nil)
    match guardedAuxChildren a b with
    | none => original
    | some (f,g) =>
      let key := pair f g
      if key < i+1 ∧ evaluate lookup ((i-key) ::ᵥ old ::ᵥ nil) = 1 then 1 else original

/-- The precise input/output obligation on the future physical step.
Its selected auxiliary branch can later be derived from its actual AST. -/
def StepCalibrated (base : Program 2) (R : Program 4) : Prop :=
  ∀ i old, evaluate R (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = stepValue base i old

/-- Input order is the original raw source and target. The true physical
recursor is selected at their original sparse pair key. -/
def selected (R : Program 4) : Program 2 :=
  .composition (scratchRow (constantZero 2) R)
    ![NumberedWindowInternalSparsePair.pair,constantZero 2,constantZero 2]

/-- The all-input calibration of the physical scratch computation from its
explicit row update, keeping the exact original checker at malformed inputs. -/
def ExactAuxExchangeMemoCalibration : Prop :=
  ∀ (s : Settings) (base : Program 2) (R : Program 4), ActualTermExchange s base →
    StepCalibrated base R → ActualTermExchange s (selected R)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoTargets
