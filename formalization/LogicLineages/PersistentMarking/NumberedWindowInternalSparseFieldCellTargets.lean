module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCell
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparseFieldCell
open NumberedWindowInternalSparseFieldInductionTargets (consGraph someCons)

def AllInputCell : Prop :=
  chosenCell 0 = none ∧ ∀ n, chosenCell (n+1) = NumberedWindowPairAlgorithm.decode n

/-- Covers every original cursor/accumulator state, including a prior
failure, a successful nil cursor and a nonzero malformed field cell. -/
def ActualFieldStep : Prop :=
  ∀ s, chosenStep s = NumberedWindowFieldAlgorithm.step s

def certifiedCell {α : Type} (n h t : OTerm α) : Formula α :=
  programGraph cellGood (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![n] ⊓
    (programGraph cellHead h ![n] ⊓ programGraph cellTail t ![n])

/-- Original field constructor and selected parser agree in actual
object-language proofs on every free object term, without reflection. -/
def OpenCellSuccess : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t : OTerm α),
    let g := consGraph n h t
    let s := certifiedCell n h t
    Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def OpenCellFailure : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α),
    let g := programGraph cellGood OrdinaryArithmetic.zeroTerm ![n]
    let s := (someCons n).not
    Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

/-- Nil causes no cell recognition and has no actual cons witness. Its
successful terminal-state behavior is stated separately in ActualFieldStep. -/
def OpenNilCell : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type),
    let z : OTerm α := OrdinaryArithmetic.zeroTerm
    Nonempty (Derivation body []
      (programGraph cellGood z ![z] ⊓ (someCons z).not))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellTargets
