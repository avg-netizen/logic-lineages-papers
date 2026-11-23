module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)

def agreementBody {α : Type} (left right : OTerm α) : Formula (α ⊕ Fin 3) :=
  let l := left.relabel (Sum.inl : α → α ⊕ Fin 3)
  let r := right.relabel (Sum.inl : α → α ⊕ Fin 3)
  let needle : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  (counted l needle lc ⊓ counted r needle rc).imp (eqn lc rc)

def agreement {α : Type} (left right : OTerm α) : Formula α :=
  allBlock (agreementBody left right)

/-- Both count reports are on the exact two operands of the actual
literal accepting permutation graph. All object needles and both actual
outputs are universally bound, including needles outside both lists. -/
def ExactOpenLiteralCountAgreement : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (left right : OTerm α),
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) →
    Nonempty (Derivation B Γ (agreement left right))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
