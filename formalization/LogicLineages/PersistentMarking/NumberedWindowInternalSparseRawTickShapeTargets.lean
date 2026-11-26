module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseRawTick (liveTick chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)

/-- Object-language reachable scratch shape. Both witnesses are bound by
actual object quantifiers (flag outermost, frame innermost): the term is
the literal two-field scratch and its flag or its frame is zero. Nothing
is asserted about the other component: it need not be a Boolean flag, a
decodable frame, or a typed raw triple. -/
def goodState {α : Type} (out : OTerm α) : Formula α :=
  let o : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := (out.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  let f : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let F : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  existsOne (existsOne (eqn o (stateTerm f F) ⊓ (eqn f z ⊔ eqn F z)))

/-- Every output of the actual live dispatcher on ANY ternary tape has
the reachable shape. The tape entries are arbitrary open terms: no raw
triple, tag, typing or callback semantics is assumed, and both callback
programs are arbitrary. -/
def ExactOpenLiveTickShape : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (out : OTerm α)
    (xs : Fin 3 → OTerm α),
    Nonempty (Derivation body []
      ((programGraph (liveTick p other) out xs).imp (goodState out)))

/-- One actual tick from an arbitrary pack-shaped scratch reaches the
shape. The input flag and frame are arbitrary open terms and carry no
prior shape premise; the input is NOT generalized to malformed scratch
bytes, which a terminal selector would return unchanged. -/
def ExactOpenTickShape : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (flag frame out : OTerm α),
    Nonempty (Derivation body []
      ((programGraph (chosenTick p other) out ![stateTerm flag frame]).imp (goodState out)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTargets
