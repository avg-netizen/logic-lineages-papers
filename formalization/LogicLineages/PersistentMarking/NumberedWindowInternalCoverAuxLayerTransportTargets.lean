module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverAuxApplicationsTargets (auxApplications)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)

/-- The original factored auxiliary graph; no new compiled callback. -/
abbrev auxReport {α : Type} (out K T : OTerm α) : Formula α :=
  programGraph auxApplications out ![K,T]

abbrev auxOriginRow {α : Type} (K T key d c f a : OTerm α) : Formula α :=
  memberGraph K d ⊓ (memberGraph K c ⊓
    (memberGraph T f ⊓ (memberGraph T a ⊓ eqn (auxiliaryTerm d c f a) key)))

abbrev auxOriginMatrix {α : Type} (K T key : OTerm α) : Formula (α ⊕ Fin 4) :=
  auxOriginRow (K.relabel Sum.inl) (T.relabel Sum.inl) (key.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

abbrev auxOrigin {α : Type} (K T key : OTerm α) : Formula α :=
  block (auxOriginMatrix K T key)

/-- The original physical auxiliary occurrence retains its two actual
annotation inputs, two actual child inputs, and same sparse tag-six key. -/
def ExactOpenCoverAuxLayerOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out K T key : OTerm α),
  Nonempty (Derivation body Γ (auxReport out K T)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (auxOrigin K T key))

/-- Both original layer reports share the same K scratch on both type
axes. One actual child inclusion is used on both child axes. -/
def ExactOpenCoverAuxLayerTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (old next K T T' key : OTerm α),
  Nonempty (Derivation body Γ (auxReport old K T)) →
  Nonempty (Derivation body Γ (auxReport next K T')) →
  Nonempty (Derivation body Γ (axisInclusion T T')) →
  Nonempty (Derivation body Γ (memberGraph old key)) →
  Nonempty (Derivation body Γ (memberGraph next key))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportTargets
