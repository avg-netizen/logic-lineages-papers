module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocks (block)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitter

def consTerm {α : Type} (head tail : OTerm α) : OTerm α :=
  OrdinaryArithmetic.succTerm (pairTerm head tail)

def packedFreeTerm {α : Type} (ctx dom name : OTerm α) : OTerm α :=
  let z : OTerm α := OrdinaryArithmetic.zeroTerm
  let variablePayload := consTerm z (consTerm dom (consTerm name z))
  consTerm (numeral 3) (consTerm ctx (consTerm dom (consTerm variablePayload z)))

/-- Genuine exact arithmetic graph equation at arbitrary open terms. No
canonicality or valid code assertion is smuggled into the raw arguments. -/
def ExactPackedFreeEmitterGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (u c t n : OTerm α),
    let g := programGraph packedEmitter u ![c,t,n]
    let equation := equal u (packedFreeTerm c t n)
    Nonempty (Derivation body Γ (g.imp equation ⊓ equation.imp g))

/-- Fixed first-order block: packed context, domain type code and fresh
name. The same original q is relabelled over all three witnesses. -/
def shapeAt {α : Type} (p : Selectors) (q u : OTerm α) : Formula α :=
  let q' := q.relabel (Sum.inl : α → α ⊕ Fin 3)
  let u' := u.relabel (Sum.inl : α → α ⊕ Fin 3)
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  block (programGraph p.context c ![q'] ⊓
    (programGraph p.domain t ![q'] ⊓ (programGraph p.name n ![q'] ⊓
      equal u' (packedFreeTerm c t n))))

/-- Only this actual a's graph produces the open shape. All leaves can
be arbitrary original Programs in the structural proof. Source calibration
later selects the original four at the same literal instance of a. -/
def ExactSelectedFreshOpenShape : Prop :=
  ∀ (p : Selectors) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (q u : OTerm α),
      Nonempty (Derivation body Γ (freshAt (chooseFresh p) q u)) →
      Nonempty (Derivation body Γ (shapeAt p q u))

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectTargets
