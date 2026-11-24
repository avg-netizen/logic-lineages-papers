module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalRawListRecursion (recGraph consStep)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

abbrev Report {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) : Prop :=
  Nonempty (Derivation B Γ f)

def selectField : Program 3 := .composition (field 1) ![.projection 0]
def selectMember : Program 3 := .composition scratchMember ![.projection 2, selectField]
def prependRow : Program 3 := .composition consCode ![.projection 0, .projection 1]
def rowStep (takeMember : Bool) : Program 3 :=
  if takeMember then branch (normalize selectMember) (.projection 1) prependRow
  else branch (normalize selectMember) prependRow (.projection 1)

abbrev zeroBase : Program 1 := constantZero 1
abbrev rowCell {α : Type} (code head tail : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph consCode code ![head,tail]

def ExactOpenOriginRowStep : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h rest pool dom out : OrdinaryArithmetic.Term α),
    Report B Γ (unary (field 1) dom h) →
    let q := programGraph scratchMember (suc z) ![pool,dom]
    let l := programGraph (rowStep true) out ![h,rest,pool]
    let r := programGraph (rowStep false) out ![h,rest,pool]
    let c := rowCell out h rest
    let e := eqn out rest
    (Report B Γ q → ((Report B Γ l ↔ Report B Γ c) ∧ (Report B Γ r ↔ Report B Γ e))) ∧
    (Report B Γ q.not → ((Report B Γ l ↔ Report B Γ e) ∧ (Report B Γ r ↔ Report B Γ c)))

def ExactOpenOriginRowFilterNil : Prop :=
  ∀ (side : Bool) (B : Positive (Fin 1)) (α : Type) (pool out : OrdinaryArithmetic.Term α),
    Report B [] ((recGraph zeroBase (rowStep side) out z ![pool]).iff
      (programGraph zeroBase out ![pool]))

def ExactOpenOriginRowFilterCons : Prop :=
  ∀ (side : Bool) (B : Positive (Fin 1)) (α : Type)
    (code head tail pool out : OrdinaryArithmetic.Term α),
    Report B [] ((rowCell code head tail).imp
      ((recGraph zeroBase (rowStep side) out code ![pool]).iff
        (consStep zeroBase (rowStep side) out head tail ![pool])))

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets
