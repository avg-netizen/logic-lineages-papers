module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)

def hasLeast {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  existsOne (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j) (.var (.inr 0)))

def ExactSeedInComputedPool : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed vertices pool : OTerm α),
    let cover := unary (scratchVertices C s) vertices seed
    let members := programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed]
    Nonempty (Derivation body Γ
      (((cover ⊓ members) ⊓ memberGraph vertices seed).imp (memberGraph pool seed)))

/-- Given the actual parsed lexical context and the original cover projection,
success of the complete packed least is exactly occurrence of the original seed. -/
def ExactPackedDomain : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed payload vertices : OTerm α),
    let parsed := programGraph contextOption (suc payload) ![ctx,ty,seed]
    let cover := unary (scratchVertices C s) vertices seed
    Nonempty (Derivation body Γ ((parsed ⊓ cover).imp
      (equivalent (hasLeast C X W s ctx ty seed) (memberGraph vertices seed))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
