module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (strictLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)

/-- At a successful actual context and the actual computed pool, the complete
optional packed output is exactly the original ordered minimum on that pool. -/
def ExactOpenPackedPoolMinimum : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed payload pool out : OTerm α),
    let tape := ![ctx,ty,seed]
    Nonempty (Derivation body Γ
      ((programGraph contextOption (suc payload) tape ⊓ programGraph (membersAtSeed C X W s) pool tape).imp
        (equivalent (programGraph (packedLeastProgram C X W s) out tape)
          (unary scratchMinimum out pool))))

/-- Every supplied genuine member of the very same computed pool bounds the
successful packed least. No context decoding or validity premise is supplied. -/
def ExactOpenPackedLeastLowerBound : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed pool candidate minimum : OTerm α),
    Nonempty (Derivation body Γ
      ((leastGraph C X W s ctx ty seed minimum ⊓
        (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool candidate)).imp
          (strictLess candidate minimum).not))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets
