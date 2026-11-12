module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumCoherenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors
open OriginalActiveClassKernel (Domain)

/-- The literal relation accepted by the actual all-position, rank-observed
minimum. In particular the observer is OUTSIDE the active kernel. -/
def Accepted {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
 (W : Program 2) (P : Program 3) (seed candidate parameter : OTerm alpha) : Formula alpha :=
 graph3 (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
   (OriginalActiveObservedClass.classTest p H G W OriginalRawSyntaxTransport.variableRankPackedRaw
     (OriginalClassContextAllPositionSelection.classTest p H G W P)))
   InternalOriginalStepGuard.one seed candidate parameter

/-- Equal actual acceptance rows at ONE parameter; no assumed row oracle. -/
def RowCoherence : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (seed other candidate parameter : OTerm alpha),
 Nonempty (Derivation body Delta
  ((Domain p H G W seed parameter ⊓ Accepted p H G W P seed other parameter).imp
    ((Accepted p H G W P seed candidate parameter).iff (Accepted p H G W P other candidate parameter))))

/-- SAME actual once-minimum, not the later traversal or canonical Object. -/
def MinimumCoherence : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (seed other out otherOut parameter : OTerm alpha),
 let R := (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative
 Nonempty (Derivation body Delta
  ((Domain p H G W seed parameter ⊓ (Accepted p H G W P seed other parameter ⊓
    (graph2 R out seed parameter ⊓ graph2 R otherOut other parameter))).imp (equal out otherOut)))

def MinimumIdempotence : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (seed out parameter : OTerm alpha),
 let R := (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative
 Nonempty (Derivation body Delta
  ((Domain p H G W seed parameter ⊓ graph2 R out seed parameter).imp (graph2 R out out parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumCoherenceTargets
