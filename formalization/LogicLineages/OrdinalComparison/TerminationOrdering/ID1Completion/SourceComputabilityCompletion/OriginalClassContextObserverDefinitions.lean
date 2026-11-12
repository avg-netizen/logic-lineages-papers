module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserver
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2 pairOf leftOf rightOf)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- [packed,parameter] becomes the actual original Object, then undergoes
literal raw erasure. No new canonical representative occurs in this AST. -/
def erasedObject : Program 2 :=
  .composition OriginalRawObjectTransport.eraseObjectRaw
    (fun _ : Fin 1 => pairOf (rightOf (.projection 1)) (.projection 0))
def parentParameter : Program 2 :=
  pairOf (leftOf (.projection 1)) (leftOf erasedObject)
def erasedKey (R : Program 2) : Program 2 :=
  .composition R ![rightOf erasedObject,parentParameter]
def erasedRank : Program 2 :=
  .composition OriginalRawSyntaxTransport.variableRankPackedRaw
    (fun _ : Fin 1 => rightOf erasedObject)
def observerTest (R : Program 2) : Program 3 :=
  InternalAcceptance.conjunction
    (OriginalActiveClassKernel.keyTest (erasedKey R))
    (OriginalActiveClassKernel.keyTest erasedRank)
/-- Refine only active seeds in a genuine nonempty original context. All
empty-context, inactive and malformed behavior is inherited unchanged. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Program 3 :=
  InternalAcceptance.branch (rightOf (.projection 2)) P
    (InternalAcceptance.branch
      (.composition (OriginalActiveObservedClass.activation p H G W)
        ![.projection 0,.projection 2])
      P (InternalAcceptance.conjunction P (observerTest p.base.oldRepresentative)))
/-- Concrete internal observer exposure only. This is not full canonical
cancellation, final-fold class preservation or internal I/C. -/
def HitLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter gamma tail key rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (OriginalActiveObservedClass.activation p H G W)
        InternalOriginalStepGuard.one seed parameter ⊓
      (InternalControlGraph.programGraph InternalUnpair.right gamma
          (Fin.cons parameter Fin.elim0) ⊓
        ((equal gamma (OrdinaryArithmetic.succTerm tail)) ⊓
          OriginalTransparentMinimum.graph3 (classTest p H G W P)
            InternalOriginalStepGuard.one seed candidate parameter))).imp
      (((graph2 (erasedKey p.base.oldRepresentative) key seed parameter).iff
        (graph2 (erasedKey p.base.oldRepresentative) key candidate parameter)) ⊓
        ((graph2 erasedRank rank seed parameter).iff
          (graph2 erasedRank rank candidate parameter)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserver
