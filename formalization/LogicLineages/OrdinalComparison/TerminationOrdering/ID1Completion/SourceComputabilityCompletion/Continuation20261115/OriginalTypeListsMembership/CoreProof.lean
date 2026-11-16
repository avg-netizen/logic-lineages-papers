module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalContextInsertionSyntaxProof (lengthRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def rows : Program 2 := .composition OriginalTypeListsEnumeration.cross
  ![.projection 1,OriginalTypeListsEnumeration.enumeration]

theorem successorCore (bound allowed out types len : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (row bound)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration out (suc bound) allowed)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types))) :
    Nonempty (Derivation body Delta (result (suc bound) allowed out types len)) := by
  let qs : Fin 2 → Program 2 := ![OriginalTypeListsEnumeration.enumeration,rows]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs ![bound,allowed] _
  intro beta j ys Theta hj hq
  have hxs : (fun i : Fin 2 => (![bound,allowed] i).relabel j) =
      ![bound.relabel j,allowed.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs] at hq
  rw [resultRename]
  simp only [sucRelabel]
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  rw [rowRename] at ihj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,sucRelabel] at hgj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  rw [lengthRename] at hlj
  have hc := binaryRecover OriginalTypeListsEnumeration.cross (.projection 1) OriginalTypeListsEnumeration.enumeration
    (ys 1) (allowed.relabel j) (ys 0) ![bound.relabel j,allowed.relabel j]
    (hq 1) (projectionValue 1 ![bound.relabel j,allowed.relabel j]) (hq 0)
  have ho := (OriginalTypeListsEnumeration.StatementChecks.exactSuccessor body beta Theta
    (bound.relabel j) (allowed.relabel j) (ys 0) (ys 1) (out.relabel j) (hq 0) hc).mp hgj
  exact StepProof.atLists (bound.relabel j) (allowed.relabel j) (out.relabel j)
    (types.relabel j) (len.relabel j) (ys 0) (ys 1) ihj (hq 0) hc ho hlj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CoreProof
