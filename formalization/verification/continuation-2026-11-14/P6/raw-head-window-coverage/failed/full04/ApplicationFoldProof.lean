module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ConstructorFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open SupportProof FoldCoreProof

open ConstructorFoldProof

def appTransform : Program 2 := pairOf (constant 2 4) (pairOf (.projection 1) (.projection 0))
def rowMember : Program 3 := .composition contains
  ![.composition OriginalSourceHeads.appRow ![.projection 2,.projection 1],.projection 0]

theorem pairValue {m : Nat} (i j : Fin m) (payload sigma tau : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hi : xs i = sigma) (hj : xs j = tau)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau))) :
    Nonempty (Derivation body Delta (programGraph (pairOf (.projection i) (.projection j)) payload xs)) := by
  apply binaryValue InternalPairing.pairing (.projection i) (.projection j) payload sigma tau xs hp
  · simpa only [hi] using (projectionValue (body := body) (Gamma := Delta) i xs)
  · simpa only [hj] using (projectionValue (body := body) (Gamma := Delta) j xs)

theorem appValue {m : Nat} (i j : Fin m) (image payload sigma tau : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hi : xs i = sigma) (hj : xs j = tau)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral 4) payload))) :
    Nonempty (Derivation body Delta (programGraph
      (pairOf (constant m 4) (pairOf (.projection i) (.projection j))) image xs)) :=
  binaryValue InternalPairing.pairing (constant m 4) (pairOf (.projection i) (.projection j)) image
    (numeral 4) payload xs hh (constantValue 4 xs) (pairValue i j payload sigma tau xs hi hj hp)

theorem rowHit : Hit body OriginalSourceHeads.appStep appTransform := by
  intro alpha Delta head rest out image params ht hs
  apply programCases InternalPairing.pairing (Fin.cons (params 0) (Fin.cons head Fin.elim0)) _
  intro beta j Theta payload hj hp
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hp
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have htj := renameInto ht j Theta hj
  have hsj := renameInto hs j Theta hj
  simp only [programRename,InternalRecursionGraphStepSyntaxProof.consTermRename] at htj hsj
  let xs : Fin 2 → OTerm beta := Fin.cons (head.relabel j) (fun i => (params i).relabel j)
  have hi := pairValue (1 : Fin 2) 0 payload ((params 0).relabel j) (head.relabel j) xs rfl rfl hp
  have hh := binaryRecover InternalPairing.pairing (constant 2 4) (pairOf (.projection 1) (.projection 0))
    (image.relabel j) (numeral 4) payload xs htj (constantValue 4 xs) hi
  let ys : Fin 3 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (rest.relabel j) (fun i => (params i).relabel j))
  exact consHead _ (.projection 1) (out.relabel j) (image.relabel j) ys
    (appValue 2 0 (image.relabel j) payload ((params 0).relabel j) (head.relabel j) ys rfl rfl hp hh) hsj

theorem rowTail : Tail body OriginalSourceHeads.appStep := by
  intro alpha Delta head rest out image params hm hs
  exact consTail _ (.projection 1) out rest image (Fin.cons head (Fin.cons rest params))
    (projectionValue 1 (Fin.cons head (Fin.cons rest params))) hm hs

theorem rowCoverage (types sigma tau image payload out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.appRow out types sigma)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral 4) payload)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) types tau))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image)) :=
  FoldProof.coverage (constant 1 0) OriginalSourceHeads.appStep appTransform rowHit rowTail
    types tau image out (Fin.cons sigma Fin.elim0)
    (appValue 1 0 image payload sigma tau (Fin.cons tau (Fin.cons sigma Fin.elim0)) rfl rfl hp hh) hm hf

theorem outerHit : RelationFoldCoreProof.Hit body OriginalSourceHeads.appsStep rowMember := by
  intro alpha Delta head rest out image params ht hs
  apply programCases OriginalSourceHeads.appRow (Fin.cons (params 0) (Fin.cons head Fin.elim0)) _
  intro beta j Theta row hj hr
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have htj := renameInto ht j Theta hj
  have hsj := renameInto hs j Theta hj
  simp only [programRename,InternalRecursionGraphStepSyntaxProof.consTermRename,GuardedSourceSyntaxProof.numeralRename] at htj hsj
  let xs : Fin 3 → OTerm beta := Fin.cons (image.relabel j) (Fin.cons (head.relabel j) (fun i => (params i).relabel j))
  have hrow := binaryValue OriginalSourceHeads.appRow (.projection 2) (.projection 1) row
    ((params 0).relabel j) (head.relabel j) xs hr (projectionValue 2 xs) (projectionValue 1 xs)
  have hm := binaryRecover contains (.composition OriginalSourceHeads.appRow ![.projection 2,.projection 1])
    (.projection 0) (numeral 1) row (image.relabel j) xs htj hrow (projectionValue 0 xs)
  let ys : Fin 3 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (rest.relabel j) (fun i => (params i).relabel j))
  have hrow' := binaryValue OriginalSourceHeads.appRow (.projection 2) (.projection 0) row
    ((params 0).relabel j) (head.relabel j) ys hr (projectionValue 2 ys) (projectionValue 0 ys)
  exact appendLeft (.composition OriginalSourceHeads.appRow ![.projection 2,.projection 0]) (.projection 1)
    (out.relabel j) row (image.relabel j) ys hrow' hm hsj

theorem outerTail : RelationFoldCoreProof.Tail body OriginalSourceHeads.appsStep := by
  intro alpha Delta head rest out image params hm hs
  exact appendRight _ (.projection 1) out rest image (Fin.cons head (Fin.cons rest params))
    (projectionValue 1 (Fin.cons head (Fin.cons rest params))) hm hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ApplicationFoldProof
