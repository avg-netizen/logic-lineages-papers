module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.LayerPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalQuotientComparisonProof (orRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalRawSyntaxTransport
open Continuation20261114.HeadWindowBooleanRange
open SyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consRange (raw head tail allowed out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hg : Nonempty (Derivation body Delta (graph2 allTypes out raw allowed))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  have hs := InternalRawListRecursionProof.consForward (constant 1 1) allStep raw head tail out (Fin.cons allowed Fin.elim0) hc hg
  apply InternalRawListRecursionProof.stepCases (constant 1 1) allStep out head tail (Fin.cons allowed Fin.elim0) _ hs
  intro beta j Theta old hj ht hstep
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at ht hstep
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hbool := atRawApply (tail.relabel j) (allowed.relabel j) old
    (belowRawAt (raw.relabel j) (tail.relabel j) ihj
      (InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (head.relabel j) (tail.relabel j) hcj)) ht
  have hright := Boolean.PointBindingProof.fromValue (.projection 1) ![head.relabel j,old,allowed.relabel j] old
    (projectionValue 1 ![head.relabel j,old,allowed.relabel j]) hbool
  have hrange := Boolean.LayerPointProof.bothAt (.composition TwoSol20261113.CalibratedPrimary.Membership.contains ![.projection 2,.projection 0])
    (.projection 1) ![head.relabel j,old,allowed.relabel j] hright
  exact Boolean.PointBindingProof.applyAt allStep ![head.relabel j,old,allowed.relabel j] (out.relabel j) hrange hstep

theorem nonzeroRange (raw allowed out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hg : Nonempty (Derivation body Delta (graph2 allTypes out raw allowed))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply Boolean.ListCasesProof.nonzeroCases raw _ hn
  intro beta j Theta head tail hj hc
  rw [booleanRename]
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hgj := renameInto hg j Theta hj
  rw [graph2Rename] at hgj
  exact consRange (raw.relabel j) head tail (allowed.relabel j) (out.relabel j) ihj hc hgj

theorem core (raw allowed out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hg : Nonempty (Derivation body Delta (graph2 allTypes out raw allowed))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hg0 := headTransport allTypes out raw z (Fin.cons allowed Fin.elim0) hz (withHyp hg A)
    obtain ⟨he⟩ := valueUnique allTypes out (suc z) ![z,allowed] hg0 (Types.RecursionProof.nilValue allowed)
    exact ⟨orRight he⟩
  · exact nonzeroRange raw allowed out (withHyp ih A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hg A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.CoreProof
