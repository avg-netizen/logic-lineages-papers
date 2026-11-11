module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathPathCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixNonzeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalParameterizedPathCheckerProof
open InternalListCodec InternalListCodecSupportProof
open InternalTagArithmeticSyntaxProof (eqn z suc sucRelabel zRelabel)
open InternalGraphCompositionFunctionalityProof
open OriginalVariableQuotientPathPathCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The ordinary and positive checkers use exactly the same original cons
clause. Bind the literal entry's selectors internally; keep code and tail. -/
theorem atCons (edge : Program 4) (x y code raw tail parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (hp : Nonempty (Derivation body Gamma (pathGraph edge x y code parameter))) :
    Nonempty (Derivation body Gamma (positiveGraph edge x y code parameter)) := by
  let qs : Fin 2 → Program 1 := Fin.cons InternalUnpair.left (Fin.cons InternalUnpair.right Fin.elim0)
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Delta hj hq
  rw [positiveRename]
  have hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (ys 0) (raw.relabel j))) := by
    have hvalue := hq 0
    rw [show qs (0 : Fin 2) = InternalUnpair.left from rfl] at hvalue
    simpa only [consTermRename,emptyRename] using hvalue
  have hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right (ys 1) (raw.relabel j))) := by
    have hvalue := hq 1
    rw [show qs (1 : Fin 2) = InternalUnpair.right from rfl] at hvalue
    simpa only [consTermRename,emptyRename] using hvalue
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hp' := renameInto hp j Delta hj
  rw [pathRename] at hp'
  have hpair := reconstructPair (raw.relabel j) (ys 0) (ys 1) hl hr
  obtain ⟨hf⟩ := pathCons edge (x.relabel j) (y.relabel j) (code.relabel j)
    (raw.relabel j) (tail.relabel j) (ys 0) (ys 1) (parameter.relabel j) hpair hc'
  obtain ⟨hb⟩ := positiveCons edge (x.relabel j) (y.relabel j) (code.relabel j)
    (raw.relabel j) (tail.relabel j) (ys 0) (ys 1) (parameter.relabel j) hpair hc'
  obtain ⟨hp'⟩ := hp'
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hb)
    (Derivation.implicationElimination (Derivation.conjunctionLeft hf) hp')⟩

/-- A nonzero code is reconstructed by the existing original list codec.
Only arithmetic case elimination is used; the path is never re-encoded. -/
theorem nonzero (edge : Program 4) (x y code parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (equal code z).not))
    (hp : Nonempty (Derivation body Gamma (pathGraph edge x y code parameter))) :
    Nonempty (Derivation body Gamma (positiveGraph edge x y code parameter)) := by
  rw [equalEqn] at hn
  apply nonzeroConsCases code _ hn
  intro beta j Delta raw tail hj hc
  rw [positiveRename]
  have hp' := renameInto hp j Delta hj
  rw [pathRename] at hp'
  exact atCons edge (x.relabel j) (y.relabel j) (code.relabel j) raw tail
    (parameter.relabel j) hc hp'

theorem actualOriginalSameCodeNonzeroPathPositive :
    OriginalSameCodeSuffixTargets.ActualOriginalSameCodeNonzeroPathPositive := by
  intro edge body alpha Gamma x y code parameter
  let P := (equal code z).not ⊓ pathGraph edge x y code parameter
  have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := nonzero edge x y code parameter (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixNonzeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixNonzeroProof
