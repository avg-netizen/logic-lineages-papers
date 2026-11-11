module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathPathCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathFirstStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof (emptyRename)
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalParameterizedPathCheckerProof
open InternalParameterizedApplicationPathLiftSupportProof
open InternalListCodec InternalListCodecSupportProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion OriginalNonLambdaApplicationPath OriginalNonLambdaApplicationPathTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original positive checker binds its literal list and pair fields.
Its first edge and ordinary suffix retain the original witness and parameter. -/
theorem actualOriginalPositivePathFirstStepElimination :
    ActualOriginalPositivePathFirstStepElimination := by
  intro data oldStep body alpha Gamma x y pathCode parameter psi hp next
  let edge := edgeChecker data oldStep
  apply positiveConsCases edge x y pathCode parameter psi hp
  intro beta j Delta raw tail hj hc
  have hp' := renameInto hp j Delta hj
  rw [positiveRename] at hp'
  let qs : Fin 2 → Program 1 := Fin.cons InternalUnpair.left (Fin.cons InternalUnpair.right Fin.elim0)
  apply queryCases qs (Fin.cons raw Fin.elim0) (psi.relabel j)
  intro gamma q ys Theta hq hvalues
  have hleft : Nonempty (Derivation body Theta
      (graph1 InternalUnpair.left (ys 0) (raw.relabel q))) := by
    have h := hvalues 0
    rw [show qs (0 : Fin 2) = InternalUnpair.left from rfl] at h
    simpa only [consTermRename,emptyRename] using h
  have hright : Nonempty (Derivation body Theta
      (graph1 InternalUnpair.right (ys 1) (raw.relabel q))) := by
    have h := hvalues 1
    rw [show qs (1 : Fin 2) = InternalUnpair.right from rfl] at h
    simpa only [consTermRename,emptyRename] using h
  have hpair := reconstructPair (raw.relabel q) (ys 0) (ys 1) hleft hright
  have hc' := renameInto hc q Theta hq
  rw [graph2Rename] at hc'
  have hp'' := renameInto hp' q Theta hq
  rw [positiveRename] at hp''
  simp only [Term.relabel_relabel] at hc' hp''
  obtain ⟨heq⟩ := consEquation edge true (x.relabel (q ∘ j)) (y.relabel (q ∘ j))
    (pathCode.relabel (q ∘ j)) (raw.relabel q) (tail.relabel q) (ys 0) (ys 1)
    (parameter.relabel (q ∘ j)) hpair hc'
  obtain ⟨hp''⟩ := hp''
  have hparts := Derivation.implicationElimination (Derivation.conjunctionLeft heq) hp''
  have hfirst : Nonempty (Derivation body Theta
      (FirstStep data oldStep (x.relabel (q ∘ j)) (y.relabel (q ∘ j))
        (pathCode.relabel (q ∘ j)) (parameter.relabel (q ∘ j))
        (raw.relabel q) (tail.relabel q) (ys 0) (ys 1))) :=
    andIntro hc' (andIntro hpair
      (andIntro ⟨Derivation.conjunctionLeft hparts⟩ ⟨Derivation.conjunctionRight hparts⟩))
  have hinc : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
    intro h hh
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      hq (h.relabel j) (hj h hh)
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
    next gamma (q ∘ j) Theta hinc (raw.relabel q) (tail.relabel q) (ys 0) (ys 1) hfirst

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathFirstStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathFirstStepProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathFirstStepProof.actualOriginalPositivePathFirstStepElimination
