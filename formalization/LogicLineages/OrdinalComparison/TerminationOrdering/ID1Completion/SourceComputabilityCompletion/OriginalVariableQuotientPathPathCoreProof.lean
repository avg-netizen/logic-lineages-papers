module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathPathCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableQuotientPath OriginalVariableQuotientPathEdgeProof
open OriginalVariableRepresentative (selectedData windowGraph)
open InternalParameterizedCanonicalResultFold (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalParameterizedPathCheckerProof
open InternalParameterizedApplicationPathLiftSupportProof
open InternalListCodec InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalTagArithmeticSyntaxProof (OTerm z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Original raw-list reconstruction at every nonzero code, with both
original selector outputs bound internally. No parse-success assumption. -/
theorem nonzeroConsCases (code : OTerm α) (psi : Formula α)
    (hn : Nonempty (Derivation body Gamma (eqn code z).not))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (raw tail : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (consGraph (code.relabel j) raw tail)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 2 → Program 1 := Fin.cons headCode (Fin.cons tailCode Fin.elim0)
  apply queryCases qs (Fin.cons code Fin.elim0) _
  intro β j ys Delta hj hq
  have hn' := renameInto hn j Delta hj
  rw [nonzeroRename] at hn'
  have hh : Nonempty (Derivation body Delta (unaryGraph headCode (ys 0) (code.relabel j))) := by
    have hvalue := hq 0
    rw [show qs (0 : Fin 2) = headCode from rfl] at hvalue
    simpa only [consTermRename,emptyRename] using hvalue
  have ht : Nonempty (Derivation body Delta (unaryGraph tailCode (ys 1) (code.relabel j))) := by
    have hvalue := hq 1
    rw [show qs (1 : Fin 2) = tailCode from rfl] at hvalue
    simpa only [consTermRename,emptyRename] using hvalue
  exact next β j Delta (ys 0) (ys 1) hj
    (reconstructNonzero (code.relabel j) (ys 0) (ys 1) hn' hh ht)

/-- Invert an original cons checker after internally binding the original
entry's left vertex and right certificate. The tail remains the literal
ordinary path checker at the SAME symbolic parameter. -/
theorem checkerConsFieldsCases (edge : Program 4) (positive : Bool)
    (x y code raw tail parameter : OTerm α) (psi : Formula α)
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (hp : Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) x y code parameter)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (vertex certificate : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (edgeGraph edge (x.relabel j) vertex certificate (parameter.relabel j))) →
      Nonempty (Derivation body Delta (pathGraph edge vertex (y.relabel j) (tail.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 2 → Program 1 := Fin.cons InternalUnpair.left (Fin.cons InternalUnpair.right Fin.elim0)
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro β j ys Delta hj hq
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
  simp only [checkerRename,sucRelabel,zRelabel] at hp'
  obtain ⟨hi⟩ := consEquation edge positive (x.relabel j) (y.relabel j) (code.relabel j)
    (raw.relabel j) (tail.relabel j) (ys 0) (ys 1) (parameter.relabel j)
    (reconstructPair (raw.relabel j) (ys 0) (ys 1) hl hr) hc'
  obtain ⟨hp'⟩ := hp'
  have hparts := Derivation.implicationElimination (Derivation.conjunctionLeft hi) hp'
  exact next β j Delta (ys 0) (ys 1) hj
    ⟨Derivation.conjunctionLeft hparts⟩ ⟨Derivation.conjunctionRight hparts⟩

theorem bottomConsContradiction (data : Data) (window : Program 1) (oldStep : Program 4)
    (positive : Bool) (x y code raw tail parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomAccepted x)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (hp : Nonempty (Derivation body Gamma
      (checkerGraph (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
        positive (suc z) x y code parameter))) :
    Nonempty (Derivation body Gamma ⊥) := by
  apply checkerConsFieldsCases
    (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep)) positive
    x y code raw tail parameter _ hc hp
  intro β j Delta vertex certificate hj he ht
  have hw' := renameInto hw j Delta hj
  have hb' := renameInto hb j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [bottomAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hb'
  exact bottomEdgeContradiction data window oldStep (x.relabel j) vertex certificate
    (parameter.relabel j) hw' hb' he

/-- An ordinary path from literal bottom is either the original nil code,
or its first actual edge contradicts the paid bottom terminality law. -/
theorem bottomPathIdentity (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y code parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomAccepted x)))
    (hp : Nonempty (Derivation body Gamma
      (pathGraph (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
        x y code parameter))) :
    Nonempty (Derivation body Gamma (equal y x)) := by
  let edge := edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep)
  let P := eqn code z
  apply formulaCases P
  · have hz := checkerCodeTransport edge false x y code z parameter
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hp P)
    obtain ⟨he⟩ := nilRecover edge x y parameter hz
    rw [equalEqn] at he ⊢
    exact ⟨symm he⟩
  · have hn : Nonempty (Derivation body (P.not :: Gamma) P.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hw0 := withHyp hw P.not
    have hb0 := withHyp hb P.not
    have hp0 := withHyp hp P.not
    apply nonzeroConsCases code _ hn
    intro β j Delta raw tail hj hc
    simp only [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
    have hw' := renameInto hw0 j Delta hj
    have hb' := renameInto hb0 j Delta hj
    have hp' := renameInto hp0 j Delta hj
    simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
    simp only [bottomAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hb'
    rw [pathRename] at hp'
    obtain ⟨hc⟩ := bottomConsContradiction data window oldStep false (x.relabel j) (y.relabel j)
      (code.relabel j) raw tail (parameter.relabel j) hw' hb' hc hp'
    exact ⟨Derivation.explosion hc⟩

theorem bottomPositiveContradiction (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y code parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomAccepted x)))
    (hp : Nonempty (Derivation body Gamma
      (positiveGraph (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
        x y code parameter))) :
    Nonempty (Derivation body Gamma ⊥) := by
  apply positiveConsCases (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
    x y code parameter _ hp
  intro β j Delta raw tail hj hc
  have hw' := renameInto hw j Delta hj
  have hb' := renameInto hb j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [bottomAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hb'
  rw [positiveRename] at hp'
  exact bottomConsContradiction data window oldStep true (x.relabel j) (y.relabel j)
    (code.relabel j) raw tail (parameter.relabel j) hw' hb' hc hp'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathPathCoreProof
