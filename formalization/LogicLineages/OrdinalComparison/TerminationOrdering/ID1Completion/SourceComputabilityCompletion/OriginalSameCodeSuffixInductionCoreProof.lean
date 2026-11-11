module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixSpineCompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalParameterizedPathCheckerProof
open InternalParameterizedApplicationPathLiftSupportProof
open InternalListCodec InternalListCodecSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalClosedPrograms InternalClosedProgramsBindingProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalSameCodeSuffixInductionSyntaxProof OriginalSameCodeSuffixSpineCompositionProof
open OriginalVariableQuotientPathPathCoreProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem rowApply (edge : Program 4) (window : Program 1) (code x y parameter : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (spineRow edge window code)))
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (hp : Nonempty (Derivation body Gamma (positiveGraph edge x y code parameter))) :
    Nonempty (Derivation body Gamma (OriginalSpineGuardLeaf.spineAccepted x y code parameter)) := by
  have h := actualFiniteUniversalElimination body alpha 3 Gamma (spineBody edge window code)
    (fun i => emb (![x,y,parameter] i)) hrow
  rw [spineBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hpre⟩ := andIntro hw hp
  exact ⟨Derivation.implicationElimination h hpre⟩

theorem rightEndpoint (x vertex y code parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (equal vertex y)))
    (h : Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted x vertex code parameter))) :
    Nonempty (Derivation body Gamma (OriginalSpineGuardLeaf.spineAccepted x y code parameter)) := by
  apply graphInputTransport body alpha 4 Gamma
    (OrdinaryArithmetic.graphFormula (PositiveGuard.spineGuard BottomSpineMeasure.measure)) (suc z)
    (Fin.cons x (Fin.cons vertex (Fin.cons code (Fin.cons parameter Fin.elim0))))
    (Fin.cons x (Fin.cons y (Fin.cons code (Fin.cons parameter Fin.elim0)))) _ h
  intro i
  exact Fin.cases (UniformCertificateCompletion.PathSupportProof.equalReflexive x) (Fin.cases he
    (Fin.cases (UniformCertificateCompletion.PathSupportProof.equalReflexive code) (Fin.cases (UniformCertificateCompletion.PathSupportProof.equalReflexive parameter) (fun q => Fin.elim0 q)))) i

/-- A tail is either literal nil, where its endpoint equality transports the
first guard, or the same nonempty code, where the induction row composes it. -/
theorem firstThenTail (edge : Program 4) (window : Program 1)
    (x vertex y code first tail parameter : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (spineRow edge window tail)))
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (hf : Nonempty (Derivation body Gamma (OriginalSpineGuardLeaf.spineAccepted x vertex first parameter)))
    (ht : Nonempty (Derivation body Gamma (pathGraph edge vertex y tail parameter))) :
    Nonempty (Derivation body Gamma (OriginalSpineGuardLeaf.spineAccepted x y code parameter)) := by
  let P := equal tail z
  apply formulaCases P
  · have he : Nonempty (Derivation body (P :: Gamma) (eqn tail z)) := by
      rw [← equalEqn]
      exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hnil := checkerCodeTransport edge false vertex y tail z parameter he (withHyp ht P)
    have hxy := nilRecover edge vertex y parameter hnil
    have hcode := spineRecode BottomSpineMeasure.measure x vertex first code parameter (withHyp hf P)
    exact rightEndpoint x vertex y code parameter hxy hcode
  · have hn : Nonempty (Derivation body (P.not :: Gamma) (equal tail z).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hpos := OriginalSameCodeSuffixNonzeroProof.nonzero edge vertex y tail parameter hn (withHyp ht P.not)
    have hwv := BottomDescentStepProof.windowChange window (suc z) x vertex parameter (withHyp hw P.not)
    have htail := rowApply edge window tail vertex y parameter (withHyp hrow P.not) hwv hpos
    exact spineTrans BottomSpineMeasure.measure x vertex y first tail code parameter (withHyp hf P.not) htail

theorem consCore (data : Data) (window : Program 1) (oldStep : Program 4)
    (hguard : OriginalQuotientSpine.QuotientHasSpineGuard data window oldStep)
    (x y code raw tail parameter : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (spineRow (edgeChecker data oldStep) window tail)))
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (hp : Nonempty (Derivation body Gamma (positiveGraph (edgeChecker data oldStep) x y code parameter))) :
    Nonempty (Derivation body Gamma (OriginalSpineGuardLeaf.spineAccepted x y code parameter)) := by
  apply checkerConsFieldsCases (edgeChecker data oldStep) true x y code raw tail parameter _ hc hp
  intro beta j Delta vertex certificate hj he ht
  simp only [OriginalSpineGuardLeaf.spineAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]
  have hrow' := renameInto hrow j Delta hj
  rw [spineRowRename] at hrow'
  have hw' := renameInto hw j Delta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  obtain ⟨hi⟩ := hguard body beta Delta (x.relabel j) vertex certificate (parameter.relabel j)
  obtain ⟨hpre⟩ := andIntro hw' he
  have hf : Nonempty (Derivation body Delta
      (OriginalSpineGuardLeaf.spineAccepted (x.relabel j) vertex certificate (parameter.relabel j))) :=
    ⟨Derivation.implicationElimination hi hpre⟩
  exact firstThenTail (edgeChecker data oldStep) window (x.relabel j) vertex (y.relabel j)
    (code.relabel j) certificate (tail.relabel j) (parameter.relabel j) hrow' hw' hf ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionCoreProof
