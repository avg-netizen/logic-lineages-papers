module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeFieldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeFullFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalConstructorShape OriginalConstructorShapeSyntaxProof
open OriginalConstructorShapeApplicationProof
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalResultFold (sourcePremises foldGraph)
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Recover root fields from full mark preservation. The mark is obtained by
internal Program totality, and its original pair projections establish both
directions without an extra supplied mark premise. -/
theorem fieldsFromMarkPreservation (data : Data) (window : Program 1)
    (hfull : FullFoldMarkPreservation data window) : FullFoldRootFields data window := by
  intro body alpha Delta out input typeCode parameter value domain
  let P := windowGraph window input parameter ⊓
    (sourcePremises data input typeCode parameter ⊓ foldGraph data out input parameter)
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hresult : Nonempty (Derivation body (P :: Delta)
      (((tagGraph value out).iff (tagGraph value input)) ⊓
        ((applicationShape domain out).iff (applicationShape domain input)))) := by
    apply programCases mark (Fin.cons input Fin.elim0) _
    intro beta j Theta code hj hm
    rw [fieldsIffRename]
    have hw' := renameInto (andLeft hp) j Theta hj
    have hs' := renameInto (andLeft (andRight hp)) j Theta hj
    have hn' := renameInto (andRight (andRight hp)) j Theta hj
    simp only [OriginalConstructorShape.windowGraph,OriginalVariableRepresentative.windowGraph,
      graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
    rw [sourcePremisesRename] at hs'
    rw [foldGraphRename] at hn'
    simp only [consTermRename,emptyRename] at hm
    have hinput : Nonempty (Derivation body Theta (markGraph code (input.relabel j))) := hm
    obtain ⟨hlaw⟩ := hfull body beta Theta (out.relabel j) (input.relabel j)
      (typeCode.relabel j) (parameter.relabel j) code
    obtain ⟨hpre⟩ := andIntro hw' (andIntro hs' hn')
    have hiff := Derivation.implicationElimination hlaw hpre
    obtain ⟨hinputProof⟩ := hinput
    have hout : Nonempty (Derivation body Theta (markGraph code (out.relabel j))) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hiff) hinputProof⟩
    exact andIntro
      (sharedTagIff code (out.relabel j) (input.relabel j) (value.relabel j) hout ⟨hinputProof⟩)
      (sharedApplicationIff code (out.relabel j) (input.relabel j) (domain.relabel j) hout ⟨hinputProof⟩)
  obtain ⟨hresult⟩ := hresult
  exact ⟨Derivation.implicationIntroduction hresult⟩

theorem fullFoldRootFields (data : Data) (window : Program 1) :
    FullFoldRootFields (selectedData data window) window :=
  fieldsFromMarkPreservation (selectedData data window) window
    (OriginalConstructorShapeFullFoldProof.fullFoldMarkPreservation data window)

theorem actualOriginalConstructorShapeRootFields :
    OriginalConstructorShapeTargets.ActualOriginalConstructorShapeRootFields :=
  fullFoldRootFields

/-- Both raw sources reflect through their COMMON actual canonical output.
The resulting equivalences compare every symbolic constructor tag and the
original application domain, without asserting equality of child components. -/
theorem actualOriginalCanonicalRootComparison :
    OriginalConstructorShapeTargets.ActualOriginalCanonicalRootComparison := by
  intro data window body alpha Delta out left right leftType rightType parameter value domain
  let selected := selectedData data window
  let P := windowGraph window left parameter ⊓
    (windowGraph window right parameter ⊓
      (sourcePremises selected left leftType parameter ⊓
        (sourcePremises selected right rightType parameter ⊓
          (foldGraph selected out left parameter ⊓ foldGraph selected out right parameter))))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 := andRight hp
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  obtain ⟨hlaw⟩ := fullFoldRootFields data window body alpha (P :: Delta)
    out left leftType parameter value domain
  obtain ⟨hrlaw⟩ := fullFoldRootFields data window body alpha (P :: Delta)
    out right rightType parameter value domain
  obtain ⟨hleftPre⟩ := andIntro (andLeft hp) (andIntro (andLeft h2) (andLeft h4))
  obtain ⟨hrightPre⟩ := andIntro (andLeft h1) (andIntro (andLeft h3) (andRight h4))
  have hleft := Derivation.implicationElimination hlaw hleftPre
  have hright := Derivation.implicationElimination hrlaw hrightPre
  have htag := iffCompose (tagGraph value left) (tagGraph value out) (tagGraph value right)
    (iffFlip (tagGraph value out) (tagGraph value left) ⟨Derivation.conjunctionLeft hleft⟩)
    ⟨Derivation.conjunctionLeft hright⟩
  have happ := iffCompose (applicationShape domain left) (applicationShape domain out)
    (applicationShape domain right)
    (iffFlip (applicationShape domain out) (applicationShape domain left) ⟨Derivation.conjunctionRight hleft⟩)
    ⟨Derivation.conjunctionRight hright⟩
  obtain ⟨h⟩ := andIntro htag happ
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
