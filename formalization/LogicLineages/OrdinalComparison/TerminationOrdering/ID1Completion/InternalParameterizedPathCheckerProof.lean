module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSummaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof
open InternalParameterizedPathCheckerFinishProof InternalParameterizedPathCheckerSummaryProof
open InternalPathCheckerSyntaxProof (pairGraphRename)
open InternalListCodec InternalListCodecSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nilRecover (edge : Program 4) (x y parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (pathGraph edge x y z parameter))) :
    Nonempty (Derivation body Gamma (equal x y)) := by
  have hf := checkerRecover edge false (suc z) x y z z parameter (summaryZero edge y parameter) h
  have he := endpointsRecover (suc z) x y z parameter (finishZeroRecover edge false (suc z) x y parameter hf)
  obtain ⟨hi⟩ := InternalEqualityTestProof.actualOriginalEqualityAcceptance body α x y
  exact closedApply ⟨Derivation.conjunctionLeft hi⟩ he

theorem nilAccept (edge : Program 4) (x y parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (equal x y))) :
    Nonempty (Derivation body Gamma (pathGraph edge x y z parameter)) := by
  obtain ⟨hi⟩ := InternalEqualityTestProof.actualOriginalEqualityAcceptance body α x y
  have he := closedApply ⟨Derivation.conjunctionRight hi⟩ h
  have hf := finishZeroValue edge false (suc z) x y parameter (endpointsValue (suc z) x y z parameter he)
  exact checkerValue edge false (suc z) x y z z parameter (summaryZero edge y parameter) hf

/-- Contextual nil equivalence in the original calculus. -/
theorem pathNil (edge : Program 4) (x y parameter : OTerm α) :
    Nonempty (Derivation body Gamma ((pathGraph edge x y z parameter).iff (equal x y))) := by
  obtain ⟨hf⟩ := nilRecover (body := body) (Gamma := pathGraph edge x y z parameter :: Gamma) edge x y parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := nilAccept (body := body) (Gamma := equal x y :: Gamma) edge x y parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The literal positive checker rejects nil in every context. -/
theorem positiveNil (edge : Program 4) (x y parameter : OTerm α) :
    Nonempty (Derivation body Gamma (positiveGraph edge x y z parameter).not) := by
  let P := positiveGraph edge x y z parameter
  have h : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := checkerRecover edge true (suc z) x y z z parameter (summaryZero edge y parameter) h
  have hz := finishZeroRecover edge true (suc z) x y parameter hf
  obtain ⟨he⟩ := valueUnique (InternalRawListRecursion.zero : Program 4)
    (suc z) z (quadruple x y z parameter) hz (InternalRawListRecursionSupportProof.constantZero (quadruple x y z parameter))
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem consAtState (edge : Program 4) (positive : Bool)
    (x y code raw tail vertex certificate previous result state parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y parameter)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous parameter)))
    (hs : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate parameter)) := by
  obtain ⟨hsummary⟩ := summaryConsValue edge code raw tail y vertex certificate previous result state parameter hp hc ht hf hs
  obtain ⟨htail⟩ := checkerValue edge false result vertex y tail previous parameter ht hf
  obtain ⟨hp⟩ := hp
  obtain ⟨hs⟩ := hs
  let P := checkerGraph edge positive (suc z) x y code parameter
  let Q := edgeGraph edge x vertex certificate parameter ⊓ pathGraph edge vertex y tail parameter
  have forward : Nonempty (Derivation body (P :: Gamma) Q) := by
    have hf' := checkerRecover edge positive (suc z) x y code state parameter ⟨addHyp hsummary P⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := finishConsRecover edge positive x y state raw result vertex certificate parameter
      ⟨addHyp hp P⟩ ⟨addHyp hs P⟩ hf'
    obtain ⟨ht'⟩ := outputTransport (checker edge false) result (suc z) (quadruple vertex y tail parameter)
      ⟨Derivation.conjunctionRight he⟩ ⟨addHyp htail P⟩
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft he) ht'⟩
  have backward : Nonempty (Derivation body (Q :: Gamma) P) := by
    have hq : Derivation body (Q :: Gamma) Q := Derivation.hypothesis List.mem_cons_self
    have he := valueUnique (checker edge false) result (suc z) (quadruple vertex y tail parameter)
      ⟨addHyp htail Q⟩ ⟨Derivation.conjunctionRight hq⟩
    have hf' := finishConsAccept edge positive x y state raw result vertex certificate parameter
      ⟨addHyp hp Q⟩ ⟨addHyp hs Q⟩ ⟨Derivation.conjunctionLeft hq⟩ he
    exact checkerValue edge positive (suc z) x y code state parameter ⟨addHyp hsummary Q⟩ hf'
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem consAtResult (edge : Program 4) (positive : Bool)
    (x y code raw tail vertex certificate previous result parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y parameter)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous parameter))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate parameter)) := by
  apply programCases consCode (Fin.cons raw (Fin.cons result Fin.elim0)) _
  intro β j Delta state hj hs
  rw [checkerConsResultRename]
  simp only [consTermRename,emptyRename] at hs
  have hp' := renameInto hp j Delta hj
  have hc' := renameInto hc j Delta hj
  have ht' := renameInto ht j Delta hj
  have hf' := renameInto hf j Delta hj
  rw [pairGraphRename] at hp'
  rw [consGraphRename] at hc'
  rw [summaryRename] at ht'
  rw [finishRename] at hf'
  exact consAtState edge positive (x.relabel j) (y.relabel j) (code.relabel j) (raw.relabel j)
    (tail.relabel j) (vertex.relabel j) (certificate.relabel j) (previous.relabel j) (result.relabel j)
    state (parameter.relabel j) hp' hc' ht' hf' hs

theorem consAtSummary (edge : Program 4) (positive : Bool)
    (x y code raw tail vertex certificate previous parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y parameter))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate parameter)) := by
  apply programCases (finish edge false) (quadruple vertex y previous parameter) _
  intro β j Delta result hj hf
  rw [checkerConsResultRename]
  rw [quadrupleRename] at hf
  have hp' := renameInto hp j Delta hj
  have hc' := renameInto hc j Delta hj
  have ht' := renameInto ht j Delta hj
  rw [pairGraphRename] at hp'
  rw [consGraphRename] at hc'
  rw [summaryRename] at ht'
  exact consAtResult edge positive (x.relabel j) (y.relabel j) (code.relabel j) (raw.relabel j)
    (tail.relabel j) (vertex.relabel j) (certificate.relabel j) (previous.relabel j) result (parameter.relabel j) hp' hc' ht' hf

/-- All summary and result witnesses are obtained from original Program
totality and eliminated inside the original derivation. -/
theorem consEquation (edge : Program 4) (positive : Bool)
    (x y code raw tail vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate parameter)) := by
  apply programCases (summary edge) (Fin.cons tail (Fin.cons y (Fin.cons parameter Fin.elim0))) _
  intro β j Delta previous hj ht
  rw [checkerConsResultRename]
  simp only [consTermRename,emptyRename] at ht
  have hp' := renameInto hp j Delta hj
  have hc' := renameInto hc j Delta hj
  rw [pairGraphRename] at hp'
  rw [consGraphRename] at hc'
  exact consAtSummary edge positive (x.relabel j) (y.relabel j) (code.relabel j) (raw.relabel j)
    (tail.relabel j) (vertex.relabel j) (certificate.relabel j) previous (parameter.relabel j) hp' hc' ht

theorem pathCons (edge : Program 4) (x y code raw tail vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma ((pathGraph edge x y code parameter).iff
      (edgeGraph edge x vertex certificate parameter ⊓ pathGraph edge vertex y tail parameter))) :=
  consEquation edge false x y code raw tail vertex certificate parameter hp hc

theorem positiveCons (edge : Program 4) (x y code raw tail vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma ((positiveGraph edge x y code parameter).iff
      (edgeGraph edge x vertex certificate parameter ⊓ pathGraph edge vertex y tail parameter))) :=
  consEquation edge true x y code raw tail vertex certificate parameter hp hc

theorem actualInternalParameterizedPathNil : InternalParameterizedPathCheckerTargets.ActualInternalParameterizedPathNil := by
  intro body edge α x y parameter
  exact pathNil edge x y parameter

theorem actualInternalParameterizedPositivePathNil : InternalParameterizedPathCheckerTargets.ActualInternalParameterizedPositivePathNil := by
  intro body edge α x y parameter
  exact positiveNil edge x y parameter

theorem actualInternalParameterizedPathCons : InternalParameterizedPathCheckerTargets.ActualInternalParameterizedPathCons := by
  intro body edge α x y code raw tail vertex certificate parameter
  let P := consPremises code raw tail vertex certificate
  obtain ⟨h⟩ := pathCons (body := body) (Gamma := [P]) edge x y code raw tail vertex certificate parameter
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualInternalParameterizedPositivePathCons : InternalParameterizedPathCheckerTargets.ActualInternalParameterizedPositivePathCons := by
  intro body edge α x y code raw tail vertex certificate parameter
  let P := consPremises code raw tail vertex certificate
  obtain ⟨h⟩ := positiveCons (body := body) (Gamma := [P]) edge x y code raw tail vertex certificate parameter
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerProof
