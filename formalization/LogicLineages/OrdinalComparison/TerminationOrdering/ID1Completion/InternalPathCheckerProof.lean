module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSummaryProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalPathChecker InternalPathCheckerSyntaxProof InternalPathCheckerFinishProof InternalPathCheckerSummaryProof
open InternalListCodec InternalListCodecSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nilRecover (edge : Program 3) (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (pathGraph edge x y z))) :
    Nonempty (Derivation body Gamma (equal x y)) := by
  have hf := checkerRecover edge false (suc z) x y z z (summaryZero edge y) h
  have he := endpointsRecover (suc z) x y z (finishZeroRecover edge false (suc z) x y hf)
  obtain ⟨hi⟩ := InternalEqualityTestProof.actualOriginalEqualityAcceptance body α x y
  exact closedApply ⟨Derivation.conjunctionLeft hi⟩ he

theorem nilAccept (edge : Program 3) (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (equal x y))) :
    Nonempty (Derivation body Gamma (pathGraph edge x y z)) := by
  obtain ⟨hi⟩ := InternalEqualityTestProof.actualOriginalEqualityAcceptance body α x y
  have he := closedApply ⟨Derivation.conjunctionRight hi⟩ h
  have hf := finishZeroValue edge false (suc z) x y (endpointsValue (suc z) x y z he)
  exact checkerValue edge false (suc z) x y z z (summaryZero edge y) hf

/-- Contextual nil equivalence in the original calculus. -/
theorem pathNil (edge : Program 3) (x y : OTerm α) :
    Nonempty (Derivation body Gamma ((pathGraph edge x y z).iff (equal x y))) := by
  obtain ⟨hf⟩ := nilRecover (body := body) (Gamma := pathGraph edge x y z :: Gamma) edge x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := nilAccept (body := body) (Gamma := equal x y :: Gamma) edge x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The literal positive checker rejects nil in every context. -/
theorem positiveNil (edge : Program 3) (x y : OTerm α) :
    Nonempty (Derivation body Gamma (positiveGraph edge x y z).not) := by
  let P := positiveGraph edge x y z
  have h : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := checkerRecover edge true (suc z) x y z z (summaryZero edge y) h
  have hz := finishZeroRecover edge true (suc z) x y hf
  obtain ⟨he⟩ := valueUnique (InternalRawListRecursion.zero : Program 3)
    (suc z) z (triple x y z) hz (InternalRawListRecursionSupportProof.constantZero (triple x y z))
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem consAtState (edge : Program 3) (positive : Bool)
    (x y code raw tail vertex certificate previous result state : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous)))
    (hs : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate)) := by
  obtain ⟨hsummary⟩ := summaryConsValue edge code raw tail y vertex certificate previous result state hp hc ht hf hs
  obtain ⟨htail⟩ := checkerValue edge false result vertex y tail previous ht hf
  obtain ⟨hp⟩ := hp
  obtain ⟨hs⟩ := hs
  let P := checkerGraph edge positive (suc z) x y code
  let Q := edgeGraph edge x vertex certificate ⊓ pathGraph edge vertex y tail
  have forward : Nonempty (Derivation body (P :: Gamma) Q) := by
    have hf' := checkerRecover edge positive (suc z) x y code state ⟨addHyp hsummary P⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := finishConsRecover edge positive x y state raw result vertex certificate
      ⟨addHyp hp P⟩ ⟨addHyp hs P⟩ hf'
    obtain ⟨ht'⟩ := outputTransport (checker edge false) result (suc z) (triple vertex y tail)
      ⟨Derivation.conjunctionRight he⟩ ⟨addHyp htail P⟩
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft he) ht'⟩
  have backward : Nonempty (Derivation body (Q :: Gamma) P) := by
    have hq : Derivation body (Q :: Gamma) Q := Derivation.hypothesis List.mem_cons_self
    have he := valueUnique (checker edge false) result (suc z) (triple vertex y tail)
      ⟨addHyp htail Q⟩ ⟨Derivation.conjunctionRight hq⟩
    have hf' := finishConsAccept edge positive x y state raw result vertex certificate
      ⟨addHyp hp Q⟩ ⟨addHyp hs Q⟩ ⟨Derivation.conjunctionLeft hq⟩ he
    exact checkerValue edge positive (suc z) x y code state ⟨addHyp hsummary Q⟩ hf'
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem consAtResult (edge : Program 3) (positive : Bool)
    (x y code raw tail vertex certificate previous result : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y)))
    (hf : Nonempty (Derivation body Gamma (finishGraph edge false result vertex y previous))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate)) := by
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
    state hp' hc' ht' hf' hs

theorem consAtSummary (edge : Program 3) (positive : Bool)
    (x y code raw tail vertex certificate previous : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (ht : Nonempty (Derivation body Gamma (summaryGraph edge previous tail y))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate)) := by
  apply programCases (finish edge false) (triple vertex y previous) _
  intro β j Delta result hj hf
  rw [checkerConsResultRename]
  rw [tripleRename] at hf
  have hp' := renameInto hp j Delta hj
  have hc' := renameInto hc j Delta hj
  have ht' := renameInto ht j Delta hj
  rw [pairGraphRename] at hp'
  rw [consGraphRename] at hc'
  rw [summaryRename] at ht'
  exact consAtResult edge positive (x.relabel j) (y.relabel j) (code.relabel j) (raw.relabel j)
    (tail.relabel j) (vertex.relabel j) (certificate.relabel j) (previous.relabel j) result hp' hc' ht' hf

/-- All summary and result witnesses are obtained from original Program
totality and eliminated inside the original derivation. -/
theorem consEquation (edge : Program 3) (positive : Bool)
    (x y code raw tail vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma (checkerConsResult edge positive x y code tail vertex certificate)) := by
  apply programCases (summary edge) (Fin.cons tail (Fin.cons y Fin.elim0)) _
  intro β j Delta previous hj ht
  rw [checkerConsResultRename]
  simp only [consTermRename,emptyRename] at ht
  have hp' := renameInto hp j Delta hj
  have hc' := renameInto hc j Delta hj
  rw [pairGraphRename] at hp'
  rw [consGraphRename] at hc'
  exact consAtSummary edge positive (x.relabel j) (y.relabel j) (code.relabel j) (raw.relabel j)
    (tail.relabel j) (vertex.relabel j) (certificate.relabel j) previous hp' hc' ht

theorem pathCons (edge : Program 3) (x y code raw tail vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma ((pathGraph edge x y code).iff
      (edgeGraph edge x vertex certificate ⊓ pathGraph edge vertex y tail))) :=
  consEquation edge false x y code raw tail vertex certificate hp hc

theorem positiveCons (edge : Program 3) (x y code raw tail vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma ((positiveGraph edge x y code).iff
      (edgeGraph edge x vertex certificate ⊓ pathGraph edge vertex y tail))) :=
  consEquation edge true x y code raw tail vertex certificate hp hc

theorem actualInternalPathNil : InternalPathCheckerTargets.ActualInternalPathNil := by
  intro body edge α x y
  exact pathNil edge x y

theorem actualInternalPositivePathNil : InternalPathCheckerTargets.ActualInternalPositivePathNil := by
  intro body edge α x y
  exact positiveNil edge x y

theorem actualInternalPathCons : InternalPathCheckerTargets.ActualInternalPathCons := by
  intro body edge α x y code raw tail vertex certificate
  let P := consPremises code raw tail vertex certificate
  obtain ⟨h⟩ := pathCons (body := body) (Gamma := [P]) edge x y code raw tail vertex certificate
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualInternalPositivePathCons : InternalPathCheckerTargets.ActualInternalPositivePathCons := by
  intro body edge α x y code raw tail vertex certificate
  let P := consPremises code raw tail vertex certificate
  obtain ⟨h⟩ := positiveCons (body := body) (Gamma := [P]) edge x y code raw tail vertex certificate
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerProof
