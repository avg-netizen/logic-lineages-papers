module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerGuardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerCollapseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationStepCheckerGraphProof (edgeStateValue)
open InternalParameterizedApplicationResultStackWiringProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open OriginalNonapplicationChecker OriginalNonapplicationCheckerGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atStateForward (endpoint : Program 6) (oldChecker : Program 4)
    (out s t k parameter state : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hn : Nonempty (Derivation body Gamma (nonapplicationRoot s)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (graph4 oldChecker out s t k parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  let sp : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let vals : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have fields := edgeSelectors state s t k he
  have hf := normalizerFixed endpoint state s parameter (andLeft fields) hn
  have hstate := binaryRecover (checkedStateP endpoint oldChecker) edgeStateP (.projection 3)
    out state parameter xs hc (edgeStateValue state s t k parameter he) (projectionValue 3 xs)
  have hselected := binaryRecover (selectedCheckerP oldChecker) (normalizerP endpoint) (.projection 1)
    out state parameter sp hstate hf (projectionValue 1 sp)
  have hold := wireRecover oldChecker ![source,target,step] out state parameter vals hselected
    (fun i => Fin.cases (andLeft fields) (Fin.cases (andLeft (andRight fields))
      (Fin.cases (andRight (andRight fields)) (fun j => Fin.elim0 j))) i)
  simpa only [vals,appendParameterThree] using hold

theorem atStateBackward (endpoint : Program 6) (oldChecker : Program 4)
    (out s t k parameter state : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hn : Nonempty (Derivation body Gamma (nonapplicationRoot s)))
    (hc : Nonempty (Derivation body Gamma (graph4 oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  let sp : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let vals : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have fields := edgeSelectors state s t k he
  have hf := normalizerFixed endpoint state s parameter (andLeft fields) hn
  have hselected : Nonempty (Derivation body Gamma (graph2 (selectedCheckerP oldChecker) out state parameter)) := by
    apply wireValue oldChecker ![source,target,step] out state parameter vals
    · simpa only [vals,appendParameterThree] using hc
    · intro i
      exact Fin.cases (andLeft fields) (Fin.cases (andLeft (andRight fields))
        (Fin.cases (andRight (andRight fields)) (fun j => Fin.elim0 j))) i
  have hstate := binaryValue (selectedCheckerP oldChecker) (normalizerP endpoint) (.projection 1)
    out state parameter sp hselected hf (projectionValue 1 sp)
  exact binaryValue (checkedStateP endpoint oldChecker) edgeStateP (.projection 3)
    out state parameter xs hstate (edgeStateValue state s t k parameter he) (projectionValue 3 xs)

/-- The raw edge state is internally bound by original Program totality,
not given as a new witness or inferred from a semantic certificate parse. -/
theorem checkerForward (endpoint : Program 6) (oldChecker : Program 4)
    (out s t k parameter : OTerm α)
    (hn : Nonempty (Derivation body Gamma (nonapplicationRoot s)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (graph4 oldChecker out s t k parameter)) := by
  apply programCases edgeCode (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) _
  intro β j Delta state hj he
  rw [graph4Rename]
  simp only [consTermRename,emptyRename] at he
  have hn' := renameInto hn j Delta hj
  have hc' := renameInto hc j Delta hj
  rw [nonapplicationRename] at hn'
  rw [checkerGraphRename] at hc'
  exact atStateForward endpoint oldChecker (out.relabel j) (s.relabel j) (t.relabel j)
    (k.relabel j) (parameter.relabel j) state he hn' hc'

theorem checkerBackward (endpoint : Program 6) (oldChecker : Program 4)
    (out s t k parameter : OTerm α)
    (hn : Nonempty (Derivation body Gamma (nonapplicationRoot s)))
    (hc : Nonempty (Derivation body Gamma (graph4 oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter)) := by
  apply programCases edgeCode (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) _
  intro β j Delta state hj he
  rw [checkerGraphRename]
  simp only [consTermRename,emptyRename] at he
  have hn' := renameInto hn j Delta hj
  have hc' := renameInto hc j Delta hj
  rw [nonapplicationRename] at hn'
  rw [graph4Rename] at hc'
  exact atStateBackward endpoint oldChecker (out.relabel j) (s.relabel j) (t.relabel j)
    (k.relabel j) (parameter.relabel j) state he hn' hc'

theorem actualOriginalNonapplicationCheckerCollapse :
    OriginalNonapplicationCheckerTargets.ActualOriginalNonapplicationCheckerCollapse := by
  intro endpoint oldChecker body α Delta out s t k parameter
  apply guardedIffAt
  · exact checkerForward endpoint oldChecker out s t k parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerBackward endpoint oldChecker out s t k parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerCollapseProof
