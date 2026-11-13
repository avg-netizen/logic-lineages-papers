module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalListInduction InternalListInductionSyntaxProof InternalListInductionProof
open InheritedMapDefinitions InheritedMapSyntaxProof InheritedMapCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map InternalListCodec.consCode

theorem zeroRow (Q : Program 2) : Nonempty (Derivation body Delta (row Q (z : OTerm alpha))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let typ : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let annotated : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let valueRow : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields Q z typ annotated valueRow
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  obtain ⟨h⟩ := zeroCore Q typ annotated valueRow (body := body) (Delta := Theta)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem consRow (Q : Program 2) (code head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row Q tail))) :
    Nonempty (Derivation body Delta (row Q code)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let typ : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let annotated : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let valueRow : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields Q (code.relabel Sum.inl) typ annotated valueRow
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have hc' := renameInto hc Sum.inl Theta inc
  rw [graph2Rename] at hc'
  have hi' := renameInto hi Sum.inl Theta inc
  rw [InheritedMapSyntaxProof.rowRename] at hi'
  obtain ⟨h⟩ := consCore Q (code.relabel Sum.inl) (head.relabel Sum.inl) (tail.relabel Sum.inl)
    typ annotated valueRow hc' hi'
    (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem allRows (Q : Program 2) (jobs : OTerm alpha) :
    Nonempty (Derivation body Delta (row Q jobs)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row Q (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (atCode theta z)) := by
    rw [InheritedMapSyntaxProof.rowAtCode]
    exact zeroRow Q
  have hs : Nonempty (Derivation body Delta (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Delta
    simp only [constructorBody,theta,InheritedMapSyntaxProof.rowAtIndex]
    let code : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let head : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let tail : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := graph2 InternalListCodec.consCode code head tail
    let IH := row Q tail
    obtain ⟨h⟩ := consRow Q code head tail
      (body := body) (Delta := IH :: C :: Delta.map (fun f => f.relabel Sum.inl))
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
  have h := actualOriginalListInductionAtCode body alpha Delta theta jobs (andIntro hz hs)
  rw [InheritedMapSyntaxProof.rowAtCode] at h
  exact h

theorem forward (Q : Program 2) (jobs typ annotated valueRow : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) inheritedJob) annotated jobs typ)))
    (hs : Nonempty (Derivation body Delta
      (graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) valueRow annotated))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow jobs typ)) :=
  rowApply Q jobs typ annotated valueRow (allRows Q jobs) (andIntro ha hs)

theorem backward (Q : Program 2) (jobs typ annotated valueRow : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) inheritedJob) annotated jobs typ)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow jobs typ))) :
    Nonempty (Derivation body Delta
      (graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) valueRow annotated)) := by
  let S := InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)
  let M := InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)
  let xs : Fin 1 → OTerm alpha := Fin.cons annotated Fin.elim0
  apply programCases S xs _
  intro beta j Theta actual hj hs
  simp only [graph1Rename]
  have hx : (fun i => (xs i).relabel j) = Fin.cons (annotated.relabel j) Fin.elim0 := by
    funext i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) i
    rfl
  rw [hx] at hs
  have ha' := renameInto ha j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename] at ha' hr'
  have hm := forward Q (jobs.relabel j) (typ.relabel j) (annotated.relabel j) actual ha' hs
  have he := valueUnique M actual (valueRow.relabel j) ![jobs.relabel j,typ.relabel j] hm hr'
  exact outputTransport S actual (valueRow.relabel j) ![annotated.relabel j] he hs

theorem actualScalarFusion : InheritedMapTargets.ActualScalarFusion := by
  intro Q body alpha Delta jobs typ annotated valueRow ha
  let A := graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) valueRow annotated
  let B := graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow jobs typ
  obtain ⟨hf⟩ := forward Q jobs typ annotated valueRow (withHyp ha A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := backward Q jobs typ annotated valueRow (withHyp ha B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualInheritedDeletionRow : InheritedMapTargets.ActualInheritedDeletionRow := by
  intro Q body alpha Delta input typ raw parameter jobs annotated valueRow hp hj ha
  exact SuffixLookupCoreProof.composeIff
    (actualScalarFusion Q body alpha Delta jobs typ annotated valueRow ha)
    (DeletionMapProof.actualOrderedMap Q body alpha Delta input typ raw parameter jobs valueRow hp hj)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapProof.actualScalarFusion
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapProof.actualInheritedDeletionRow
