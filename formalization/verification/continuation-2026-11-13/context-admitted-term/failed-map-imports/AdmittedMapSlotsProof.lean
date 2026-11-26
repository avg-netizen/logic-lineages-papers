module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLengthCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildMapRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedMapSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map

theorem mapZero (F : Program 1) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) z z)) := by
  obtain ⟨law⟩ := InternalListMapProof.actualOriginalListMapZero body 0 F alpha z Fin.elim0
  have he : Nonempty (Derivation body Delta (equal z z)) := by
    rw [equalEqn]
    exact ⟨refl z⟩
  exact closedApply ⟨Derivation.conjunctionRight law⟩ he

theorem singletonAtValue (F : Program 1) (code head row first value : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph code head z)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hv : Nonempty (Derivation body Delta (graph1 F value head))) :
    Nonempty (Derivation body Delta (consGraph row first z)) := by
  have hs := InternalListMapProof.consForward F code head z value z row Fin.elim0 hc hv (mapZero F) hm
  have he := valueUnique InternalRawListRecursion.lookup value first (Fin.cons z (Fin.cons row Fin.elim0))
    (OriginalAllPositionContextDeleteBaseProof.lookupZero row value z hs) hl
  exact headTransport InternalListCodec.consCode row value first (Fin.cons z Fin.elim0) he hs

theorem singletonAtCons (F : Program 1) (code head row first : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph code head z)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row))) :
    Nonempty (Derivation body Delta (consGraph row first z)) := by
  apply programCases F (Fin.cons head Fin.elim0) _
  intro beta j Theta value hj hv
  simp only [consGraphRename,zRelabel]
  have hc' := renameInto hc j Theta hj
  have hm' := renameInto hm j Theta hj
  have hl' := renameInto hl j Theta hj
  simp only [consGraphRename,graph1Rename,graph2Rename,zRelabel] at hc' hm' hl'
  simp only [consTermRename,emptyRename] at hv
  exact singletonAtValue F (code.relabel j) (head.relabel j) (row.relabel j) (first.relabel j) value hc' hm' hl' hv

theorem singleton (F : Program 1) (code row first : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (lengthGraph (suc z) code)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row))) :
    Nonempty (Derivation body Delta (consGraph row first z)) := by
  apply AdmittedLengthCasesProof.singletonCases code _ hc
  intro beta j Theta head hj hs
  simp only [consGraphRename,zRelabel]
  have hm' := renameInto hm j Theta hj
  have hl' := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel] at hm' hl'
  exact singletonAtCons F (code.relabel j) head (row.relabel j) (first.relabel j) hs hm' hl'

theorem binaryAtValues (F : Program 1) (code head tail row first second value tailOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph code head tail)))
    (ht : Nonempty (Derivation body Delta (lengthGraph (suc z) tail)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row)))
    (hv : Nonempty (Derivation body Delta (graph1 F value head)))
    (hmt : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) tailOut tail))) :
    Nonempty (Derivation body Delta (consGraph row first tailOut ⊓ consGraph tailOut second z)) := by
  have hrow := InternalListMapProof.consForward F code head tail value tailOut row Fin.elim0 hc hv hmt hm
  have he := valueUnique InternalRawListRecursion.lookup value first (Fin.cons z (Fin.cons row Fin.elim0))
    (OriginalAllPositionContextDeleteBaseProof.lookupZero row value tailOut hrow) hf
  have hrow' := headTransport InternalListCodec.consCode row value first (Fin.cons tailOut Fin.elim0) he hrow
  obtain ⟨law⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff row first tailOut z second hrow'
  have hs' : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second z tailOut)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice hs)⟩
  exact andIntro hrow' (singleton F tail tailOut second ht hmt hs')

theorem binaryCases (F : Program 1) (code row first second : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (lengthGraph (suc (suc z)) code)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tailOut : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (consGraph (row.relabel j) (first.relabel j) tailOut)) →
      Nonempty (Derivation body Theta (consGraph tailOut (second.relabel j) z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply AdmittedLengthCasesProof.successorCases code (suc z) psi hc
  intro beta j Theta head tail hj hcode htail
  let qs : Fin 2 → Program 2 := ![.composition F (fun _ : Fin 1 => .projection 0),
    .composition (InternalListMap.map (k := 0) F) (fun _ : Fin 1 => .projection 1)]
  let xs : Fin 2 → OTerm beta := Fin.cons head (Fin.cons tail Fin.elim0)
  apply queryCases qs xs _
  intro gamma k ys Xi hk hq
  let xx : Fin 2 → OTerm gamma := Fin.cons (head.relabel k) (Fin.cons (tail.relabel k) Fin.elim0)
  have hx : (fun i => (xs i).relabel k) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun l => Fin.elim0 l)) i
  rw [hx] at hq
  have hc' := renameInto hcode k Xi hk
  have ht' := renameInto htail k Xi hk
  have hm' := renameInto (renameInto hm j Theta hj) k Xi hk
  have hf' := renameInto (renameInto hf j Theta hj) k Xi hk
  have hs' := renameInto (renameInto hs j Theta hj) k Xi hk
  simp only [consGraphRename,lengthRename,graph1Rename,graph2Rename,zRelabel,sucRelabel] at hc' ht' hm' hf' hs'
  have hv := unaryRecover F (.projection 0) (ys 0) (head.relabel k) xx (hq 0) (projectionValue 0 xx)
  have hmt := unaryRecover (InternalListMap.map (k := 0) F) (.projection 1) (ys 1) (tail.relabel k) xx (hq 1) (projectionValue 1 xx)
  have facts := binaryAtValues F ((code.relabel j).relabel k) (head.relabel k) (tail.relabel k)
    ((row.relabel j).relabel k) ((first.relabel j).relabel k) ((second.relabel j).relabel k)
    (ys 0) (ys 1) hc' ht' hm' hf' hs' hv hmt
  have inc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
    intro f h
    simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk _ (hj f h)
  have result := next gamma (k ∘ j) Xi (ys 1) inc
    (by simpa only [Term.relabel_relabel] using andLeft facts)
    (by simpa only [Term.relabel_relabel] using andRight facts)
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using result
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedMapSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedMapSlotsProof
