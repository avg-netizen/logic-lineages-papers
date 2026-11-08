module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationPathLift InternalApplicationPathLiftSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionTotalityProof
open InternalRecursionGraphStepSyntaxProof InternalRecursionClosureProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem mapGraphAt (vertex : Program 5) (ps : Parameters α) (out code : OTerm α) :
    InternalApplicationPathMap.mapGraph vertex out code (ps 0) (ps 1) (ps 2) (ps 3) =
      mappedAt vertex ps out code := by
  unfold InternalApplicationPathMap.mapGraph mappedAt
  rw [parametersExpand ps]

/-- Six ordinary Program outputs provide the entry fields and their images
in one context extension. Every witness is discharged by original existential
elimination; the supplied map output is then unfolded on the original cons. -/
theorem mappedConsCases (vertex : Program 5) (ps : Parameters α)
    (code raw tail mapped : OTerm α) (psi : Formula α)
    (hcons : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode code raw tail)))
    (hmapped : Nonempty (Derivation body Gamma (mappedAt vertex ps mapped code)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (v certificate mv mc mr mt : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing (raw.relabel j) v certificate)) →
      Nonempty (Derivation body Delta
        (vertexAt vertex (fun i => (ps i).relabel j) mv v)) →
      Nonempty (Derivation body Delta
        (liftedEdgeAt (fun i => (ps i).relabel j) mc certificate)) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mr mv mc)) →
      Nonempty (Derivation body Delta
        (mappedAt vertex (fun i => (ps i).relabel j) mt (tail.relabel j))) →
      Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (mapped.relabel j) mr mt)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let xs : Fin 6 → OTerm α := Fin.cons raw (Fin.cons tail ps)
  let leftProgram : Program 6 := .composition InternalUnpair.left
    (fun _ : Fin 1 => .projection 0)
  let rightProgram : Program 6 := .composition InternalUnpair.right
    (fun _ : Fin 1 => .projection 0)
  let vertexProgram : Program 6 := .composition vertex
    ![.projection 2,.projection 3,.projection 4,.projection 5,leftProgram]
  let edgeProgram : Program 6 := .composition InternalApplicationCertificateConstructors.edgeLift
    ![.projection 3,.projection 4,.projection 5,rightProgram]
  let pairProgram : Program 6 := .composition InternalPairing.pairing ![vertexProgram,edgeProgram]
  let tailProgram : Program 6 := .composition (InternalApplicationPathMap.pathMap vertex)
    (Fin.cons (.projection 1) (fun i : Fin 4 => .projection i.succ.succ))
  let programs : Fin 6 → Program 6 :=
    ![leftProgram,rightProgram,vertexProgram,edgeProgram,pairProgram,tailProgram]
  apply supplyOutputs body 6 6 (fun i => OrdinaryArithmetic.graphFormula (programs i))
    (fun i => (actualOriginalPrograms body 6 (programs i)).1) α Gamma xs psi
  intro β j Delta ys hj hys
  let ps' : Parameters β := fun i => (ps i).relabel j
  let xs' : Fin 6 → OTerm β := Fin.cons (raw.relabel j) (Fin.cons (tail.relabel j) ps')
  have hs (i : Fin 6) : Nonempty (Derivation body Delta
      (programGraph (programs i) (ys i) xs')) := by
    simpa only [programGraph,xs,xs',ps',consTermRename] using hys i
  have hl := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (raw.relabel j) xs'
    (hs 0) (projectionValue 0 xs')
  have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (raw.relabel j) xs'
    (hs 1) (projectionValue 0 xs')
  obtain ⟨hraw⟩ := reconstructPair (raw.relabel j) (ys 0) (ys 1) hl hr
  have hv : Nonempty (Derivation body Delta (vertexAt vertex ps' (ys 2) (ys 0))) := by
    apply compositionRecover vertex
      ![.projection 2,.projection 3,.projection 4,.projection 5,leftProgram]
      (ys 2) xs' (vertexInputs ps' (ys 0)) (hs 2)
    intro i
    exact Fin.cases (projectionValue 2 xs') (Fin.cases (projectionValue 3 xs')
      (Fin.cases (projectionValue 4 xs') (Fin.cases (projectionValue 5 xs')
        (Fin.cases (hs 0) (fun q => Fin.elim0 q))))) i
  have he : Nonempty (Derivation body Delta (liftedEdgeAt ps' (ys 3) (ys 1))) := by
    apply compositionRecover InternalApplicationCertificateConstructors.edgeLift
      ![.projection 3,.projection 4,.projection 5,rightProgram]
      (ys 3) xs' (Fin.cons (ps' 1) (Fin.cons (ps' 2) (Fin.cons (ps' 3)
        (Fin.cons (ys 1) Fin.elim0)))) (hs 3)
    intro i
    exact Fin.cases (projectionValue 3 xs') (Fin.cases (projectionValue 4 xs')
      (Fin.cases (projectionValue 5 xs') (Fin.cases (hs 1) (fun q => Fin.elim0 q)))) i
  have hp := binaryRecover InternalPairing.pairing vertexProgram edgeProgram
    (ys 4) (ys 2) (ys 3) xs' (hs 4) (hs 2) (hs 3)
  have ht : Nonempty (Derivation body Delta
      (mappedAt vertex ps' (ys 5) (tail.relabel j))) := by
    apply compositionRecover (InternalApplicationPathMap.pathMap vertex)
      (Fin.cons (.projection 1) (fun i : Fin 4 => .projection i.succ.succ))
      (ys 5) xs' (Fin.cons (tail.relabel j) ps') (hs 5)
    intro i
    exact Fin.cases (projectionValue 1 xs')
      (fun q => projectionValue q.succ.succ xs') i
  have hc := renameInto hcons j Delta hj
  rw [graph2Rename] at hc
  have hm := renameInto hmapped j Delta hj
  rw [mappedAtRename] at hm
  change Nonempty (Derivation body Delta
    (mappedAt vertex ps' (mapped.relabel j) (code.relabel j))) at hm
  rw [← mapGraphAt vertex ps' (mapped.relabel j) (code.relabel j)] at hm
  have htail := ht
  rw [← mapGraphAt vertex ps' (ys 5) (tail.relabel j)] at htail
  obtain ⟨hc⟩ := hc
  obtain ⟨hv⟩ := hv
  obtain ⟨he⟩ := he
  obtain ⟨hp⟩ := hp
  obtain ⟨htail⟩ := htail
  have hpremise : Nonempty (Derivation body Delta
      (InternalApplicationPathMap.consPremises vertex (ps' 0) (ps' 1) (ps' 2) (ps' 3)
        (code.relabel j) (raw.relabel j) (tail.relabel j)
        (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))) :=
    ⟨Derivation.conjunctionIntroduction hc
      (Derivation.conjunctionIntroduction
        (Derivation.conjunctionIntroduction hraw (Derivation.conjunctionIntroduction hv he))
        (Derivation.conjunctionIntroduction hp htail))⟩
  obtain ⟨hiff⟩ := closedApply
    (InternalApplicationPathMapProof.actualOriginalPathMapCons body vertex β
      (ps' 0) (ps' 1) (ps' 2) (ps' 3)
      (code.relabel j) (raw.relabel j) (tail.relabel j)
      (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (mapped.relabel j)) hpremise
  obtain ⟨hm⟩ := hm
  have hout : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode (mapped.relabel j) (ys 4) (ys 5))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hiff) hm⟩
  exact k β j Delta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hj
    ⟨hraw⟩ ⟨hv⟩ ⟨he⟩ ⟨hp⟩ ht hout

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftWitnessProof
