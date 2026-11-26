module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open DeletionMapDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map OriginalHereditaryDeletionRows.scan
  InternalPairing.pairing InternalUnpair.right OriginalContextInsertion.length

theorem rawRows (raw parameter fake jobs : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
    (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalHereditaryDeletionRows.rows OriginalHereditaryExpansion.unpackJob) jobs fake parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![raw,parameter]
  let f : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
  have fv := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
    fake z raw xs hf (constantValue 0 xs) (projectionValue 0 xs)
  exact binaryRecover (OriginalHereditaryDeletionRows.rows OriginalHereditaryExpansion.unpackJob)
    f (.projection 1) jobs fake parameter xs hj fv (projectionValue 1 xs)

theorem rowsFromScan (Q : Program 2) (input parameter gamma count row : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)))
    (hs : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan Q) row count input parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![input,parameter]
  let c : Program 2 := .composition OriginalContextInsertion.length
    (fun _ : Fin 1 => rightOf (.projection 1))
  have rightValue := unaryValue InternalUnpair.right (.projection 1) gamma parameter xs hg (projectionValue 1 xs)
  have countValue := unaryValue OriginalContextInsertion.length (rightOf (.projection 1)) count gamma xs hl rightValue
  apply compositionValue (OriginalHereditaryDeletionRows.scan Q) ![c,.projection 0,.projection 1]
    row xs ![count,input,parameter] hs
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · exact countValue
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs

theorem forwardAtCoordinates (Q : Program 2) (input typ raw parameter jobs row fake gamma count : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) (rawScalarFromJob Q)) row jobs typ)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma))) :
    Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)) := by
  have sourceRows := rawRows raw parameter fake jobs hf hj
  have sourceScan := OriginalHereditaryDeletionRowsBoundProof.scanFromRows
    OriginalHereditaryExpansion.unpackJob fake parameter gamma count jobs hg hl sourceRows
  have mappedScan := DeletionScanProof.actualScanMap Q count input fake typ raw parameter jobs row
    hi hf sourceScan hm
  exact rowsFromScan Q input parameter gamma count row hg hl mappedScan

theorem forward (Q : Program 2) (input typ raw parameter jobs row : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) (rawScalarFromJob Q)) row jobs typ))) :
    Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)) := by
  let f : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
  let g : Program 2 := rightOf (.projection 1)
  let c : Program 2 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => g)
  let qs : Fin 3 → Program 2 := ![f,g,c]
  let xs : Fin 2 → OTerm alpha := ![raw,parameter]
  apply queryCases qs xs _
  intro beta j ys Theta hTheta hq
  simp only [graph2Rename]
  let xx : Fin 2 → OTerm beta := ![raw.relabel j,parameter.relabel j]
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ (fun k => Fin.elim0 k) i
      rfl
  rw [hxs] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph f (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph g (ys 1) xx)) := hq 1
  have q2 : Nonempty (Derivation body Theta (programGraph c (ys 2) xx)) := hq 2
  have hi := renameInto hi j Theta hTheta
  have hj := renameInto hj j Theta hTheta
  have hm := renameInto hm j Theta hTheta
  simp only [graph2Rename] at hi hj hm
  have hf := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
    (ys 0) z (raw.relabel j) xx q0 (constantValue 0 xx) (projectionValue 0 xx)
  have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) xx q1 (projectionValue 1 xx)
  have hl := unaryRecover OriginalContextInsertion.length g (ys 2) (ys 1) xx q2 q1
  exact forwardAtCoordinates Q (input.relabel j) (typ.relabel j) (raw.relabel j)
    (parameter.relabel j) (jobs.relabel j) (row.relabel j) (ys 0) (ys 1) (ys 2) hi hj hm hf hg hl

theorem backward (Q : Program 2) (input typ raw parameter jobs row : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter))) :
    Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) (rawScalarFromJob Q)) row jobs typ)) := by
  let M := InternalListMap.map (k := 1) (rawScalarFromJob Q)
  let xs : Fin 2 → OTerm alpha := Fin.cons jobs (Fin.cons typ Fin.elim0)
  apply programCases M xs _
  intro beta j Theta value hTheta hm
  simp only [graph2Rename]
  have hxs : (fun i => (xs i).relabel j) = Fin.cons (jobs.relabel j) (Fin.cons (typ.relabel j) Fin.elim0) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ (fun k => Fin.elim0 k) i
      rfl
  rw [hxs] at hm
  have hi := renameInto hi j Theta hTheta
  have hj := renameInto hj j Theta hTheta
  have hr := renameInto hr j Theta hTheta
  simp only [graph2Rename] at hi hj hr
  have actualRows := forward Q (input.relabel j) (typ.relabel j) (raw.relabel j)
    (parameter.relabel j) (jobs.relabel j) value hi hj hm
  have he := valueUnique (OriginalHereditaryDeletionRows.rows Q) value (row.relabel j)
    ![input.relabel j,parameter.relabel j] actualRows hr
  exact outputTransport M value (row.relabel j) ![jobs.relabel j,typ.relabel j] he hm

theorem actualOrderedMap : DeletionMapTargets.ActualOrderedMap := by
  intro Q body alpha Delta input typ raw parameter jobs row hi hj
  let A := graph2 (InternalListMap.map (k := 1) (rawScalarFromJob Q)) row jobs typ
  let B := graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter
  obtain ⟨hf⟩ := forward Q input typ raw parameter jobs row
    (withHyp hi A) (withHyp hj A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := backward Q input typ raw parameter jobs row
    (withHyp hi B) (withHyp hj B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapProof.actualOrderedMap
