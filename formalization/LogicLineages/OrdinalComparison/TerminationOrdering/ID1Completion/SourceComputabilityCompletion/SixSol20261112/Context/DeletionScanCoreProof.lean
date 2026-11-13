module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.MapAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open OriginalLambdaTraversalLambdaRootProof (binaryInputs)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open DeletionMapDefinitions DeletionScanSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map OriginalHereditaryDeletionRows.scan
  InternalApplicationValidityStackAppend.append InternalListCodec.consCode

theorem zeroCore (Q : Program 2) (input fake typ raw parameter jobs out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields Q z input fake typ raw parameter jobs out))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan Q) out z input parameter)) := by
  let F := rawScalarFromJob Q
  let M := InternalListMap.map (k := 1) F
  obtain ⟨jobsEq⟩ := valueUnique (OriginalHereditaryDeletionRows.scan OriginalHereditaryExpansion.unpackJob)
    jobs z ![z,fake,parameter] (andLeft (andRight (andRight hf)))
    (OriginalHereditaryDeletionRowsCongruenceCoreProof.scanZero
      (body := body) (Delta := Delta) OriginalHereditaryExpansion.unpackJob fake parameter)
  have mapAtZero := binaryInputs M out jobs typ z typ ⟨jobsEq⟩ ⟨refl typ⟩
    (andRight (andRight (andRight hf)))
  obtain ⟨outEq⟩ := valueUnique M out z ![z,typ] mapAtZero
    (MapAppendCoreProof.mapZero F typ)
  exact outputTransport (OriginalHereditaryDeletionRows.scan Q) z out ![z,input,parameter]
    ⟨symm outEq⟩ (OriginalHereditaryDeletionRowsCongruenceCoreProof.scanZero
      (body := body) (Delta := Delta) Q input parameter)

theorem successorAtValues (Q : Program 2)
    (count input fake typ raw parameter jobs out previous rawJob singleton previousMapped value mappedSingleton joined : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (fields Q (suc count) input fake typ raw parameter jobs out)))
    (hp : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan OriginalHereditaryExpansion.unpackJob) previous count fake parameter)))
    (hv : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation OriginalHereditaryExpansion.unpackJob) rawJob count fake parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton rawJob z)))
    (hm : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) (rawScalarFromJob Q)) previousMapped previous typ)))
    (hx : Nonempty (Derivation body Delta (graph2 (rawScalarFromJob Q) value rawJob typ)))
    (hms : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode mappedSingleton value z)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined previousMapped mappedSingleton))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan Q) out (suc count) input parameter)) := by
  let F := rawScalarFromJob Q
  let M := InternalListMap.map (k := 1) F
  have sourceAppend := OriginalHereditaryDeletionRowsStepProof.scanAppendRecover
    OriginalHereditaryExpansion.unpackJob count previous fake parameter rawJob singleton jobs
    hp (andLeft (andRight (andRight hf))) hv hs
  have singletonMap := InternalListMapProof.consBackward F singleton rawJob z value z mappedSingleton
    (Fin.cons typ Fin.elim0) hs hx (MapAppendCoreProof.mapZero F typ) hms
  have mappedJoined := MapAppendProof.actualMapAppend F body alpha Delta
    previous singleton jobs typ previousMapped mappedSingleton joined sourceAppend hm singletonMap hj
  have joinedEq := valueUnique M joined out ![jobs,typ] mappedJoined (andRight (andRight (andRight hf)))
  have actualAppend := outputTransport InternalApplicationValidityStackAppend.append joined out
    ![previousMapped,mappedSingleton] joinedEq hj
  have previousScan := rowApply Q count input fake typ raw parameter previous previousMapped hi
    (andIntro (andLeft hf) (andIntro (andLeft (andRight hf)) (andIntro hp hm)))
  have actualObservation := RawDeletionMapCellProof.rawCell Q input fake typ raw parameter count rawJob value
    (andLeft hf) (andLeft (andRight hf)) hv hx
  exact OriginalHereditaryDeletionRowsStepProof.scanNext Q count previousMapped input parameter value mappedSingleton out
    previousScan actualObservation hms actualAppend

theorem successorAtSource (Q : Program 2)
    (count input fake typ raw parameter jobs out previous rawJob singleton : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (fields Q (suc count) input fake typ raw parameter jobs out)))
    (hp : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan OriginalHereditaryExpansion.unpackJob) previous count fake parameter)))
    (hv : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation OriginalHereditaryExpansion.unpackJob) rawJob count fake parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton rawJob z))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan Q) out (suc count) input parameter)) := by
  let F := rawScalarFromJob Q
  let p0 : Program 3 := .composition (InternalListMap.map (k := 1) F) ![.projection 0,.projection 2]
  let p1 : Program 3 := .composition F ![.projection 1,.projection 2]
  let p2 : Program 3 := .composition InternalListCodec.consCode ![p1,InternalAcceptance.constantZero 3]
  let p3 : Program 3 := .composition InternalApplicationValidityStackAppend.append ![p0,p2]
  let qs : Fin 4 → Program 3 := ![p0,p1,p2,p3]
  let xs : Fin 3 → OTerm alpha := ![previous,rawJob,typ]
  apply queryCases qs xs _
  intro beta j ys Theta hTheta hq
  simp only [graph3Rename,sucRelabel]
  let xx : Fin 3 → OTerm beta := ![previous.relabel j,rawJob.relabel j,typ.relabel j]
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ (fun k => Fin.elim0 k) i
        rfl
  rw [hxs] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph p0 (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph p1 (ys 1) xx)) := hq 1
  have q2 : Nonempty (Derivation body Theta (programGraph p2 (ys 2) xx)) := hq 2
  have q3 : Nonempty (Derivation body Theta (programGraph p3 (ys 3) xx)) := hq 3
  have hi := renameInto hi j Theta hTheta
  have hf := renameInto hf j Theta hTheta
  have hp := renameInto hp j Theta hTheta
  have hv := renameInto hv j Theta hTheta
  have hs := renameInto hs j Theta hTheta
  simp only [rowRename,fieldsRename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at hi hf hp hv hs
  have hm := binaryRecover (InternalListMap.map (k := 1) F) (.projection 0) (.projection 2)
    (ys 0) (previous.relabel j) (typ.relabel j) xx q0 (projectionValue 0 xx) (projectionValue 2 xx)
  have hx := binaryRecover F (.projection 1) (.projection 2)
    (ys 1) (rawJob.relabel j) (typ.relabel j) xx q1 (projectionValue 1 xx) (projectionValue 2 xx)
  have hms := binaryRecover InternalListCodec.consCode p1 (InternalAcceptance.constantZero 3)
    (ys 2) (ys 1) z xx q2 q1 (InternalRawListRecursionSupportProof.constantZero xx)
  have hj := binaryRecover InternalApplicationValidityStackAppend.append p0 p2
    (ys 3) (ys 0) (ys 2) xx q3 q0 q2
  exact successorAtValues Q (count.relabel j) (input.relabel j) (fake.relabel j)
    (typ.relabel j) (raw.relabel j) (parameter.relabel j) (jobs.relabel j) (out.relabel j)
    (previous.relabel j) (rawJob.relabel j) (singleton.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    hi hf hp hv hs hm hx hms hj

theorem successorCore (Q : Program 2) (count input fake typ raw parameter jobs out : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (fields Q (suc count) input fake typ raw parameter jobs out))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan Q) out (suc count) input parameter)) := by
  apply OriginalHereditaryDeletionRowsCasesProof.scanCases OriginalHereditaryExpansion.unpackJob count fake parameter _
  intro beta j Theta previous rawJob singleton hTheta hp hv hs
  simp only [graph3Rename,sucRelabel]
  have hi := renameInto hi j Theta hTheta
  have hf := renameInto hf j Theta hTheta
  simp only [rowRename,fieldsRename,sucRelabel] at hi hf
  exact successorAtSource Q (count.relabel j) (input.relabel j) (fake.relabel j)
    (typ.relabel j) (raw.relabel j) (parameter.relabel j) (jobs.relabel j) (out.relabel j)
    previous rawJob singleton hi hf hp hv hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanCoreProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanCoreProof.successorCore
