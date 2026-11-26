module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (refl symm)
open OriginalLambdaTraversalLambdaRootProof (binaryInputs)
open InternalRecursionClosureLogicProof (closedApply)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open UnaryMapAppendSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map
  InternalApplicationValidityStackAppend.append InternalListCodec.consCode

theorem mapZero (F : Program 1) (parameter : OTerm alpha) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) z z)) := by
  obtain ⟨law⟩ := InternalListMapProof.actualOriginalListMapZero body 0 F alpha z Fin.elim0
  have hr : Nonempty (Derivation body Delta (equal z z)) := by
    rw [equalEqn]
    exact ⟨refl z⟩
  exact closedApply ⟨Derivation.conjunctionRight law⟩ hr

theorem zeroCore (F : Program 1) (right joined parameter mappedLeft mappedRight out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields F z right joined parameter mappedLeft mappedRight out))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out joined)) := by
  let M := InternalListMap.map (k := 0) F
  obtain ⟨joinedEq⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover
    joined right (andLeft hf)
  obtain ⟨leftEq⟩ := valueUnique M mappedLeft z ![z]
    (andLeft (andRight hf)) (mapZero F parameter)
  have hz := binaryInputs InternalApplicationValidityStackAppend.append out mappedLeft mappedRight
    z mappedRight ⟨leftEq⟩ ⟨refl mappedRight⟩ (andRight (andRight (andRight hf)))
  obtain ⟨outEq⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover out mappedRight hz
  have mappedJoined := headTransport M mappedRight right joined Fin.elim0
    ⟨symm joinedEq⟩ (andLeft (andRight (andRight hf)))
  exact outputTransport M mappedRight out ![joined] ⟨symm outEq⟩ mappedJoined

theorem consAtValues (F : Program 1)
    (code head tail right joined parameter mappedLeft mappedRight out tailJoined mappedHead mappedTail tailOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row F tail)))
    (hf : Nonempty (Derivation body Delta (fields F code right joined parameter mappedLeft mappedRight out)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailJoined tail right)))
    (hh : Nonempty (Derivation body Delta (graph1 F mappedHead head)))
    (ht : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) mappedTail tail)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailOut mappedTail mappedRight))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out joined)) := by
  have joinedCons := InternalApplicationValidityStackAppendListProof.consForward
    code head tail right tailJoined joined hc hj (andLeft hf)
  have mappedCons := InternalListMapProof.consForward F code head tail mappedHead mappedTail mappedLeft
    Fin.elim0 hc hh ht (andLeft (andRight hf))
  have outCons := InternalApplicationValidityStackAppendListProof.consForward
    mappedLeft mappedHead mappedTail mappedRight tailOut out mappedCons ho (andRight (andRight (andRight hf)))
  have tailMapped := rowApply F tail right tailJoined parameter mappedTail mappedRight tailOut hi
    (andIntro hj (andIntro ht (andIntro (andLeft (andRight (andRight hf))) ho)))
  exact InternalListMapProof.consBackward F joined head tailJoined mappedHead tailOut out
    Fin.elim0 joinedCons hh tailMapped outCons

/-- The actual tail map, head computation and both suffix append outputs are
queried internally. No map/append supplier is assumed by the successor step. -/
theorem consCore (F : Program 1)
    (code head tail right joined parameter mappedLeft mappedRight out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row F tail)))
    (hf : Nonempty (Derivation body Delta (fields F code right joined parameter mappedLeft mappedRight out))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out joined)) := by
  let q0 : Program 5 := .composition InternalApplicationValidityStackAppend.append ![.projection 1,.projection 2]
  let q1 : Program 5 := .composition F (fun _ : Fin 1 => .projection 0)
  let q2 : Program 5 := .composition (InternalListMap.map (k := 0) F) (fun _ : Fin 1 => .projection 1)
  let q3 : Program 5 := .composition InternalApplicationValidityStackAppend.append ![q2,.projection 4]
  let qs : Fin 4 → Program 5 := ![q0,q1,q2,q3]
  let xs : Fin 5 → OTerm alpha := ![head,tail,right,parameter,mappedRight]
  apply queryCases qs xs _
  intro beta j ys Theta hTheta hq
  simp only [graph1Rename,graph2Rename]
  let xx : Fin 5 → OTerm beta :=
    ![head.relabel j,tail.relabel j,right.relabel j,parameter.relabel j,mappedRight.relabel j]
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro i
            refine Fin.cases ?_ (fun k => Fin.elim0 k) i
            rfl
  rw [hxs] at hq
  have p0 : Nonempty (Derivation body Theta (programGraph q0 (ys 0) xx)) := hq 0
  have p1 : Nonempty (Derivation body Theta (programGraph q1 (ys 1) xx)) := hq 1
  have p2 : Nonempty (Derivation body Theta (programGraph q2 (ys 2) xx)) := hq 2
  have p3 : Nonempty (Derivation body Theta (programGraph q3 (ys 3) xx)) := hq 3
  have hc := renameInto hc j Theta hTheta
  have hi := renameInto hi j Theta hTheta
  have hf := renameInto hf j Theta hTheta
  simp only [graph1Rename,graph2Rename,rowRename,fieldsRename] at hc hi hf
  have joinedValue := binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) (.projection 2)
    (ys 0) (tail.relabel j) (right.relabel j) xx p0 (projectionValue 1 xx) (projectionValue 2 xx)
  have headValue := unaryRecover F (.projection 0)
    (ys 1) (head.relabel j) xx p1 (projectionValue 0 xx)
  have tailValue := unaryRecover (InternalListMap.map (k := 0) F) (.projection 1)
    (ys 2) (tail.relabel j) xx p2 (projectionValue 1 xx)
  have outValue := binaryRecover InternalApplicationValidityStackAppend.append q2 (.projection 4)
    (ys 3) (ys 2) (mappedRight.relabel j) xx p3 p2 (projectionValue 4 xx)
  exact consAtValues F (code.relabel j) (head.relabel j) (tail.relabel j)
    (right.relabel j) (joined.relabel j) (parameter.relabel j) (mappedLeft.relabel j)
    (mappedRight.relabel j) (out.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    hc hi hf joinedValue headValue tailValue outValue

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendCoreProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendCoreProof.consCore
