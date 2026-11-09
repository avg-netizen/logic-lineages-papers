module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open InternalPositiveUnfoldingSupportProof
open SourceComputabilityCompletion.BottomRepresentative
open SourceComputabilityCompletion.BottomDescent SourceComputabilityCompletion.BottomDescentSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def bottomPayload : Program 1 := pairOf (constant 3) (.projection 0)

theorem bottomCodeProgram : bottomCode = .composition InternalPairing.pairing
    (Fin.cons (.projection (0 : Fin 1)) (Fin.cons bottomPayload Fin.elim0)) := rfl

theorem bottomCodeLeft (input typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 bottomCode input typ))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)) := by
  let pay : Program 1 := bottomPayload
  apply programCases pay (Fin.cons typ Fin.elim0) _
  intro β j Delta payload hj hv
  rw [graph1Rename]
  have h' := renameInto h j Delta hj
  rw [graph1Rename] at h'
  rw [bottomCodeProgram] at h'
  have hv' : Nonempty (Derivation body Delta (graph1 pay payload (typ.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hv
  let xs : Fin 1 → OTerm β := Fin.cons (typ.relabel j) Fin.elim0
  have hp := compositionRecover InternalPairing.pairing
    (Fin.cons (.projection (0 : Fin 1)) (Fin.cons pay Fin.elim0))
    (input.relabel j) xs (Fin.cons (typ.relabel j) (Fin.cons payload Fin.elim0)) h'
    (fun i => Fin.cases (projectionValue 0 xs) (Fin.cases hv' (fun k => Fin.elim0 k)) i)
  exact pairLeft (input.relabel j) (typ.relabel j) payload hp

theorem bottomAccept (input typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 bottomCode input typ))) :
    Nonempty (Derivation body Gamma (bottomGraph (suc z) input)) := by
  let xs : Fin 1 → OTerm α := Fin.cons input Fin.elim0
  have hl := unaryValue InternalUnpair.left (.projection (0 : Fin 1)) typ input xs
    (bottomCodeLeft input typ h) (projectionValue 0 xs)
  have hc := unaryValue bottomCode (leftOf (.projection (0 : Fin 1))) input typ xs h hl
  exact sameAccept (.projection (0 : Fin 1))
    (.composition bottomCode (fun _ : Fin 1 => leftOf (.projection 0))) input xs (projectionValue 0 xs) hc

/-- The exact bottom test together with the ORIGINAL outer type field
reconstructs the entire literal bottom code. No decoder or semantic theorem. -/
theorem bottomRecover (input typ : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph (suc z) input))) :
    Nonempty (Derivation body Gamma (graph1 bottomCode input typ)) := by
  apply programCases bottomCode (Fin.cons typ Fin.elim0) _
  intro β j Delta candidate hj hc
  rw [graph1Rename]
  have hc' : Nonempty (Derivation body Delta (graph1 bottomCode candidate (typ.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hc
  have hl' := renameInto hl j Delta hj
  rw [graph1Rename] at hl'
  have hb' := renameInto hb j Delta hj
  simp only [bottomGraph,graph1Rename,sucRelabel,zRelabel] at hb'
  let xs : Fin 1 → OTerm β := Fin.cons (input.relabel j) Fin.elim0
  have hleft := unaryValue InternalUnpair.left (.projection (0 : Fin 1))
    (typ.relabel j) (input.relabel j) xs hl' (projectionValue 0 xs)
  have hcode := unaryValue bottomCode (leftOf (.projection (0 : Fin 1)))
    candidate (typ.relabel j) xs hc' hleft
  have hp := sameRightRecover (.projection (0 : Fin 1))
    (.composition bottomCode (fun _ : Fin 1 => leftOf (.projection 0))) candidate xs hb' hcode
  have he := valueUnique (.projection (0 : Fin 1)) candidate (input.relabel j) xs hp (projectionValue 0 xs)
  exact outputTransport bottomCode candidate (input.relabel j) (Fin.cons (typ.relabel j) Fin.elim0) he hc'

/-- Raw bottom fixedness needs only ONE transition, whose literal guard
already preserves the original type field. Full iteration is unnecessary. -/
theorem bottomStepFixed (data : Data) (window : Program 1) (input typ parameter : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hc : Nonempty (Derivation body Gamma (graph1 bottomCode input typ))) :
    Nonempty (Derivation body Gamma (graph2 (step data window) input input parameter)) := by
  apply programCases (step data window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta next hj ht
  rw [graph2Rename]
  have ht' : Nonempty (Derivation body Delta
      (graph2 (step data window) next (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using ht
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hc' := renameInto hc j Delta hj
  rw [graph1Rename] at hc'
  have hleft := bottomCodeLeft (input.relabel j) (typ.relabel j) hc'
  have hb := bottomAccept (input.relabel j) (typ.relabel j) hc'
  have hbnext := BottomDescentStepProof.forwardStep data window next (input.relabel j)
    (parameter.relabel j) (suc z) ha' hb ht'
  have hlnext := InternalParameterizedBoundedDescentNormalizerStepProof.stepLeft
    (representative data window) (selectedValidity data window) next (input.relabel j)
    (typ.relabel j) (parameter.relabel j) ht' hleft
  have hcnext := bottomRecover next (typ.relabel j) hlnext hbnext
  have he := valueUnique bottomCode next (input.relabel j) (Fin.cons (typ.relabel j) Fin.elim0) hcnext hc'
  exact outputTransport (step data window) next (input.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
