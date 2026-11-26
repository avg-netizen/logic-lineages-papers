module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeApplicationMarkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableRepresentative InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original packed constructor has literal tag two on all raw inputs. -/
theorem packedTag (d e fp ap parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationStepPeel.constructorTag (.projection 0)) (suc (suc z)) parent)) := by
  let middle : Program 4 := pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))
  let node : Program 4 := pairOf (two 4) middle
  let qs : Fin 2 → Program 4 := Fin.cons node (Fin.cons middle Fin.elim0)
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [graph1Rename,sucRelabel,zRelabel]
  have hp' := renameInto hp j Delta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm β := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hn : Nonempty (Derivation body Delta (programGraph node (ys 0) xx)) := hq 0
  have hm : Nonempty (Derivation body Delta (programGraph middle (ys 1) xx)) := hq 1
  have ht : Nonempty (Derivation body Delta (programGraph (two 4) (suc (suc z)) xx)) := by
    simpa only [positionTermEq] using (twoValue (body := body) (Gamma := Delta) xx)
  have hnode := binaryRecover InternalPairing.pairing (two 4) middle
    (ys 0) (suc (suc z)) (ys 1) xx hn ht hm
  have hparent := binaryRecover InternalPairing.pairing (.projection 1) node
    (parent.relabel j) (e.relabel j) (ys 0) xx hp' (projectionValue 1 xx) hn
  let yy : Fin 1 → OTerm β := Fin.cons (parent.relabel j) Fin.elim0
  exact unaryValue InternalUnpair.left (rightOf (.projection 0)) (suc (suc z)) (ys 0) yy
    (pairLeft (ys 0) (suc (suc z)) (ys 1) hnode)
    (unaryValue InternalUnpair.right (.projection 0) (ys 0) (parent.relabel j) yy
      (pairRight (parent.relabel j) (e.relabel j) (ys 0) hparent) (projectionValue 0 yy))

theorem rawTag (d e f a parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph1 (InternalApplicationStepPeel.constructorTag (.projection 0)) (suc (suc z)) parent)) := by
  let qs : Fin 2 → Program 4 := ![rightOf (.projection 2),rightOf (.projection 3)]
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0)))
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [graph1Rename,sucRelabel,zRelabel]
  have hp' := renameInto hp j Delta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  have hf := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (f.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0))))
    (hq 0) (projectionValue (n := 4) 2 (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)))))
  have ha := unaryRecover InternalUnpair.right (.projection 3) (ys 1) (a.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0))))
    (hq 1) (projectionValue (n := 4) 3 (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)))))
  exact packedTag (d.relabel j) (e.relabel j) (ys 0) (ys 1) (parent.relabel j)
    (applicationForward (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j)
      (ys 0) (ys 1) (parent.relabel j) hf ha hp')

theorem applicationRejectsVariable (d e f a parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest (suc z) parent).not) := by
  let V := graph1 OriginalConstructorLeaf.variableTest (suc z) parent
  let xs : Fin 1 → OTerm α := Fin.cons parent Fin.elim0
  have hzero := InternalStructuralEndpointGuardSupportProof.sameRightRecover
    (InternalApplicationStepPeel.constructorTag (.projection 0)) (InternalAcceptance.constantZero 1)
    z xs (show Nonempty (Derivation body (V :: Gamma) V) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (constantZeroValue xs)
  obtain ⟨he⟩ := valueUnique (InternalApplicationStepPeel.constructorTag (.projection 0))
    (suc (suc z)) z xs (rawTag d e f a parent (withHyp hp V)) hzero
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem nonvariableMarkZero (value : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest (suc z) value).not)) :
    Nonempty (Derivation body Gamma (markGraph z value)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  exact zeroBranchIntro
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalConstructorLeaf.variableTest)
    (InternalAcceptance.constantZero 1)
    (pairOf (InternalLessThan.constantOne 1) (.projection 0)) z xs
    (normalizeReject OriginalConstructorLeaf.variableTest xs hv) (constantZeroValue xs)

theorem applicationMarkZero (d e f a parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (markGraph z parent)) :=
  nonvariableMarkZero parent (applicationRejectsVariable d e f a parent hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeApplicationMarkProof
