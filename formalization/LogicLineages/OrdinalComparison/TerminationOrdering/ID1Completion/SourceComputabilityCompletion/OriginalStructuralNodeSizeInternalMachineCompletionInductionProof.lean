module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExistenceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExistenceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof OriginalStructuralNodeSizeInternalMachineCompletionRawBindingProof
open OriginalStructuralNodeSizeInternalMachineCompletionRawSyntaxProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafCase (d k raw : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z raw))) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) := by
  apply programCases (constant 3 1) (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,zRelabel] at ha'
  simp only [consTermRename,emptyRename] at hp
  exact OriginalStructuralNodeSizeInternalMachineCompletionLeafProof.leafHasCompletion
    (d.relabel j) (k.relabel j) (raw.relabel j) (raw.relabel j) produced ha' hp

def unaryQueries : Fin 2 → Program 2 :=
  ![.composition (firstOf (.projection 0)) (fun _ : Fin 1 => .projection 1),nextCutoff]

theorem unaryCase (d k raw : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc z) raw)))
    (hi : Nonempty (Derivation positive Delta (belowRaw raw))) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) := by
  apply queryCases unaryQueries (Fin.cons k (Fin.cons raw Fin.elim0)) _
  intro beta j ys Theta hj hq
  rw [hasCompletionRename]
  simp only [consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at ha'
  rw [belowRawRename] at hi'
  let xs : Fin 2 → OTerm beta := ![k.relabel j,raw.relabel j]
  have hfirst := unaryRecover (firstOf (.projection 0)) (.projection 1) (ys 0) (raw.relabel j) xs
    (hq 0) (projectionValue 1 xs)
  have hb := unaryChildBound (raw.relabel j) (ys 0) ha' hfirst
  exact OriginalStructuralNodeSizeInternalMachineExistenceUnaryProof.fromChild
    (d.relabel j) (k.relabel j) (raw.relabel j) (ys 0) (ys 1)
    (andIntro ha' (andIntro hfirst (hq 1))) hb
    (belowRawApply (raw.relabel j) (ys 0) (d.relabel j) (ys 1) hi'
      (unaryChildStrict (raw.relabel j) (ys 0) ha' hfirst))

theorem binaryCase (d k raw : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hi : Nonempty (Derivation positive Delta (belowRaw raw))) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) := by
  apply queryCases ![firstOf (.projection 0),secondOf (.projection 0)] (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [hasCompletionRename]
  simp only [consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at ha'
  rw [belowRawRename] at hi'
  have hb := binaryChildBound (raw.relabel j) (ys 0) (ys 1) ha' (hq 0) (hq 1)
  have hlt := binaryChildrenStrict (raw.relabel j) (ys 0) (ys 1) ha' (hq 0) (hq 1)
  exact OriginalStructuralNodeSizeInternalMachineExistenceBinaryProof.fromChildren
    (d.relabel j) (k.relabel j) (raw.relabel j) (ys 0) (ys 1)
    (andIntro ha' (andIntro (hq 0) (hq 1))) hb
    (belowRawApply (raw.relabel j) (ys 0) (d.relabel j) (k.relabel j) hi' (andLeft hlt))
    (belowRawApply (raw.relabel j) (ys 1) (d.relabel j) (k.relabel j) hi' (andRight hlt))

theorem stepAtInput (d k raw : OTerm alpha)
    (hi : Nonempty (Derivation positive Delta (belowRaw raw))) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) := by
  apply arityCases raw _
  · intro beta j Theta hj ha
    rw [hasCompletionRename]
    exact leafCase (d.relabel j) (k.relabel j) (raw.relabel j) ha
  · intro beta j Theta hj ha
    rw [hasCompletionRename]
    have hi' := renameInto hi j Theta hj
    rw [belowRawRename] at hi'
    exact unaryCase (d.relabel j) (k.relabel j) (raw.relabel j) ha hi'
  · intro beta j Theta hj ha
    rw [hasCompletionRename]
    have hi' := renameInto hi j Theta hj
    rw [belowRawRename] at hi'
    exact binaryCase (d.relabel j) (k.relabel j) (raw.relabel j) ha hi'

theorem rawStep (raw : OTerm alpha)
    (hi : Nonempty (Derivation positive Delta (belowRaw raw))) :
    Nonempty (Derivation positive Delta (AtRaw raw)) := by
  let Theta : List (Formula (alpha ⊕ Fin 2)) :=
    Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have hi' := renameInto hi (Sum.inl : alpha → alpha ⊕ Fin 2) Theta (by
    intro p hp
    exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hi'
  have h := stepAtInput (positive := positive) (alpha := alpha ⊕ Fin 2) (Delta := Theta)
    (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2)))
    (raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)) hi'
  exact atRawIntro (body := positive) (α := alpha) (Gamma := Delta) raw h

/-- The actual original traversal has a bounded stack continuation for EVERY
raw arithmetic input. This induction is a Derivation in the original calculus. -/
theorem allRaw (raw : OTerm alpha) :
    Nonempty (Derivation positive Delta (AtRaw raw)) := by
  apply rawInduction raw
  intro beta Theta value hi
  exact rawStep value hi

theorem hasCompletion (d k raw : OTerm alpha) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) :=
  atRawApply raw d k (allRaw raw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionInductionProof
