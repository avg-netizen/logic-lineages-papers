module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionBindingProof OriginalRawSyntaxTransportInternalMachineCompletionRawBindingProof
open OriginalRawSyntaxTransportInternalMachineCompletionRawSyntaxProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafCase (mode : Mode) (d k raw : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z raw))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply programCases (leaf mode) (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,zRelabel] at ha'
  simp only [consTermRename,emptyRename] at hp
  exact OriginalRawSyntaxTransportInternalMachineCompletionLeafProof.leafHasCompletion mode
    (d.relabel j) (k.relabel j) (raw.relabel j) (raw.relabel j) produced ha' hp

def unaryQueries : Fin 2 → Program 2 :=
  ![.composition (firstOf (.projection 0)) (fun _ : Fin 1 => .projection 1),nextCutoff]

theorem unaryCase (mode : Mode) (d k raw : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc z) raw)))
    (hi : Nonempty (Derivation positive Delta (belowRaw mode raw))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
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
  exact OriginalRawSyntaxTransportInternalMachineExistenceUnaryProof.fromChild mode
    (d.relabel j) (k.relabel j) (raw.relabel j) (ys 0) (ys 1)
    (andIntro ha' (andIntro hfirst (hq 1))) hb
    (belowRawApply mode (raw.relabel j) (ys 0) (d.relabel j) (ys 1) hi'
      (unaryChildStrict (raw.relabel j) (ys 0) ha' hfirst))

theorem binaryCase (mode : Mode) (d k raw : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hi : Nonempty (Derivation positive Delta (belowRaw mode raw))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
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
  exact OriginalRawSyntaxTransportInternalMachineExistenceBinaryProof.fromChildren mode
    (d.relabel j) (k.relabel j) (raw.relabel j) (ys 0) (ys 1)
    (andIntro ha' (andIntro (hq 0) (hq 1))) hb
    (belowRawApply mode (raw.relabel j) (ys 0) (d.relabel j) (k.relabel j) hi' (andLeft hlt))
    (belowRawApply mode (raw.relabel j) (ys 1) (d.relabel j) (k.relabel j) hi' (andRight hlt))

theorem stepAtInput (mode : Mode) (d k raw : OTerm alpha)
    (hi : Nonempty (Derivation positive Delta (belowRaw mode raw))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply arityCases raw _
  · intro beta j Theta hj ha
    rw [hasCompletionRename]
    exact leafCase mode (d.relabel j) (k.relabel j) (raw.relabel j) ha
  · intro beta j Theta hj ha
    rw [hasCompletionRename]
    have hi' := renameInto hi j Theta hj
    rw [belowRawRename] at hi'
    exact unaryCase mode (d.relabel j) (k.relabel j) (raw.relabel j) ha hi'
  · intro beta j Theta hj ha
    rw [hasCompletionRename]
    have hi' := renameInto hi j Theta hj
    rw [belowRawRename] at hi'
    exact binaryCase mode (d.relabel j) (k.relabel j) (raw.relabel j) ha hi'

theorem rawStep (mode : Mode) (raw : OTerm alpha)
    (hi : Nonempty (Derivation positive Delta (belowRaw mode raw))) :
    Nonempty (Derivation positive Delta (AtRaw mode raw)) := by
  let Theta : List (Formula (alpha ⊕ Fin 2)) :=
    Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have hi' := renameInto hi (Sum.inl : alpha → alpha ⊕ Fin 2) Theta (by
    intro p hp
    exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hi'
  have h := stepAtInput (positive := positive) (alpha := alpha ⊕ Fin 2) (Delta := Theta)
    mode (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2)))
    (raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)) hi'
  exact atRawIntro (body := positive) (α := alpha) (Gamma := Delta) mode raw h

/-- The actual original traversal has a bounded stack continuation for EVERY
raw arithmetic input. This induction is a Derivation in the original calculus. -/
theorem allRaw (mode : Mode) (raw : OTerm alpha) :
    Nonempty (Derivation positive Delta (AtRaw mode raw)) := by
  apply rawInduction mode raw
  intro beta Theta value hi
  exact rawStep mode value hi

theorem hasCompletion (mode : Mode) (d k raw : OTerm alpha) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) :=
  atRawApply mode raw d k (allRaw mode raw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionInductionProof
