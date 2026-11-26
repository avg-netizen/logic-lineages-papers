module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSupportProof (refl)
open InternalQuotientComparisonProof (equalToNext)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem selfBound (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc raw))) :=
  ⟨equalToNext (refl raw)⟩

theorem toOwn (n : Nat) (raw previous child : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 (OriginalCodeDecoderTable.tableProgram n) previous raw raw)))
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) child previous))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalCodeDecoderTable.tableProgram n)
    (Fin.cons (suc child) (Fin.cons child Fin.elim0)) _
  intro beta j Theta own hj ho
  simp only [consTermRename,emptyRename,sucRelabel] at ho
  simp only [graph1Rename,graph2Rename,InternalTagArithmeticSyntaxProof.zRelabel,sucRelabel]
  have ht' := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph2Rename] at ht'
  have hc' := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [InternalLessThan.strictLess,orderRename] at hc'
  have ha' := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,InternalTagArithmeticSyntaxProof.zRelabel,sucRelabel] at ha'
  have hb := OriginalCodeValidityCoherence.StageProof.childBound (child.relabel j) (raw.relabel j)
    (raw.relabel j) hc' (selfBound _)
  have hl := OriginalCodeValidityCoherence.Proof.transport n (child.relabel j)
    (raw.relabel j) (raw.relabel j) (previous.relabel j) (suc (child.relabel j)) (child.relabel j) own
    hb (selfBound _) hc' (selfBound _) ht' ho ha'
  exact SupportProof.checkIntro n (child.relabel j) own (suc z) ho hl

theorem fromOwn (n : Nat) (raw previous child : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 (OriginalCodeDecoderTable.tableProgram n) previous raw raw)))
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) child previous)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalCodeDecoderTable.tableProgram n)
    (Fin.cons (suc child) (Fin.cons child Fin.elim0)) _
  intro beta j Theta own hj ho
  simp only [consTermRename,emptyRename,sucRelabel] at ho
  simp only [graph1Rename,graph2Rename,InternalTagArithmeticSyntaxProof.zRelabel,sucRelabel]
  have ht' := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph2Rename] at ht'
  have hc' := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [InternalLessThan.strictLess,orderRename] at hc'
  have ha' := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,InternalTagArithmeticSyntaxProof.zRelabel,sucRelabel] at ha'
  have hb := OriginalCodeValidityCoherence.StageProof.childBound (child.relabel j) (raw.relabel j)
    (raw.relabel j) hc' (selfBound _)
  have hl := SupportProof.checkRecover n (child.relabel j) own (suc z) ho ha'
  exact OriginalCodeValidityCoherence.Proof.transport n (child.relabel j)
    (suc (child.relabel j)) (child.relabel j) own (raw.relabel j) (raw.relabel j) (previous.relabel j)
    (selfBound _) hb (selfBound _) hc' ho ht' hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ChildProof
