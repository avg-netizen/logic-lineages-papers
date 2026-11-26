module
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupTailProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open NumberedWindowInternalSparseFieldParser (scratchBase scratchStep scratchTable scratchRow)
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalScratchMemoThinLookupSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tableTail (B : Program 2) (R : Program 4)
    (old out index : OTerm alpha) (params : Fin 2 → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (memoGraph B R old index params)))
    (hs : Nonempty (Derivation body Delta (memoGraph B R out (suc index) params))) :
    Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode old out)) := by
  have ht := recursionRecover (scratchBase B) (scratchStep R) out old index params hp hs
  apply programCases R (Fin.cons index (Fin.cons old params)) _
  intro beta j Theta value hj hv
  rw [graph1Rename]
  simp only [consTermRename] at hv
  have ht' := renameInto ht j Theta hj
  simp only [programRename,consTermRename] at ht'
  let xs : Fin 4 → OTerm beta := Fin.cons (index.relabel j) (Fin.cons (old.relabel j) (fun i => (params i).relabel j))
  have hc := binaryRecover InternalListCodec.consCode R (.projection 1)
    (out.relabel j) value (old.relabel j) xs ht' hv (projectionValue 1 xs)
  obtain ⟨consFields⟩ := InternalListCodecSupportProof.consDestruction (out.relabel j) value (old.relabel j) hc
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight consFields)⟩

theorem memoHead (B : Program 2) (R : Program 4)
    (out code tab : OTerm alpha) (params : Fin 2 → OTerm alpha)
    (hr : Nonempty (Derivation body Delta (memoRowGraph B R out code params)))
    (ht : Nonempty (Derivation body Delta (memoGraph B R tab code params))) :
    Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out tab)) :=
  unaryRecover InternalListCodec.headCode (scratchTable B R) out tab (Fin.cons code params) hr ht

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupTailProof
