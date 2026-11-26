module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename recursionZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consDestruction)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open NumberedWindowInternalSparseFieldParser (scratchBase scratchStep scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverSelectedMemoZero : ExactOpenCoverSelectedMemoZero := by
  intro R body α Γ
  apply programCases consCode (![z,z] : Fin 2 → OTerm α) _
  intro β j Δ base keep hcons
  simp only [binaryInputsRename,zRelabel] at hcons
  simp only [unaryRename,zRelabel]
  let zeros : Fin 2 → OTerm β := ![z,z]
  have actualBase : Nonempty (Derivation body Δ (programGraph (scratchBase (constantZero 2)) base zeros)) := by
    apply compositionValue consCode ![constantZero 2,constantZero 2] base zeros zeros hcons
    intro i
    exact Fin.cases (zeroConstantValue zeros)
      (Fin.cases (zeroConstantValue zeros) (fun k => Fin.elim0 k)) i
  have table := recursionZeroValue (scratchBase (constantZero 2)) (scratchStep R) base zeros actualBase
  obtain ⟨fields⟩ := consDestruction base z z hcons
  apply (projection R z z).mpr
  apply compositionValue headCode (fun _ : Fin 1 => scratchTable (constantZero 2) R)
    z ![z,z,z] ![base] ⟨Derivation.conjunctionLeft fields⟩
  intro i
  obtain rfl := Fin.eq_zero i
  exact table

#print axioms exact_OpenCoverSelectedMemoZero

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
