module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryAtSharedTapesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCertifiedTargetTypedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (certificate)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectCoreInstalledCertificateProof (exact_InstalledCertificateSharedTape)
open NumberedWindowInternalDirectBoundaryAtSharedTapesProof (exact_OpenBoundaryAtSharedTapes)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameParser)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atSame (i : Program 1) (r a b : OTerm α)
    (actual : Nonempty (Derivation B Γ (unary parser (suc a) r)))
    (known : Nonempty (Derivation B Γ (unary parser (suc b) r)))
    (p : Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) a))) :
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) b)) := by
  obtain ⟨e⟩ := valueUnique parser (suc a) (suc b) ![r] actual known
  exact headTransport (typedScratch i) (suc z) a b Fin.elim0 ⟨cancelSuc e⟩ p

/-- A genuine exact original odd certificate already types its target.
Identify the boundary scratch at the same physical raw target and
transport that very typing derivation to its held parser output. -/
theorem exact_OriginalLiteralCertifiedTargetTyped (i : Program 1) (r : Program 3) (c : Nat)
    (source target witness desired : OTerm α)
    (step : Pr (literalData i r) c Γ (certificate (literalData i r) true c source target witness))
    (seen : Pr (literalData i r) c Γ (unary parser (suc desired) target)) :
    Pr (literalData i r) c Γ (unary (typedScratch i) (suc z) desired) := by
  let goal := unary (typedScratch i) (suc z) desired
  apply exact_InstalledCertificateSharedTape i (jRaw i) r permutation c α Γ source witness target goal step
  intro β j Δ rawK rawD rawA ds dt dk dd da dp sk tp keep _ _ bound run
  let src := source.relabel j
  let dst := target.relabel j
  apply exact_OpenBoundaryAtSharedTapes i src dst rawD ds dt dd
    ⟨run.sourceParsed,run.targetParsed,run.removedParsed⟩ bound (goal.relabel j)
  intro γ k Ω _ _ carry _ trueTyped _
  have targetView := renameParser dst dt run.targetParsed k Ω carry
  have held := renameParser target desired seen (k ∘ j) Ω (keepThrough j k keep carry)
  simp only [goal,unaryRename,sucRelabel,zRelabel]
  exact atSame i (dst.relabel k) (dt.relabel k) ((desired.relabel j).relabel k)
    targetView (by simpa only [← Term.relabel_relabel,dst] using held) trueTyped

#print axioms exact_OriginalLiteralCertifiedTargetTyped
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCertifiedTargetTypedProof
