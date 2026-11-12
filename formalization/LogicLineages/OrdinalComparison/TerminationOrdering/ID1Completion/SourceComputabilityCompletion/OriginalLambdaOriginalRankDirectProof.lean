module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDirectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDirectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalBetaTotalityProof (disjunctionElimination)
open OriginalLambdaOriginalRankDefinitions
open OriginalLambdaErasureSquareDichotomyDefinitions (Witness WitnessMatrix Certificate)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A witnessed certificate supports the existing context-stable certificate
continuation. This does not attempt to extract a branch from a disjunction. -/
theorem witnessSupplier (leaf : Program 4) (s t parameter oldS oldT before after : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (Witness leaf s t parameter))) :
 ChildSupplier leaf body Delta s t parameter oldS oldT before after := by
 intro psi he hc
 obtain ⟨hw⟩ := hw
 apply Nonempty.intro
 apply Derivation.existentialElimination hw
 change Derivation body (WitnessMatrix leaf s t parameter :: Delta.map weaken)
  (psi.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 apply Classical.choice
 apply hc (alpha ⊕ Fin 1) Sum.inl (WitnessMatrix leaf s t parameter :: Delta.map weaken) (.var (.inr 0))
 · intro f hf
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualDirectCongruence : OriginalLambdaOriginalRankDirectTargets.ActualDirectCongruence := by
 intro source oldStep endpoint window body alpha Delta s t parameter childS childT childParam
  d e context gamma extended oldS oldT oldChildS oldChildT before after
 dsimp only
 intro hf holdS holdT hresult
 let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
  (OriginalTransparentLambdaStep.refined source oldStep)
 let A := equal childS childT ⊓ PackedRankDrop oldChildS oldChildT before after
 let B := Witness leaf childS childT childParam
 have left : Nonempty (Derivation body (A :: Delta) (Result leaf s t parameter oldS oldT before after)) := by
  apply OriginalLambdaOriginalRankDichotomyProof.actualLocalRankedCongruence source oldStep endpoint window
   body alpha (A :: Delta) s t parameter childS childT childParam d e context gamma extended
   oldS oldT oldChildS oldChildT before after (withHyp hf A) (withHyp holdS A) (withHyp holdT A)
  intro psi he hc
  exact he ⟨Derivation.hypothesis List.mem_cons_self⟩
 have right : Nonempty (Derivation body (B :: Delta) (Result leaf s t parameter oldS oldT before after)) := by
  apply OriginalLambdaOriginalRankDichotomyProof.actualLocalRankedCongruence source oldStep endpoint window
   body alpha (B :: Delta) s t parameter childS childT childParam d e context gamma extended
   oldS oldT oldChildS oldChildT before after (withHyp hf B) (withHyp holdS B) (withHyp holdT B)
  exact witnessSupplier leaf childS childT childParam oldChildS oldChildT before after
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hresult⟩ := hresult
 obtain ⟨left⟩ := left
 obtain ⟨right⟩ := right
 exact ⟨disjunctionElimination hresult (Derivation.implicationIntroduction left)
  (Derivation.implicationIntroduction right)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDirectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDirectProof
