module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalExistentialRankResultDefinitions
open OriginalLambdaErasureSquareDichotomyDefinitions (Witness WitnessMatrix Certificate)
open OriginalLambdaErasureSquareDichotomySyntaxProof (witnessRename localOrRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem resultRename {beta : Type} (leaf : Program 4) (s t parameter oldS oldT : OTerm alpha) (j : alpha → beta) :
 (Result leaf s t parameter oldS oldT).relabel j =
 Result leaf (s.relabel j) (t.relabel j) (parameter.relabel j) (oldS.relabel j) (oldT.relabel j) := by
 simp only [Result,localOrRename,InternalRecursionGraphStepSyntaxProof.conjunctionRename,
  OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,
  OriginalExistentialRankResultSyntaxProof.rankWitnessRename,witnessRename]

theorem mapWitness (leaf : Program 4) (s t parameter childS childT childParam : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (Witness leaf childS childT childParam)))
 (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (cert : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (Certificate leaf (childS.relabel j) (childT.relabel j) (childParam.relabel j) cert)) →
  Nonempty (Derivation body Theta (Witness leaf (s.relabel j) (t.relabel j) (parameter.relabel j)))) :
 Nonempty (Derivation body Delta (Witness leaf s t parameter)) := by
 obtain ⟨hw⟩ := hw
 apply Nonempty.intro
 apply Derivation.existentialElimination hw
 change Derivation body (WitnessMatrix leaf childS childT childParam :: Delta.map weaken)
  ((Witness leaf s t parameter).relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 rw [witnessRename]
 exact Classical.choice (step (alpha ⊕ Fin 1) Sum.inl
  (WitnessMatrix leaf childS childT childParam :: Delta.map weaken) (.var (.inr 0))
  (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
