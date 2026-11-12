module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem forgetExactCode (leaf : Program 4) (s t parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (OriginalTransparentDirectBottomDichotomy.Witness leaf s t parameter))) :
 Nonempty (Derivation body Delta (OriginalLambdaErasureSquareDichotomyDefinitions.Witness leaf s t parameter)) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialElimination h
 change Derivation body _ ((OriginalLambdaErasureSquareDichotomyDefinitions.Witness leaf s t parameter).relabel Sum.inl)
 rw [OriginalLambdaErasureSquareDichotomySyntaxProof.witnessRename]
 have hf : Nonempty (Derivation body
   (OriginalTransparentDirectBottomDichotomy.WitnessMatrix leaf s t parameter :: Delta.map weaken)
   (OriginalTransparentDirectBottomDichotomy.WitnessMatrix leaf s t parameter)) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hc := InternalApplicationStepPeelSupportProof.andRight hf
 exact Classical.choice (OriginalLambdaErasureSquareDichotomySyntaxProof.witnessIntro leaf
  (s.relabel Sum.inl) (t.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0)) hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankWitnessProof
