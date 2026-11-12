module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalExistentialRankResultDefinitions OriginalExistentialRankResultSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fixedChild (input out d e child childOut before after : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (ho : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hc : Nonempty (Derivation body Delta (OriginalLambdaOriginalRankDefinitions.PackedRankDrop child childOut before after))) :
 Nonempty (Derivation body Delta (RankWitness input out)) :=
 rankIntro input out before after
   (OriginalLambdaOriginalRankProof.liftOriginalRanks input out child childOut d e before after hi ho hc)

theorem afterChild (input out d e child childOut before : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (ho : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hc : Nonempty (Derivation body Delta (AfterWitness child childOut before))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 obtain ⟨hc⟩ := hc
 apply Nonempty.intro
 apply Derivation.existentialElimination hc
 change Derivation body (AfterMatrix child childOut before :: Delta.map weaken) ((RankWitness input out).relabel Sum.inl)
 rw [rankWitnessRename]
 have hi' := renameInto hi Sum.inl (AfterMatrix child childOut before :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 have ho' := renameInto ho Sum.inl (AfterMatrix child childOut before :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [graph3Rename] at hi' ho'
 exact Classical.choice (fixedChild _ _ _ _ _ _ _ (.var (.inr 0)) hi' ho'
   ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem lift (input out d e child childOut : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (ho : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hc : Nonempty (Derivation body Delta (RankWitness child childOut))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 obtain ⟨hc⟩ := hc
 apply Nonempty.intro
 apply Derivation.existentialElimination hc
 change Derivation body (BeforeMatrix child childOut :: Delta.map weaken) ((RankWitness input out).relabel Sum.inl)
 rw [rankWitnessRename]
 have hi' := renameInto hi Sum.inl (BeforeMatrix child childOut :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 have ho' := renameInto ho Sum.inl (BeforeMatrix child childOut :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [graph3Rename] at hi' ho'
 exact Classical.choice (afterChild _ _ _ _ _ _ (.var (.inr 0)) hi' ho'
   ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem actualLambdaLift : OriginalExistentialRankResultLambdaTargets.ActualLambdaLift := by
 intro body alpha Delta input out d e child childOut
 let A := graph3 OriginalLambdaConstructor.constructor input d e child ⊓
   (graph3 OriginalLambdaConstructor.constructor out d e childOut ⊓ RankWitness child childOut)
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨he⟩ := lift input out d e child childOut (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
 exact ⟨Derivation.implicationIntroduction he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaProof
