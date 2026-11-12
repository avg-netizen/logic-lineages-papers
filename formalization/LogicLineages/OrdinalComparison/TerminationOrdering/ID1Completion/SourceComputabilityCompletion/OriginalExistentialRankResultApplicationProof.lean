module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open OriginalExistentialRankResultDefinitions OriginalExistentialRankResultSyntaxProof
open OriginalLambdaOriginalRankDefinitions (PackedRankDrop)
open OriginalRawSyntaxTransport (variableRankPackedRaw)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRanks (input out d e fn fnOut arg before after childBefore childAfter : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
 (hc : Nonempty (Derivation body Delta (PackedRankDrop fn fnOut childBefore childAfter)))
 (hb : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw before input)))
 (ha : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw after out))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 have hl := OriginalApplicationFunctionRankProof.liftFunction input out d e fn fnOut arg
   before after childBefore childAfter hi ho (andLeft hc) (andLeft (andRight hc)) hb ha (andRight (andRight hc))
 exact rankIntro input out before after (andIntro hb (andIntro ha hl))

theorem atBefore (input out d e fn fnOut arg before childBefore childAfter : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
 (hc : Nonempty (Derivation body Delta (PackedRankDrop fn fnOut childBefore childAfter)))
 (hb : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw before input))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 apply programCases variableRankPackedRaw (Fin.cons out Fin.elim0) _
 intro beta j Theta after hj ha
 rw [rankWitnessRename]
 have hi' := renameInto hi j Theta hj
 have ho' := renameInto ho j Theta hj
 have hc' := renameInto hc j Theta hj
 have hb' := renameInto hb j Theta hj
 rw [graph4Rename] at hi' ho'
 rw [OriginalLambdaOriginalRankDichotomyProof.rankDropRename] at hc'
 rw [graph1Rename] at hb'
 have ha' : Nonempty (Derivation body Theta (graph1 variableRankPackedRaw after (out.relabel j))) := by
   simpa only [graph1,consTermRename,emptyRename] using ha
 exact atRanks _ _ _ _ _ _ _ _ _ _ _ hi' ho' hc' hb' ha'

theorem fixedChild (input out d e fn fnOut arg childBefore childAfter : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
 (hc : Nonempty (Derivation body Delta (PackedRankDrop fn fnOut childBefore childAfter))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 apply programCases variableRankPackedRaw (Fin.cons input Fin.elim0) _
 intro beta j Theta before hj hb
 rw [rankWitnessRename]
 have hi' := renameInto hi j Theta hj
 have ho' := renameInto ho j Theta hj
 have hc' := renameInto hc j Theta hj
 rw [graph4Rename] at hi' ho'
 rw [OriginalLambdaOriginalRankDichotomyProof.rankDropRename] at hc'
 have hb' : Nonempty (Derivation body Theta (graph1 variableRankPackedRaw before (input.relabel j))) := by
   simpa only [graph1,consTermRename,emptyRename] using hb
 exact atBefore _ _ _ _ _ _ _ _ _ _ hi' ho' hc' hb'

theorem afterChild (input out d e fn fnOut arg childBefore : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
 (hc : Nonempty (Derivation body Delta (AfterWitness fn fnOut childBefore))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 obtain ⟨hc⟩ := hc
 apply Nonempty.intro
 apply Derivation.existentialElimination hc
 change Derivation body (AfterMatrix fn fnOut childBefore :: Delta.map weaken) ((RankWitness input out).relabel Sum.inl)
 rw [rankWitnessRename]
 have hi' := renameInto hi Sum.inl (AfterMatrix fn fnOut childBefore :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 have ho' := renameInto ho Sum.inl (AfterMatrix fn fnOut childBefore :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [graph4Rename] at hi' ho'
 exact Classical.choice (fixedChild _ _ _ _ _ _ _ _ (.var (.inr 0)) hi' ho'
   ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem lift (input out d e fn fnOut arg : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
 (hc : Nonempty (Derivation body Delta (RankWitness fn fnOut))) :
 Nonempty (Derivation body Delta (RankWitness input out)) := by
 obtain ⟨hc⟩ := hc
 apply Nonempty.intro
 apply Derivation.existentialElimination hc
 change Derivation body (BeforeMatrix fn fnOut :: Delta.map weaken) ((RankWitness input out).relabel Sum.inl)
 rw [rankWitnessRename]
 have hi' := renameInto hi Sum.inl (BeforeMatrix fn fnOut :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 have ho' := renameInto ho Sum.inl (BeforeMatrix fn fnOut :: Delta.map weaken)
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [graph4Rename] at hi' ho'
 exact Classical.choice (afterChild _ _ _ _ _ _ _ (.var (.inr 0)) hi' ho'
   ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem actualApplicationFunctionLift : OriginalExistentialRankResultTargets.ActualApplicationFunctionLift := by
 intro body alpha Delta input out d e fn fnOut arg
 let A := graph4 application input d e fn arg ⊓ (graph4 application out d e fnOut arg ⊓ RankWitness fn fnOut)
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨he⟩ := lift input out d e fn fnOut arg (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
 exact ⟨Derivation.implicationIntroduction he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultApplicationProof
