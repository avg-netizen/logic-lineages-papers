module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumInductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionBinding
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open RankArgumentDefinitions RankArgumentInductionDefinitions RankArgumentInductionSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {k : Nat}
variable (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
theorem atRawApply (parameter gamma c bound raw types observations rank : OTerm alpha)
 (params : Fin k → OTerm alpha)
 (h : Nonempty (Derivation body Delta (AtRaw Q F H M W parameter gamma c bound raw params)))
 (hf : Nonempty (Derivation body Delta (fields Q H M W parameter gamma c bound raw types observations rank))) :
 Nonempty (Derivation body Delta (programGraph (SortWeightedDefinitions.weighted F) rank (Fin.cons observations params))) := by
 obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
   (matrix Q F H M W parameter gamma c bound raw params) (fun i => emb (![types,observations,rank] i)) h
 rw [matrixWitness] at h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
theorem belowRawAt (parameter gamma c bound raw child : OTerm alpha) (params : Fin k → OTerm alpha)
 (h : Nonempty (Derivation body Delta (BelowRaw Q F H M W parameter gamma c bound raw params)))
 (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
 Nonempty (Derivation body Delta (AtRaw Q F H M W parameter gamma c bound child params)) := by
 obtain ⟨h⟩ := h
 obtain ⟨hl⟩ := hl
 have d := Derivation.universalElimination (emb child) h
 change Derivation body Delta (instantiate
   ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
     (rawPredicate Q F H M W parameter gamma c bound params)) (emb child)) at d
 rw [belowElimSyntax,rawPredicateInstantiate] at d
 exact ⟨Derivation.implicationElimination d hl⟩
theorem rawInduction (parameter gamma c bound raw : OTerm alpha) (params : Fin k → OTerm alpha)
 (hw : Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)))
 (step : ∀ (beta : Type) (Theta : List (Formula beta)) (p g ctx b r : OTerm beta)
   (ps : Fin k → OTerm beta),
   Nonempty (Derivation body Theta (LocalWeights Q F H M W p g ctx b ps)) →
   Nonempty (Derivation body Theta (BelowRaw Q F H M W p g ctx b r ps)) →
   Nonempty (Derivation body Theta (AtRaw Q F H M W p g ctx b r ps))) :
 Nonempty (Derivation body Delta (AtRaw Q F H M W parameter gamma c bound raw params)) := by
 let theta : Formula (alpha ⊕ Fin 1) := rawPredicate Q F H M W parameter gamma c bound params
 let A := InternalStrongInduction.below (lift theta) (.var (.inr 0))
 let Xi := A :: Delta.map weaken
 have hw' := renameInto hw (Sum.inl : alpha → alpha ⊕ Fin 1) Xi (by
   intro q hq
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
 rw [RankArgumentSyntax.weightsRename] at hw'
 have hs : Nonempty (Derivation body Xi theta) := by
   change Nonempty (Derivation body Xi
     (AtRaw Q F H M W (parameter.relabel Sum.inl) (gamma.relabel Sum.inl)
       (c.relabel Sum.inl) (bound.relabel Sum.inl) (.var (.inr 0)) (fun i => (params i).relabel Sum.inl)))
   apply step (alpha ⊕ Fin 1) Xi _ _ _ _ _ _ hw'
   have hi : Nonempty (Derivation body Xi A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [A,theta,rawPredicateLift] using hi
 obtain ⟨d⟩ := strongInduction theta hs
 have e := Derivation.universalElimination (emb raw) d
 change Derivation body Delta (instantiate (rawPredicate Q F H M W parameter gamma c bound params) (emb raw)) at e
 rw [rawPredicateInstantiate] at e
 exact ⟨e⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionBinding
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionBinding
