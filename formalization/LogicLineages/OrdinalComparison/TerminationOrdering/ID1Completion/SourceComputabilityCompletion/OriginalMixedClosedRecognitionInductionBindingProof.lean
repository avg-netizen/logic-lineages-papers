module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalMixedClosedRecognitionInductionDefinitions OriginalMixedClosedRecognitionInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atPathIntro (source : Program 2) (leaf outLeaf : Program 4) (path : OTerm alpha)
 (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl))
  (matrix source leaf outLeaf path))) :
 Nonempty (Derivation body Delta (AtPath source leaf outLeaf path)) :=
 InternalClosedProgramsBindingProof.introduction body alpha 2 Delta _ h

theorem atPathApply (source : Program 2) (leaf outLeaf : Program 4)
 (path out state : OTerm alpha)
 (h : Nonempty (Derivation body Delta (AtPath source leaf outLeaf path)))
 (hg : Nonempty (Derivation body Delta (fields source leaf path out state))) :
 Nonempty (Derivation body Delta (result source outLeaf path out state)) := by
 obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 2 Delta
  (matrix source leaf outLeaf path) (fun k => emb (![out,state] k)) h
 rw [matrixWitness] at h
 obtain ⟨hg⟩ := hg
 exact ⟨Derivation.implicationElimination h hg⟩

theorem belowPathAt (source : Program 2) (leaf outLeaf : Program 4)
 (path child : OTerm alpha)
 (h : Nonempty (Derivation body Delta (BelowPath source leaf outLeaf path)))
 (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child path))) :
 Nonempty (Derivation body Delta (AtPath source leaf outLeaf child)) := by
 obtain ⟨h⟩ := h
 obtain ⟨hl⟩ := hl
 have d := Derivation.universalElimination (emb child) h
 change Derivation body Delta (instantiate
  ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (path.relabel Sum.inl)).imp
   (pathPredicate source leaf outLeaf)) (emb child)) at d
 rw [belowElimSyntax,pathPredicateInstantiate] at d
 exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPathApply (source : Program 2) (leaf outLeaf : Program 4)
 (path child out state : OTerm alpha)
 (h : Nonempty (Derivation body Delta (BelowPath source leaf outLeaf path)))
 (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child path)))
 (hg : Nonempty (Derivation body Delta (fields source leaf child out state))) :
 Nonempty (Derivation body Delta (result source outLeaf child out state)) :=
 atPathApply source leaf outLeaf child out state (belowPathAt source leaf outLeaf path child h hl) hg

/-- Strong induction and the two universally quantified states are discharged
inside the original arithmetic derivation, without external path induction. -/
theorem pathInduction (source : Program 2) (leaf outLeaf : Program 4) (path : OTerm alpha)
 (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath source leaf outLeaf r)) →
  Nonempty (Derivation body Theta (AtPath source leaf outLeaf r))) :
 Nonempty (Derivation body Delta (AtPath source leaf outLeaf path)) := by
 let theta : Formula (alpha ⊕ Fin 1) := pathPredicate source leaf outLeaf
 have hs : Nonempty (Derivation body
  (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
  change Nonempty (Derivation body
   (InternalStrongInduction.below (lift (pathPredicate source leaf outLeaf)) (.var (.inr 0)) :: Delta.map weaken)
   (AtPath source leaf outLeaf (.var (.inr 0))))
  rw [pathPredicateLift]
  exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨d⟩ := strongInduction theta hs
 have e := Derivation.universalElimination (emb path) d
 change Derivation body Delta (instantiate (pathPredicate source leaf outLeaf) (emb path)) at e
 rw [pathPredicateInstantiate] at e
 exact ⟨e⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionBindingProof
