module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl))
      (transportMatrix H M W erasing raw))) :
    Nonempty (Derivation body Delta (AtRaw H M W erasing raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 7 Delta _ h

theorem atRawApply (H : Program 1) (M W : Program 2) (erasing arguments : Bool)
    (raw d cutoff gamma extended typ transformed c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H M W erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hg : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) transformed d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W arguments typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W arguments typ transformed (targetContext erasing gamma extended) c)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 7 Delta
    (transportMatrix H M W erasing raw)
    (fun i => emb (![d,cutoff,gamma,extended,typ,transformed,c] i)) h
  rw [transportMatrixWitness] at h
  obtain ⟨hi⟩ := hi
  obtain ⟨hg⟩ := hg
  obtain ⟨ha⟩ := ha
  cases arguments
  · exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft h)
      (Derivation.conjunctionIntroduction hi (Derivation.conjunctionIntroduction hg ha))⟩
  · exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight h)
      (Derivation.conjunctionIntroduction hi (Derivation.conjunctionIntroduction hg ha))⟩

theorem belowRawAt (H : Program 1) (M W : Program 2) (erasing : Bool) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw H M W erasing child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate H M W erasing)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (H : Program 1) (M W : Program 2) (erasing arguments : Bool)
    (raw child d cutoff gamma extended typ transformed c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hg : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) transformed d cutoff child)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W arguments typ child (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W arguments typ transformed (targetContext erasing gamma extended) c)) :=
  atRawApply H M W erasing arguments child d cutoff gamma extended typ transformed c
    (belowRawAt H M W erasing raw child h hl) hi hg ha

/-- Strong induction is in the ORIGINAL arithmetic raw code. Universally
bound contexts, cutoffs and transformed outputs are re-instantiated separately
for each child; no bound on transformed output or successful child premise
escapes this internal induction. -/
theorem rawInduction (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw H M W erasing r)) →
      Nonempty (Derivation body Theta (AtRaw H M W erasing r))) :
    Nonempty (Derivation body Delta (AtRaw H M W erasing raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate H M W erasing
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate H M W erasing)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw H M W erasing (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate H M W erasing) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBindingProof
