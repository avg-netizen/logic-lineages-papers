module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineStrongProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineRowsProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalStrongInduction InternalClosedProgramsBindingProof
open InternalComputabilityDownwardSyntaxProof InternalComputabilityDownwardProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (OTerm)
open SourceComputabilityFormulaSupportProof
open SourceComputabilityCompletion.TypedSpine TypedSpineSyntaxProof TypedSpineStrongProof
open InverseApplicationSyntaxProof (membershipRename)

/-- Original R existential elimination and universal successor introduction.
The continuation later strips the concrete source checker, not its native
calibration. Every added variable is bound by original logical rules. -/
theorem successorsFromCertificates (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (progress : ∀ (β : Type) (Delta : List (Formula β)) (x mark depth g witness : OTerm β),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (below (atDepth comp context tau (.var (.inr 0))) depth)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (typed comp tau (numeral context) x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (marked x mark depth)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (certificate src false context x g witness)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (membership false g)))
    (α : Type) (Gamma : List (Formula α)) (x mark depth : OTerm α)
    (hb : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (below (atDepth comp context tau (.var (.inr 0))) depth)))
    (ht : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) x)))
    (hm : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (marked x mark depth))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (successors src false context x)) := by
  let g : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let E := edge src false context (x.relabel Sum.inl) g
  let Delta := E :: Gamma.map weaken
  have hi : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hb' := renameInto hb Sum.inl Delta hi
  rw [belowDepthRename] at hb'
  have ht' := renameInto ht Sum.inl Delta hi
  simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hm' := renameInto hm Sum.inl Delta hi
  rw [markedRename] at hm'
  have he : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta E) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htarget : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (membership false g)) := by
    apply edgeCases src context (x.relabel Sum.inl) g _ he
    intro β j Theta witness hj hc
    rw [membershipRename]
    have hbb := renameInto hb' j Theta hj
    rw [belowDepthRename] at hbb
    have htt := renameInto ht' j Theta hj
    simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at htt
    have hmm := renameInto hm' j Theta hj
    rw [markedRename] at hmm
    exact progress β Theta ((x.relabel Sum.inl).relabel j)
      ((mark.relabel Sum.inl).relabel j) ((depth.relabel Sum.inl).relabel j)
      (g.relabel j) witness hbb htt hmm hc
  obtain ⟨htarget⟩ := htarget
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction htarget)⟩

theorem row (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (tau : Ty)
    (carrierRule : ∀ (β : Type) (Delta : List (Formula β)) (x : OTerm β),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (typed comp tau (numeral context) x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (carrier src false context x)))
    (progress : ∀ (β : Type) (Delta : List (Formula β)) (x mark depth g witness : OTerm β),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (below (atDepth comp context tau (.var (.inr 0))) depth)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (typed comp tau (numeral context) x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (marked x mark depth)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (certificate src false context x g witness)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (membership false g)))
    (α : Type) (Gamma : List (Formula α)) (depth : OTerm α)
    (hb : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (below (atDepth comp context tau (.var (.inr 0))) depth))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (atDepth comp context tau depth)) := by
  unfold TypedSpine.atDepth
  apply actualFiniteUniversalIntroduction (SourcePresentation.sourceBody src context) α 2 Gamma
  let x : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let mark : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let H := typed comp tau (numeral context) x ⊓ marked x mark (depth.relabel Sum.inl)
  let Delta := H :: Gamma.map (fun p => p.relabel Sum.inl)
  have hh : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb' := renameInto hb Sum.inl Delta (by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [belowDepthRename] at hb'
  have hc := carrierRule (α ⊕ Fin 2) Delta x (andLeft hh)
  have hs := successorsFromCertificates src comp context tau progress (α ⊕ Fin 2) Delta
    x mark (depth.relabel Sum.inl) hb' (andLeft hh) (andRight hh)
  obtain ⟨h⟩ := actualOriginalAccessibilityIntroduction src false context (α ⊕ Fin 2) Delta x hc hs
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineRowsProof
