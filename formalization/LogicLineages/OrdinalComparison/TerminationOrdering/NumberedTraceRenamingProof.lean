module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceRenamingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceRenamingProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimaryWeakening
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedPrimaryWeakeningProof

theorem primaryRename {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma Delta : List Ty}
    (rho : Renaming Gamma Delta) {q r : Packed Symbol arity Gamma}
    (h : NumberedWindowEquivalence.WindowPrimary Symbol arity symbols S Gamma q r) :
    NumberedWindowEquivalence.WindowPrimary Symbol arity symbols S Delta (renamePacked rho q) (renamePacked rho r) := by
  rw [packedRenameAsSubstitution,packedRenameAsSubstitution]
  exact NumberedPrimarySubstitutionProof.actualPrimarySubstitution Symbol arity symbols S Gamma Delta (fun v => .var (rho v)) q r h

theorem actualPackedTraceRenaming : NumberedTraceRenamingTargets.ActualPackedTraceRenaming := by
  intro Symbol arity symbols S above Gamma Delta rho count q r h
  induction h with
  | equivalent he => exact .equivalent (primaryRename rho he)
  | raw q r hs => exact .raw _ _ (NumberedStepRenamingProof.actualStepRenaming Symbol arity symbols S above Gamma Delta rho _ q r hs)
  | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2

theorem actualTypedTraceRenaming : NumberedTraceRenamingTargets.ActualTypedTraceRenaming := by
  intro Symbol arity symbols S above Gamma Delta rho tau count q r h
  have hp := (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Gamma tau count q r).mpr h
  have ht := actualPackedTraceRenaming Symbol arity symbols S above Gamma Delta rho count ⟨tau,q⟩ ⟨tau,r⟩ hp
  exact (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Delta tau count
    (NumberedRewriteSyntax.rename q rho) (NumberedRewriteSyntax.rename r rho)).mp ht

theorem actualTupleTraceRenaming : NumberedTraceRenamingTargets.ActualTupleTraceRenaming := by
  intro Symbol arity symbols S above Gamma Delta rho types count base target h
  induction h with
  | equivalent he =>
    apply WindowTupleTrace.equivalent
    rw [actualArgumentRenameAsSubstitution,actualArgumentRenameAsSubstitution]
    exact NumberedPrimarySubstitutionProof.actualArgumentPrimarySubstitution Symbol arity symbols S Gamma Delta _
      (fun v => .var (rho v)) _ _ he
  | raw hs => exact .raw (NumberedStepRenamingProof.actualArgumentStepRenaming Symbol arity symbols S above Gamma Delta rho _ _ _ hs)
  | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2

theorem actualCountedQuotientRenaming : NumberedTraceRenamingTargets.ActualCountedQuotientRenaming := by
  intro n arity symbols S hc above Gamma Delta rho q r hq hr count hp
  have ht := NumberedQuotientPathsProof.countedBackward n arity symbols S hc above Gamma count q r hq hr hp
  have hren := actualPackedTraceRenaming (Fin n) arity symbols S above Gamma Delta rho count q r ht
  have hgood : InUniverse symbols S (renamePacked rho q).2 :=
    NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ S) (HeadInWindow arity symbols S) Gamma Delta q.1 q.2 rho hq
  exact NumberedQuotientPathsProof.countedForward n arity symbols S hc above Delta count (renamePacked rho q) (renamePacked rho r) hgood hren

theorem actualPositiveQuotientRenaming : NumberedTraceRenamingTargets.ActualPositiveQuotientRenaming := by
  intro n arity symbols S hc above Gamma Delta rho q r hq hr hp
  obtain ⟨count,hpos,hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mp hp
  exact (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Delta _ _).mpr
    ⟨count,hpos,actualCountedQuotientRenaming n arity symbols S hc above Gamma Delta rho q r hq hr count hcount⟩

theorem actualRepresentativeRenaming : NumberedTraceRenamingTargets.ActualRepresentativeRenaming := by
  intro n arity symbols S hc Gamma Delta rho q r hq hr he
  have hp := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q r hq hr).mp he
  have hqr : InUniverse symbols S (renamePacked rho q).2 :=
    NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ S) (HeadInWindow arity symbols S) Gamma Delta q.1 q.2 rho hq
  have hrr : InUniverse symbols S (renamePacked rho r).2 :=
    NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ S) (HeadInWindow arity symbols S) Gamma Delta r.1 r.2 rho hr
  exact (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Delta
    (renamePacked rho q) (renamePacked rho r) hqr hrr).mpr (primaryRename rho hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceRenamingProof
