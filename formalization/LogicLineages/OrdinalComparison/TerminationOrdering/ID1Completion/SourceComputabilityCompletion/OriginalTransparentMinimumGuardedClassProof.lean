module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGuardedClassProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum
open InternalApplicationCertificateConstructors (graph2)
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalPositiveUnfoldingSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- A literal branch always returns one of its actual branch graphs. -/
theorem branchAlternative {k : Nat} (control a b : Program k) (out : OTerm α)
    (xs : Fin k → OTerm α)
    (hw : Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch control a b) out xs))) :
    Nonempty (Derivation body Delta (programGraph a out xs ⊔ programGraph b out xs)) := by
  apply programCases control xs _
  intro β j Gamma c hj hc
  simp only [programRename]
  have hw' := renameInto hw j Gamma hj
  simp only [programRename] at hw'
  apply formulaCases (eqn c z)
  · have hz := outputTransport control c z (fun i => (xs i).relabel j)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hc _)
    obtain ⟨ha⟩ := zeroBranchElim control a b (out.relabel j)
      (fun i => (xs i).relabel j) hz (withHyp hw' _)
    exact ⟨orLeft ha⟩
  · obtain ⟨hb⟩ := nonzeroBranchElim control a b (out.relabel j) c
      (fun i => (xs i).relabel j) (withHyp hc _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hw' _)
    exact ⟨orRight hb⟩

/-- Rank fallback can return the seed, so only class membership is retained.
The premise is the independently established internal minimum law. -/
theorem guardedClassOfMinimum (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3)
    (hminimum : MinimumLaw (OriginalTypedDecoder.target H G) P) :
    GuardedClassLaw p H G W P := by
  intro body α Delta out seed parameter
  let T := OriginalTypedDecoder.target H G
  let R := minimum T P
  let Q := reflexiveClassTest T P
  let q := transparentInputs H G W P p
  let A := graph2 T InternalOriginalStepGuard.one seed parameter ⊓
    graph2 q.base.oldRepresentative out seed parameter
  let xs : Fin 2 → OTerm α := Fin.cons seed (Fin.cons parameter Fin.elim0)
  let desired := graph3 Q InternalOriginalStepGuard.one seed out parameter
  have hh : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  have ht := Derivation.conjunctionLeft hh
  have hw : Nonempty (Derivation body (A :: Delta)
      (graph2 (OriginalRankGuardedRepresentative.representative q.base.oldSource R p.window)
        out seed parameter)) := ⟨Derivation.conjunctionRight hh⟩
  have hkeep : ∀ {Gamma : List (Formula α)},
      Nonempty (Derivation body Gamma (graph2 T InternalOriginalStepGuard.one seed parameter)) →
      Nonempty (Derivation body Gamma (graph2 R out seed parameter)) →
      Nonempty (Derivation body Gamma desired) := by
    intro Gamma ⟨ht⟩ ⟨hr⟩
    obtain ⟨hm⟩ := hminimum body α Gamma out seed parameter seed
    exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight
      (Derivation.implicationElimination hm (Derivation.conjunctionIntroduction ht hr)))⟩
  have hfallback : ∀ {Gamma : List (Formula α)},
      Nonempty (Derivation body Gamma (graph2 T InternalOriginalStepGuard.one seed parameter)) →
      Nonempty (Derivation body Gamma (programGraph (.projection (0 : Fin 2)) out xs)) →
      Nonempty (Derivation body Gamma desired) := by
    intro Gamma ⟨ht⟩ hp
    obtain ⟨he⟩ := valueUnique (.projection (0 : Fin 2)) out seed xs hp (projectionValue 0 xs)
    obtain ⟨href⟩ := OriginalTransparentMinimumInternalReflexiveProof.actualOriginalTransparentMinimumInternalReflexive
      T P body α Gamma seed parameter
    have href := Derivation.implicationElimination href ht
    apply InternalGraphCompositionEqualityProof.graphInputTransport body α 3 Gamma _
      InternalOriginalStepGuard.one (Fin.cons seed (Fin.cons seed (Fin.cons parameter Fin.elim0)))
      (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0))) _ ⟨href⟩
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
    · rw [onEquality]
      exact ⟨refl seed⟩
    · rw [onEquality]
      exact ⟨symm he⟩
    · rw [onEquality]
      exact ⟨refl parameter⟩
  obtain ⟨houter⟩ := branchAlternative (OriginalRankGuardedRepresentative.active q.base.oldSource p.window)
    R (InternalAcceptance.branch (OriginalRankGuardedRepresentative.sameRank R) (.projection 0) R)
    out xs hw
  have ha : Nonempty (Derivation body (graph2 R out seed parameter :: A :: Delta) desired) :=
    hkeep (withHyp ⟨ht⟩ _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body
      (programGraph (InternalAcceptance.branch (OriginalRankGuardedRepresentative.sameRank R)
        (.projection 0) R) out xs :: A :: Delta) desired) := by
    obtain ⟨hi⟩ := branchAlternative (OriginalRankGuardedRepresentative.sameRank R) (.projection 0) R
      out xs ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hp⟩ := hfallback (withHyp (withHyp ⟨ht⟩ _) _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := hkeep (withHyp (withHyp ⟨ht⟩ _) _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨disjunctionElimination hi (Derivation.implicationIntroduction hp)
      (Derivation.implicationIntroduction hr)⟩
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination houter
    (Derivation.implicationIntroduction ha) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGuardedClassProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGuardedClassProof
