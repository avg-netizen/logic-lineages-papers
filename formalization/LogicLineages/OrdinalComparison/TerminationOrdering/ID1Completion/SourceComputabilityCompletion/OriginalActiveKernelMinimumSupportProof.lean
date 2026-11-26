module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalControlGraphSupportProof InternalPositiveUnfoldingSupportProof
open InternalBetaTotalityProof (addHyp disjunctionElimination)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalSourceInversionSupportProof (onEquality)
open OriginalActiveClassKernel (Domain Accepted)
open OriginalActiveKernelMinimum
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The existing genuine least-hit theorem is applied to the actual kernel
minimum output. The key supplier and runtime parameter remain unchanged. -/
theorem minimumFacts (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter earlier : OTerm alpha)
    (hd : Nonempty (Derivation positive Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation positive Delta
      (OriginalTransparentMinimum.atMost out seed ⊓
        (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
            seed out parameter ⊓
          ((InternalLessThan.strictLess earlier out).imp
            (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
              seed earlier parameter).not)))) := by
  obtain ⟨hd⟩ := hd
  obtain ⟨hr⟩ := hr
  obtain ⟨hm⟩ :=
    OriginalActiveObservedMinimumInternalProof.actualOriginalActiveObservedMinimumInternalMinimum
      p H G W (OriginalActiveClassKernel.classTest p H G W P)
      positive alpha Delta out seed parameter earlier
  exact ⟨Derivation.implicationElimination hm
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hd)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionRight hd) hr))⟩

theorem minimumHit (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter : OTerm alpha)
    (hd : Nonempty (Derivation positive Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation positive Delta
      (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
        seed out parameter)) :=
  andLeft (andRight (minimumFacts p H G W P seed out parameter seed hd hr))

/-- The actual arithmetic trichotomy, with both strict alternatives
eliminated internally, gives equality of two least accepted candidates. -/
theorem equalOfNotLess (x y : OTerm alpha)
    (hxy : Nonempty (Derivation positive Delta (InternalLessThan.strictLess x y).not))
    (hyx : Nonempty (Derivation positive Delta (InternalLessThan.strictLess y x).not)) :
    Nonempty (Derivation positive Delta (equal x y)) := by
  obtain ⟨hxy⟩ := hxy
  obtain ⟨hyx⟩ := hyx
  obtain ⟨comparison⟩ := actualOriginalComparison positive alpha x y
  have hc := compareView (weakenClosed comparison Delta)
  have hl : Derivation positive Delta ((ltF x y).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp hxy _)
        (Derivation.hypothesis List.mem_cons_self)))
  have he : Derivation positive Delta ((eqn x y).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have hr : Derivation positive Delta ((ltF y x).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp hyx _)
        (Derivation.hypothesis List.mem_cons_self)))
  have hrest : Derivation positive Delta
      (((eqn x y) ⊔ ltF y x).imp (eqn x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self) (addHyp he _) (addHyp hr _))
  have result : Nonempty (Derivation positive Delta (eqn x y)) :=
    ⟨disjunctionElimination hc hl hrest⟩
  simpa only [equal,onEquality,eqn] using result

theorem domainGraphsRename (T A : Program 2) (seed parameter : OTerm alpha)
    {beta : Type} (j : alpha → beta) :
    ((graph2 T InternalOriginalStepGuard.one seed parameter ⊓
      graph2 A InternalOriginalStepGuard.one seed parameter).relabel j) =
      (graph2 T InternalOriginalStepGuard.one (seed.relabel j) (parameter.relabel j) ⊓
        graph2 A InternalOriginalStepGuard.one (seed.relabel j) (parameter.relabel j)) := by
  change ((graph2 T InternalOriginalStepGuard.one seed parameter).relabel j ⊓
    (graph2 A InternalOriginalStepGuard.one seed parameter).relabel j) = _
  rw [graph2Rename,graph2Rename,InternalOriginalStepGuardSupportProof.oneRename]

theorem domainRename (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (seed parameter : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (Domain p H G W seed parameter).relabel j =
      Domain p H G W (seed.relabel j) (parameter.relabel j) :=
  domainGraphsRename (OriginalTypedDecoder.target H G)
    (OriginalActiveObservedClass.activation p H G W) seed parameter j

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
