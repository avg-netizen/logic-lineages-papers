module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceComputabilityLeastMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceComputabilityLeastProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalComputabilityApplicationProof InternalComputabilityApplicationSyntaxProof
open InternalComputabilityDownward InternalComputabilityDownwardProof InternalComputabilityDownwardSyntaxProof
open InternalAccessibilityRules InternalAccessibilityRulesSyntaxProof
open InverseApplicationSyntaxProof (membershipRename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original finite-type induction. Every arrow uses a genuine same-Gamma
bottom Object, the original existential application, and scalar I induction
already paid by inverse application. The source is never reselected. -/
theorem least (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hbase : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hwindow : Path.windowCalibrated n window)
    (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    let src := OuterSelection.source oldSrc oldComp base oldStep window
    let comp := OuterSelection.computability oldComp base window oldVertex oldResult
    ∀ (tau : Ty) (α : Type) (Delta : List (Formula α)) (f : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (computable comp tau (numeral context) f)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (membership false f)) := by
  dsimp only
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  let lift := OuterSelection.lift base window oldVertex
  obtain ⟨rules, certified, _, hcarrier, hforward, _⟩ :=
    OuterProof.actualConcreteUniformCertificateDownwardPackage n arity base hbase window hwindow
      oldSrc oldComp oldStep oldVertex oldResult symbols S table hS
  have compatible := actualOriginalCertifiedLiftReduction src comp lift context certified
  intro tau
  induction tau with
  | ground =>
    intro α Delta f hc
    rw [computableGround] at hc
    exact andRight hc
  | arrow sigma tau ihs iht =>
    intro α Delta f hc
    by_cases hsigma : sigma ∈ S
    · apply programCases InternalUnpair.left (Fin.cons f Fin.elim0) (membership false f)
      intro β j Theta gamma hj hg
      rw [membershipRename]
      have hg' : Nonempty (Derivation (SourcePresentation.sourceBody src context) Theta
          (graph1 InternalUnpair.left gamma (f.relabel j))) := by
        simpa only [consTermRename, emptyRename] using hg
      have hc' := renameInto hc j Theta hj
      simp only [computableRename, numeralRename] at hc'
      apply programCases ComputabilityLeast.bottomObject
        (Fin.cons (numeral (NumberedLeastCodeRepresentative.typeNumber sigma))
          (Fin.cons gamma Fin.elim0)) (membership false (f.relabel j))
      intro γ k Omega a hk hb
      rw [membershipRename]
      have hb' : Nonempty (Derivation (SourcePresentation.sourceBody src context) Omega
          (ComputabilityLeast.bottomGraph a
            (numeral (NumberedLeastCodeRepresentative.typeNumber sigma)) (gamma.relabel k))) := by
        simpa only [ComputabilityLeast.bottomGraph, consTermRename, emptyRename, numeralRename] using hb
      have hca := closedApply
        (GlobalSourceSpineBottomProof.actualConcreteBottomComputable n arity base hbase
          window hwindow oldSrc oldComp oldStep oldVertex oldResult symbols S table hS
          sigma hsigma γ [] a (gamma.relabel k)) hb'
      have hpair := GlobalSourceSpineBottomSupportProof.bottomObjectPair sigma a (gamma.relabel k) hb'
      have hga := pairLeft a (gamma.relabel k) (BottomSource.bottomTerm sigma) hpair
      have hgf := renameInto hg' k Omega hk
      rw [graph1Rename] at hgf
      have hguard := OuterTypedProof.objectGuard oldComp (OuterSelection.data base window) window
        oldVertex oldResult ((f.relabel j).relabel k) a (gamma.relabel k) hgf hga
      have hc'' := renameInto hc' k Omega hk
      simp only [computableRename, numeralRename] at hc''
      have hdomain : Nonempty (Derivation (SourcePresentation.sourceBody src context) Omega
          (domain comp context sigma tau ((f.relabel j).relabel k) a)) :=
        andIntro (andIntro (typedness comp (.arrow sigma tau) (numeral context)
          ((f.relabel j).relabel k) hc'') (typedness comp sigma (numeral context) a hca)) hguard
      have hresult := arrowElimination comp sigma tau (numeral context)
        ((f.relabel j).relabel k) a hc'' hguard hca
      apply resultCases comp sigma tau (numeral context) ((f.relabel j).relabel k) a
        (membership false ((f.relabel j).relabel k)) hresult
      intro δ l Lambda out hl haccept hcout
      rw [membershipRename]
      simp only [numeralRename] at haccept hcout
      have hd := renameInto hdomain l Lambda hl
      rw [domainRename] at hd
      exact InverseApplicationProof.actualOriginalInverseApplication src comp context rules
        compatible hcarrier hforward δ Lambda sigma tau (((f.relabel j).relabel k).relabel l)
        (a.relabel l) out hd haccept (iht δ Lambda out hcout)
    · have hnot : Ty.arrow sigma tau ∉ S := by
        intro ht
        exact hsigma (NumberedUniverseOperationsProof.arrowDomain (fun typ => typ ∈ S)
          hS sigma tau ht)
      exact GlobalSourceComputabilityLeastMembershipProof.typedOutOfWindow n arity base hbase
        window hwindow oldComp oldVertex oldResult symbols S table hS (.arrow sigma tau)
        hnot f (membership false f) (typedness comp (.arrow sigma tau) (numeral context) f hc)

theorem actualConcreteComputabilityLeast : ComputabilityLeastTargets.ActualConcreteComputabilityLeast := by
  intro n arity base hbase window hwindow oldSrc oldComp oldStep oldVertex oldResult
  dsimp only
  intro symbols S table hS tau α Delta f
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  let H := computable comp tau (numeral context) f
  obtain ⟨h⟩ := least n arity base hbase window hwindow oldSrc oldComp oldStep oldVertex oldResult
    symbols S table hS tau α (H :: Delta) f ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceComputabilityLeastProof
