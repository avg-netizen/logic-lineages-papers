module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.SeedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem runMembership (C P : Program 2) (E : Program 3)
    {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (seed parameter out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta
      (graph2 (.composition (PrimaryIteration.run E) ![C,P,.projection 0,.projection 1])
        out seed parameter))) :
    Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out seed)) := by
  apply programCases C (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta count hj hc
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hc
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  apply programCases P (Fin.cons (seed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) _
  intro gamma k Xi pool hk hp
  simp only [graph2Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hc' := renameInto hc k Xi hk
  simp only [programRename,consTermRename,emptyRename] at hc'
  have hr'' := renameInto hr' k Xi hk
  rw [graph2Rename] at hr''
  let s := (seed.relabel j).relabel k
  let t := (parameter.relabel j).relabel k
  let o := (out.relabel j).relabel k
  have hi : Nonempty (Derivation body Xi
      (graph4 (PrimaryIteration.run E) o (count.relabel k) pool s t)) := by
    apply compositionRecover (PrimaryIteration.run E) ![C,P,.projection 0,.projection 1]
      o ![s,t] ![count.relabel k,pool,s,t] hr''
    intro i
    exact Fin.cases hc' (Fin.cases hp (Fin.cases (projectionValue 0 ![s,t])
      (Fin.cases (projectionValue 1 ![s,t]) (fun x => Fin.elim0 x)))) i
  exact PrimaryIteration.SeedProof.internalSeedMembership E body gamma Xi
    (count.relabel k) pool s t o hi

theorem internalSeedMembership : Targets.InternalSeedMembership := by
  intro T C P E body alpha Delta seed parameter out hT hL
  have hr := successorBranchElim T (InternalAcceptance.constantZero 2)
    (.composition (PrimaryIteration.run E) ![C,P,.projection 0,.projection 1])
    out z ![seed,parameter] hT hL
  exact runMembership C P E seed parameter out hr

theorem internalClassReflexivity : Targets.InternalClassReflexivity := by
  intro T C P E body alpha Delta seed parameter hT
  let L := primary T C P E
  apply programCases L (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta list hj hL
  simp only [graph3Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hL
  have ht := renameInto hT j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ht
  have hm := internalSeedMembership T C P E body beta Theta
    (seed.relabel j) (parameter.relabel j) list ht hL
  have hd := TransparentCandidate.InternalProof.acceptedValue T
    (seed.relabel j) (parameter.relabel j) ht
  exact MembershipInternalProof.actualInternalClassIntroduction T L (TransparentCandidate.candidate T)
    body beta Theta (seed.relabel j) (seed.relabel j) (parameter.relabel j) list
    (seed.relabel j) ht hL hd hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
