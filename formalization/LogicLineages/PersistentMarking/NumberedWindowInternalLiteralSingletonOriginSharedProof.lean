module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchFactsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginSharedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalQuotientComparisonProof (orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralMemberReverse)
open NumberedWindowInternalLiteralCountMembershipChecks (exact_OpenLiteralCountMembershipForward)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectProjectedCert (exactProjectedCert)
open NumberedWindowInternalDirectInstalledOriginSyntaxProof (addReportHyp)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appendRename)
open NumberedWindowInternalScratchAppendOpenChecks (exact_OpenScratchAppendMembership)
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalLiteralSingletonScratchFactsProof (exact_LiteralSingletonMember)
open NumberedWindowInternalLiteralSingletonCapacityProof (exact_LiteralSingletonKeptAbsent)
open NumberedWindowInternalLiteralSingletonOriginTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveSource (r : Program 3) (dom head w key : OTerm α)
    (same : Nonempty (Derivation B Γ (eqn dom head)))
    (ran : Nonempty (Derivation B Γ (programGraph r (suc z) ![dom,w,key]))) :
    Nonempty (Derivation B Γ (programGraph r (suc z) ![head,w,key])) := by
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula r) (suc z)
    ![dom,w,key] ![head,w,key] _ ran
  intro j
  rw [onEquality]
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => ?_) l) j
  · exact same
  · exact ⟨refl w⟩
  · obtain rfl := Fin.eq_zero m
    exact ⟨refl key⟩

private theorem edgeOfRemoved (i : Program 1) (r : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (s q k d sk dom w key : OTerm α)
    (cell : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (consGraph s q z)))
    (ap : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (appendGraph sk k d)))
    (p : Nonempty (Derivation (sourceBody (literalData i r) c) Γ
      (programGraph permutation (suc z) ![s,sk])))
    (member : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (memberGraph d dom)))
    (positive : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (programGraph r (suc z) ![dom,w,key]))) :
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ (edge (literalData i r) false c q key)) := by
  let S := literalData i r
  let B := sourceBody S c
  obtain ⟨m⟩ := member
  have inJoin := exact_OpenScratchAppendMembership B α Γ k d sk dom ap ⟨orRight m⟩
  have inSource := exact_LiteralMemberReverse B α Γ s sk dom p inJoin
  obtain ⟨same⟩ := exact_LiteralSingletonMember B α Γ s q dom cell inSource
  have atQ := moveSource r dom q w key ⟨symm same⟩ positive
  exact edgeIntroduction ((exact_CertificateRules i (jRaw i) r (dCore i r permutation)
    false c B α Γ q key w).2 atQ)

theorem exact_LiteralSingletonMemberEdgeFromShared : ExactLiteralSingletonMemberEdgeFromShared := by
  intro i r c α Γ src dst kept removed inserted s t k d a p sk tp q dkey key
  dsimp only
  intro shared cell picked target
  let S := literalData i r
  let B := sourceBody S c
  let G := edge S false c q key
  have inJoin := exact_OpenLiteralCountMembershipForward B α Γ t tp key shared.targetObserved target
  obtain ⟨split⟩ := exact_OpenScratchAppendOrigin B α Γ k p tp key shared.targetAppend inJoin
  obtain ⟨absent⟩ := exact_LiteralSingletonKeptAbsent B α Γ s q k d sk dkey key
    cell picked shared.sourceAppend shared.sourceObserved
  let L := memberGraph k key
  let R := memberGraph p key
  have left : Derivation B Γ (L.imp G) := by
    have haveL : Derivation B (L :: Γ) L := Derivation.hypothesis List.mem_cons_self
    exact Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp absent L) haveL))
  have right : Nonempty (Derivation B (R :: Γ) G) := by
    have shared' := addReportHyp permutation r src dst kept removed inserted s t k d a p sk tp shared R
    apply exactProjectedCert permutation permutation r B α (R :: Γ) src dst kept removed inserted s t k d a p sk tp key G
      shared' ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β ρ Δ row dom proof keep _ fields
    have old : ∀ f ∈ Γ, f.relabel ρ ∈ Δ := fun f h => keep f (List.mem_cons_of_mem R h)
    have sourceCons : Nonempty (Derivation B Δ (consGraph (s.relabel ρ) (q.relabel ρ) z)) := by
      simpa only [consGraphRename,zRelabel] using renameInto cell ρ Δ old
    have appended : Nonempty (Derivation B Δ (appendGraph (sk.relabel ρ) (k.relabel ρ) (d.relabel ρ))) := by
      simpa only [appendRename] using renameInto shared.sourceAppend ρ Δ old
    have pure : Nonempty (Derivation B Δ (programGraph permutation (suc z) ![s.relabel ρ,sk.relabel ρ])) := by
      simpa only [sucRelabel,zRelabel] using
        renamePair permutation (suc z) s sk shared.sourceObserved ρ old
    obtain ⟨e⟩ := fields.original
    have tail := Derivation.conjunctionRight e
    change Nonempty (Derivation B Δ ((edge S false c q key).relabel ρ))
    rw [edgeRename]
    exact edgeOfRemoved i r c β Δ (s.relabel ρ) (q.relabel ρ) (k.relabel ρ)
      (d.relabel ρ) (sk.relabel ρ) dom proof (key.relabel ρ) sourceCons appended pure
      ⟨Derivation.conjunctionLeft tail⟩ ⟨Derivation.conjunctionRight tail⟩
  obtain ⟨right⟩ := right
  exact ⟨disjunctionElimination split left (Derivation.implicationIntroduction right)⟩

#print axioms exact_LiteralSingletonMemberEdgeFromShared
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginSharedProof
