module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveEndpointGuardProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopTailProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedFirstHopCoreProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalAccessibilityRules (edge certificate)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalParameterizedAddressPositive (exact_OriginalAddressAt)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport witnessData)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases addressReportRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt headData)
open NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalNeutralFactsTargets (direct firstHop)
open NumberedWindowInternalOriginalFirstHopCoreProof
open NumberedWindowInternalOriginalFirstHopTailProof
open NumberedWindowInternalLiteralPositiveEndpointGuardProof

abbrev R (cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  addressPositive cv tv raw least

abbrev hop (cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  oneHopProgram (R cv tv raw least)

abbrev S (i cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  literalData i (positiveEndpointGuard i (R cv tv raw least))

private theorem mkAddress {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (x cert y ctx ty src dst : OTerm α)
    (a : D B Γ (addressReport x ctx ty src)) (b : D B Γ (addressReport y ctx ty dst))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (fold : D B Γ (positiveAt raw least ctx ty src cert dst)) :
    D B Γ (programGraph (R cv tv raw least) (suc z) ![x,cert,y]) := by
  change D B Γ (programGraph (addressPositive cv tv raw least) (suc z) ![x,cert,y])
  rw [← exact_OriginalAddressAt]
  exact exact_OriginalAddressAtIntro cv tv (positive raw least) x cert y ctx ty src dst a b gc gt fold

private theorem literalDirect {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (i cv tv : Program 1) (raw : Program 5) (least : Program 3) (c : Nat)
    (x hd y ctx ty src dst : OTerm α)
    (a : D B Γ (addressReport x ctx ty src)) (b : D B Γ (addressReport y ctx ty dst))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (known : D B Γ (selectedGraph raw least (suc dst) ctx ty (suc src) hd)) :
    D B Γ (direct (S i cv tv raw least) (hop cv tv raw least) c x y) := by
  let r := R cv tv raw least
  let h := hop cv tv raw least
  have one := exact_OriginalPositiveOneCell raw least ctx ty src hd dst known
  have full := mkAddress cv tv raw least x (rawCons hd z) y ctx ty src dst a b gc gt one
  have call := exact_OneHopProgramIntro r x hd y full
  have cert := (exact_CertificateRules i (jRaw i) h (dCore i (positiveEndpointGuard i r) permutation) false c B α Γ x y hd).2 call
  exact edgeIntroduction cert

theorem exact_OpenGuardedFirstHopAtHead {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (i cv tv : Program 1) (raw : Program 5) (least : Program 3) (c : Nat)
    (x y ctx ty src dst hd tl next : OTerm α)
    (a : D B Γ (addressReport x ctx ty src)) (b : D B Γ (addressReport y ctx ty dst))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (one : D B Γ (selectedGraph raw least (suc next) ctx ty (suc src) hd))
    (tail : D B Γ (finishAt raw least ctx ty next tl dst))
    (midScalar : D B Γ (unary i (suc z) (literalAddress ctx ty next)))
    (lastScalar : D B Γ (unary i (suc z) y)) :
    D B Γ (firstHop (S i cv tv raw least) (hop cv tv raw least) c x y) := by
  let r := R cv tv raw least
  let s := S i cv tv raw least
  let h := hop cv tv raw least
  let empty := eqn tl z
  have add {F : Formula α} (C : Formula α) (p : D B Γ F) : D B (C::Γ) F :=
    p.map (Derivation.weakening (fun _ m => List.mem_cons_of_mem _ m))
  have atEnd : D B (empty::Γ) (firstHop s h c x y) := by
    have same := exact_PositiveHeadNilEndpoint raw least ctx ty next tl dst (add empty tail)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have exactY : D B (empty::Γ) (selectedGraph raw least (suc dst) ctx ty (suc src) hd) :=
      outputTransport (advance raw least) (suc next) (suc dst) ![ctx,ty,suc src,hd] same (add empty one)
    exact provideFirstHop s h c x y y
      (literalDirect i cv tv raw least c x hd y ctx ty src dst (add empty a) (add empty b)
        (add empty gc) (add empty gt) exactY)
      (restLeft ⟨refl y⟩)
  have after : D B (empty.not::Γ) (firstHop s h c x y) := by
    let mid := literalAddress ctx ty next
    have midReport := exact_OriginalLiteralAddressReport (B := B) (Γ := empty.not::Γ) ctx ty next
    have single := literalDirect i cv tv raw least c x hd mid ctx ty src next (add empty.not a)
      midReport (add empty.not gc) (add empty.not gt) (add empty.not one)
    have folding := exact_PositiveHeadContinues raw least ctx ty next tl dst (add empty.not tail)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have graph := mkAddress cv tv raw least mid tl y ctx ty next dst midReport (add empty.not b)
      (add empty.not gc) (add empty.not gt) folding
    let full := positiveEndpointGuard i r
    have guarded := exact_OpenPositiveEndpointGuardIntro i r mid tl y graph
      (add empty.not midScalar) (add empty.not lastScalar)
    have cert := (exact_CertificateRules i (jRaw i) full (dCore i full permutation) false c B α
      (empty.not::Γ) mid y tl).2 guarded
    exact provideFirstHop s h c x mid y single (restRight (edgeIntroduction cert))
  obtain ⟨atEnd⟩ := atEnd
  obtain ⟨after⟩ := after
  exact ⟨disjunctionElimination (excludedMiddle empty) (Derivation.implicationIntroduction atEnd)
    (Derivation.implicationIntroduction after)⟩

#print axioms exact_OpenGuardedFirstHopAtHead
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedFirstHopCoreProof
