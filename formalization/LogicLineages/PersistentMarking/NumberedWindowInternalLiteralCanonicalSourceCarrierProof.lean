module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeCoherentArgumentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalOneHopInversionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalSourceCarrierProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn headTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalAccessibilityRules (carrier certificate)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases addressReportRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalOriginalOneHopInversionProof (exact_OneHopProgramElim exact_OneHopRawInversionAtReports)
open NumberedWindowInternalOriginalFirstHopCoreProof (D)
open NumberedWindowInternalNeutralFactsTargets (direct directData)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralCanonicalChildProof (exact_OpenLiteralScalarFromSelfLeast)
open NumberedWindowInternalLiteralSelectedChildWindowProof (exact_OpenLiteralSelectedWindow)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralLeastFixedPointProof (exact_LiteralLeastFixedPointFromEdge)
open NumberedWindowInternalLiteralDirectTargetCarrierProof (exact_OpenDirectTargetCarrier)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules exact_DomainRules)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem scalarAtReportedAddress (i : Program 1) (y ctx ty k : OTerm α)
    (address : D B Γ (addressReport y ctx ty k))
    (sat : D B Γ (unary i (suc z) (addressTerm ctx ty k))) :
    D B Γ (unary i (suc z) y) := by
  obtain ⟨rule⟩ := exactOpenTriple B α Γ 3 y ctx ty k
  obtain ⟨report⟩ := address
  have eq := Derivation.implicationElimination (Derivation.conjunctionRight rule) report
  rw [equalEqn] at eq
  have t := headTransport i (suc z) (addressTerm ctx ty k) y Fin.elim0 ⟨symm eq⟩ sat
  have hvec : Fin.cons y (Fin.elim0 : Fin 0 → OTerm α) = (![y] : Fin 1 → OTerm α) := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  unfold unary
  rw [← hvec]
  exact t

/-- Source-side scalar acceptance is derived from the original typed
raw source and the actual returned least, rather than from an extra
gate on the source of the reduction. -/
private theorem sourceCarrierOfCall (cv tv : Program 1) (C root other W : Program 3)
    (X : Program 2) (V : Program 1) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (c : Nat) (x hd y : OTerm α) :
    let L := packedLeastProgram C X W s
    let i := addressScalar cv tv W L
    let underlying := typedRaw5 root other W V
    let R := rawWithTarget i cv tv underlying L
    let data := S i cv tv R L
    let h := hop cv tv R L
    let B := sourceBody data c
    D B Γ (programGraph h (suc z) ![x,hd,y]) → D B Γ (carrier data false c x) := by
  intro L i underlying R data h B held
  let k := addressPositive cv tv R L
  let goal := carrier data false c x
  have one := exact_OneHopProgramElim k x hd y held
  have observed := forward cv tv R L x (rawCons hd z) y one
  apply reportsCases cv tv R L x (rawCons hd z) y goal observed
  intro β j Δ ctx ty before after keep facts
  rw [carrierRename]
  obtain ⟨f⟩ := facts
  let f₂ := Derivation.conjunctionRight f
  let f₃ := Derivation.conjunctionRight f₂
  let f₄ := Derivation.conjunctionRight f₃
  let src := x.relabel j
  let cert := hd.relabel j
  let dst := y.relabel j
  have h' := renameInto held j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at h'
  have openRaw := exact_OneHopRawInversionAtReports cv tv R L src cert dst ctx ty before after
    ⟨Derivation.conjunctionLeft f⟩ ⟨Derivation.conjunctionLeft f₂⟩ h'
  apply reportCases R L ctx ty before cert after _ openRaw
  intro γ l Ω q w r stay report
  rw [carrierRename]
  have pc := renameInto (⟨Derivation.conjunctionLeft f₃⟩ : D B Δ (unary cv (suc z) ctx)) l Ω stay
  have pt := renameInto (⟨Derivation.conjunctionLeft f₄⟩ : D B Δ (unary tv (suc z) ty)) l Ω stay
  have srcReport := renameInto (⟨Derivation.conjunctionLeft f⟩ :
    D B Δ (addressReport src ctx ty before)) l Ω stay
  simp only [unaryRename,sucRelabel,zRelabel] at pc pt
  rw [addressReportRename] at srcReport
  obtain ⟨row⟩ := report
  have calls := Derivation.conjunctionRight row
  let g := ctx.relabel l
  let t := ty.relabel l
  let m := before.relabel l
  obtain ⟨clean⟩ := conjunctionRecover underlying (targetGate i cv tv L) ![g,t,q,w,r]
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨decode⟩ := exact_OpenTypedRaw5 B root other W V γ Ω g t q w r
  have hs := Derivation.implicationElimination (Derivation.conjunctionLeft decode)
    (Derivation.conjunctionLeft clean)
  have inWin : D B Ω (windowAt W g t q) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hs)⟩
  have chosen : D B Ω (leastGraph C X W s g t q m) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight calls)⟩
  have scalar := exact_OpenLiteralScalarFromSelfLeast cv tv W L g t m pc pt
    (exact_OpenLiteralSelectedWindow C X W s g t q m inWin chosen)
    (exact_LiteralLeastFixedPointFromEdge C X W s paid g t q m chosen)
  have onAddress := scalarAtReportedAddress i (src.relabel l) g t m srcReport scalar
  exact (exact_DomainRules i (jRaw i) k (dCore i k permutation) false c B γ Ω (src.relabel l)).2 onAddress

/-- Every actual original direct edge in the canonical typed body
gives both carriers, with no separate endpoint address or validation
assumption. The least exchange coherence for the selected data
remains explicit. -/
theorem exact_OpenCanonicalDirectCarriers (cv tv : Program 1) (C root other W : Program 3)
    (X : Program 2) (V : Program 1) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (c : Nat) (x y : OTerm α) :
    let L := packedLeastProgram C X W s
    let i := addressScalar cv tv W L
    let underlying := typedRaw5 root other W V
    let R := rawWithTarget i cv tv underlying L
    let data := S i cv tv R L
    let h := hop cv tv R L
    let B := sourceBody data c
    D B Γ (direct data h c x y) → D B Γ (carrier data false c x ⊓ carrier data false c y) := by
  intro L i underlying R data h B edge
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let cert := certificate (directData data h) false c (x.relabel j) (y.relabel j) w
  let Δ := cert :: Γ.map weaken
  have held : D B Δ cert := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have yes : D B Δ (accepts h (x.relabel j) w (y.relabel j)) :=
    (exact_CertificateRules i (jRaw i) h (dCore i (addressPositive cv tv R L) permutation)
      false c B _ Δ (x.relabel j) (y.relabel j) w).1 held
  have ok : D B Δ (programGraph h (suc z) ![x.relabel j,w,y.relabel j]) := by
    unfold accepts at yes
    unfold programGraph
    exact yes
  have out : D B Δ ((carrier data false c x).relabel j) := by
    rw [carrierRename]
    exact sourceCarrierOfCall cv tv C root other W X V s paid c (x.relabel j) w (y.relabel j) ok
  obtain ⟨post⟩ := out
  obtain ⟨after⟩ := exact_OpenDirectTargetCarrier i cv tv underlying L c x y edge
  obtain ⟨pre⟩ := edge
  unfold direct at pre
  rw [edgeExists] at pre
  exact ⟨Derivation.conjunctionIntroduction (Derivation.existentialElimination pre post) after⟩

#print axioms exact_OpenCanonicalDirectCarriers
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalSourceCarrierProof
