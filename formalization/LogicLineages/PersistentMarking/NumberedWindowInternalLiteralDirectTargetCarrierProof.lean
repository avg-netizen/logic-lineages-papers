module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierOpenProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectTargetCarrierProof
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
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralHopCarrierOpenProof (exact_OpenRawWithTargetReport)
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

/-- The actual checked one-hop program already exposes both validated
address records. Follow its same one-cell tape down to the original
least target, then recover the installed scalar carrier at that target. -/
theorem targetCarrierOfCall (i cv tv : Program 1) (raw : Program 5) (L : Program 3)
    (c : Nat) (x hd y : OTerm α) :
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let h := hop cv tv R L
    let B := sourceBody data c
    D B Γ (programGraph h (suc z) ![x,hd,y]) → D B Γ (carrier data false c y) := by
  intro R data h B held
  let k := addressPositive cv tv R L
  let goal := carrier data false c y
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
  have dstReport := renameInto (⟨Derivation.conjunctionLeft f₂⟩ :
    D B Δ (addressReport dst ctx ty after)) l Ω stay
  simp only [unaryRename,sucRelabel,zRelabel] at pc pt
  rw [addressReportRename] at dstReport
  obtain ⟨row⟩ := report
  have calls := Derivation.conjunctionRight row
  have min := Derivation.conjunctionRight (Derivation.conjunctionRight calls)
  obtain ⟨exactReport⟩ := exact_OpenRawWithTargetReport i cv tv raw L (ctx.relabel l) (ty.relabel l)
    q w r (after.relabel l) pc pt ⟨min⟩ ⟨Derivation.conjunctionLeft calls⟩
  have onAddress := scalarAtReportedAddress i (dst.relabel l) (ctx.relabel l) (ty.relabel l) (after.relabel l)
    dstReport ⟨Derivation.conjunctionRight exactReport⟩
  exact (exact_DomainRules i (jRaw i) k (dCore i k permutation) false c B γ Ω (dst.relabel l)).2 onAddress

/-- The genuine direct edge of the selected ordinary original body
always yields its actual target scalar carrier. No supplied address,
typing or class representative premises are needed. -/
theorem exact_OpenDirectTargetCarrier (i cv tv : Program 1) (raw : Program 5) (L : Program 3)
    (c : Nat) (x y : OTerm α) :
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let h := hop cv tv R L
    let B := sourceBody data c
    D B Γ (direct data h c x y) → D B Γ (carrier data false c y) := by
  intro R data h B edge
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
  have out : D B Δ ((carrier data false c y).relabel j) := by
    rw [carrierRename]
    exact targetCarrierOfCall i cv tv raw L c (x.relabel j) w (y.relabel j) ok
  obtain ⟨post⟩ := out
  obtain ⟨pre⟩ := edge
  unfold direct at pre
  rw [edgeExists] at pre
  exact ⟨Derivation.existentialElimination pre post⟩

#print axioms exact_OpenDirectTargetCarrier
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectTargetCarrierProof
