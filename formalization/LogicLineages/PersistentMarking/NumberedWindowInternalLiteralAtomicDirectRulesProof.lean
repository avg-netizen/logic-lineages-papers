module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicDirectRulesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof (exact_OpenPhysicalUnderlyingReports)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicRawShapeProof
  (freeTerm bottomTerm exact_OpenLiteralGuardedFreeRawTarget exact_OpenLiteralGuardedBottomRawReject)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (atomicTest guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAtomicLeastShapeProof
  (freeAtom bottomAtom queryAtInput queryAtOutput exact_OpenLiteralAtomicGuardedLeastSingleton)
open NumberedWindowInternalLiteralAtomicAddressReportProof
  (renameAddress renameBottom renameFree alignSource rebuildAddress replaceRawSource)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rawComesFromAtom (L : Program 3) (c t q before atom : OTerm α)
    (shape : D B Γ (eqn before atom)) (recognized : D B Γ (unary atomicTest (suc z) atom))
    (held : D B Γ (programGraph (guardedLeast L) (suc before) ![c,t,q])) : D B Γ (eqn q atom) := by
  obtain ⟨same⟩ := shape
  have checked : D B Γ (unary atomicTest (suc z) before) :=
    headTransport atomicTest (suc z) atom before ![] ⟨symm same⟩ recognized
  obtain ⟨atBefore⟩ := exact_OpenLiteralAtomicGuardedLeastSingleton L c t q before held
    (queryAtOutput q before checked)
  exact ⟨trans atBefore same⟩

private theorem targetStaysAtom (L : Program 3) (c t r after atom : OTerm α)
    (shape : D B Γ (eqn r atom)) (recognized : D B Γ (unary atomicTest (suc z) atom))
    (held : D B Γ (programGraph (guardedLeast L) (suc after) ![c,t,r])) : D B Γ (eqn after atom) := by
  obtain ⟨same⟩ := shape
  have checked : D B Γ (unary atomicTest (suc z) r) :=
    headTransport atomicTest (suc z) atom r ![] ⟨symm same⟩ recognized
  obtain ⟨equal⟩ := exact_OpenLiteralAtomicGuardedLeastSingleton L c t r after held
    (queryAtInput r after checked)
  exact ⟨trans (symm equal) same⟩

/-- Rule for a literal bottom address in the actual installed
atom-guarded direct graph. The least report, not a numerical type
claim, forces the input of the raw callback to be that bottom. -/
theorem exact_OpenLiteralAtomicBottomNoDirect (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y ctx t : OTerm α) :
    let L' := guardedLeast L
    let R := rawWithTarget i cv tv (guardedRaw raw) L'
    let data := S i cv tv R L'
    let B := sourceBody data c
    D B Γ (eqn x (addressTerm ctx t (bottomTerm t))) →
    D B Γ (direct data (hop cv tv R L') c x y) → D B Γ ⊥ := by
  intro L' R data B shape edge
  apply exact_OpenPhysicalUnderlyingReports i cv tv (guardedRaw raw) L' c x y ⊥ edge
  intro β j Δ sc st before after cert q w r keep source _ _ _ _ calls
  have part := renameInto shape j Δ keep
  simp only [eqnRelabel,renameAddress,renameBottom] at part
  have aligned := alignSource (x.relabel j) (ctx.relabel j) (t.relabel j) (bottomTerm (t.relabel j))
    sc st before part source
  obtain ⟨row⟩ := calls
  let reports := Derivation.conjunctionRight row
  have origin := rawComesFromAtom L sc st q before (bottomTerm (t.relabel j))
    aligned.2.2 (bottomAtom (t.relabel j))
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight reports)⟩
  have actual := replaceRawSource (guardedRaw raw) sc st q (bottomTerm (t.relabel j)) w r
    origin ⟨Derivation.conjunctionLeft reports⟩
  exact exact_OpenLiteralGuardedBottomRawReject raw sc st (t.relabel j) w r actual

/-- Rule for a literal free address in the same actual direct graph.
The raw target is its exact same-type bottom, and the second literal
least test forces that target to stay the bottom address, including
the original packed context and result type. -/
theorem exact_OpenLiteralAtomicFreeDirectBottom (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y ctx t n : OTerm α) :
    let L' := guardedLeast L
    let R := rawWithTarget i cv tv (guardedRaw raw) L'
    let data := S i cv tv R L'
    let B := sourceBody data c
    D B Γ (eqn x (addressTerm ctx t (freeTerm t n))) →
    D B Γ (direct data (hop cv tv R L') c x y) →
    D B Γ (eqn y (addressTerm ctx t (bottomTerm t))) := by
  intro L' R data B shape edge
  apply exact_OpenPhysicalUnderlyingReports i cv tv (guardedRaw raw) L' c x y
    (eqn y (addressTerm ctx t (bottomTerm t))) edge
  intro β j Δ sc st before after cert q w r keep source target _ _ _ calls
  rw [eqnRelabel,renameAddress,renameBottom]
  let ty := t.relabel j
  let name := n.relabel j
  have part := renameInto shape j Δ keep
  simp only [eqnRelabel,renameAddress,renameFree] at part
  have aligned := alignSource (x.relabel j) (ctx.relabel j) ty (freeTerm ty name)
    sc st before part source
  obtain ⟨row⟩ := calls
  let reports := Derivation.conjunctionRight row
  let queries := Derivation.conjunctionRight reports
  have origin := rawComesFromAtom L sc st q before (freeTerm ty name) aligned.2.2
    (freeAtom ty name) ⟨Derivation.conjunctionLeft queries⟩
  have actual := replaceRawSource (guardedRaw raw) sc st q (freeTerm ty name) w r
    origin ⟨Derivation.conjunctionLeft reports⟩
  have rawFinal := exact_OpenLiteralGuardedFreeRawTarget raw sc st ty name w r actual
  have final := targetStaysAtom L sc st r after (bottomTerm ty) rawFinal (bottomAtom ty)
    ⟨Derivation.conjunctionRight queries⟩
  exact rebuildAddress (y.relabel j) sc st after (ctx.relabel j) ty (bottomTerm ty)
    target aligned.1 aligned.2.1 final

#print axioms exact_OpenLiteralAtomicBottomNoDirect
#print axioms exact_OpenLiteralAtomicFreeDirectBottom
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicDirectRulesProof
