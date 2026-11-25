module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPerTickCertifiedCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectPhysicalReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPerTickAddressedCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport equalEqn)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm congSuc)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenAtomicRecognition)
open NumberedWindowInternalLiteralAtomicAddressReportProof (alignSource rebuildAddress renameAddress)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (rawBottom)
open NumberedWindowInternalLiteralAtomicCoveredCasesProof (PerTickRaw)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (auxiliaryDecorator)
open NumberedWindowInternalLiteralAuxProfileNeutralSourceProof (lambdaAt)
open NumberedWindowInternalLiteralPerTickCertifiedCasesProof (exact_OpenPerTickCertifiedAuxBottomOrChild)
open NumberedWindowInternalLiteralDirectPhysicalReportProof (exact_OpenDirectPhysicalReportCases)
open NumberedWindowInternalNeutralFactsTargets (direct atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

private theorem retape {B : Positive (Fin 1)}
    (L : Program 3) (ctx ty before sc st source q : OTerm α)
    (e₁ : D B Γ (eqn sc ctx)) (e₂ : D B Γ (eqn st ty)) (e₃ : D B Γ (eqn source before))
    (h : D B Γ (programGraph L (suc before) ![ctx,ty,q])) :
    D B Γ (programGraph L (suc source) ![sc,st,q]) := by
  obtain ⟨c⟩ := e₁
  obtain ⟨t⟩ := e₂
  obtain ⟨v⟩ := e₃
  have same : D B Γ (programGraph L (suc before) ![sc,st,q]) := by
    unfold programGraph at h ⊢
    apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula L)
      (suc before) ![ctx,ty,q] ![sc,st,q] _ h
    intro i
    rw [onEquality]
    exact Fin.cases (⟨symm c⟩ : D B Γ (eqn ctx sc))
      (Fin.cases (⟨symm t⟩ : D B Γ (eqn ty st))
        (Fin.cases (⟨refl q⟩ : D B Γ (eqn q q)) (fun x => Fin.elim0 x))) i
  exact outputTransport L (suc before) (suc source) ![sc,st,q] ⟨congSuc (symm v)⟩ same

private theorem twoRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

/-- Exact bottom alternative on the original direct checker. The
source is aligned with the actual application output address by
functionality of its three original selectors, so no endpoint parser
premise remains. Only the genuine contextual-child branch is passed
to the explicit continuation. -/
theorem exact_OpenPerTickApplicationDirectCases
    (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (base : Program 2) (T V i cv tv : Program 1)
    (L₀ : Program 3) (c : Nat) (t y ctx dom cod fn arg k h : OTerm α)
    (goal : Formula α) :
    let W := coveredMemoWindow C s base T V
    let raw := PerTickRaw C s leaf other base T V
    let L := guardedLeast (headerLeast (auxiliaryDecorator L₀))
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (eqn t (addressTerm ctx cod k)) →
    D B Γ (programGraph L (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
    D B Γ (unary cellHead h fn) → D B Γ (lambdaAt h) →
    D B Γ (direct data (hop cv tv R L) c t y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (sc st before after cert q w r d e f a child d' e' g a' : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (addressReport (y.relabel j) sc st after) →
      D B Δ (eqn sc (ctx.relabel j)) → D B Δ (eqn st (cod.relabel j)) →
      D B Δ (eqn before (k.relabel j)) →
      D B Δ (programGraph L (suc before) ![sc,st,auxiliaryTerm (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j)]) →
      Parts B Δ q w r d e f a child d' e' g a' →
      D B Δ (programGraph (guardedRaw raw) (suc z) ![sc,rawCons d e,f,child,g] ⊓
        (childAtWindow W V sc d a ⊓ (hasLeast C X W s sc (rawCons d e) f ⊓
          (hasLeast C X W s sc (rawCons d e) g ⊓ hasLeast C X W s sc d a)))) →
      D B Δ (hopCalls R L sc st before cert after q w r) →
      D B Δ (goal.relabel j)) →
    D B Γ (atom bottomSource y ⊔ goal) := by
  intro W raw L R data B address selected head notL directHop takeChild
  let disj := atom bottomSource y ⊔ goal
  let applySplit := exact_OpenDirectPhysicalReportCases i cv tv R L c t y disj directHop
  apply applySplit
  intro β j Δ cert sc st before after keep hx hy _ _ reports
  apply reportCases R L sc st before cert after (disj.relabel j) reports
  intro γ l Ω q w r stay calls
  let m := l ∘ j
  have keepM (f : Formula α) (hf : f ∈ Γ) : f.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep f hf)
  have matching := renameInto address m Ω keepM
  rw [eqnRelabel,renameAddress] at matching
  have lx := renameInto hx l Ω stay
  rw [addressReportRename] at lx
  have rx := renameInto hy l Ω stay
  rw [addressReportRename] at rx
  let c₁ := sc.relabel l
  let t₁ := st.relabel l
  let b₁ := before.relabel l
  let a₁ := after.relabel l
  have lx' : D B Ω (addressReport (t.relabel m) c₁ t₁ b₁) :=
    by simpa only [m,Term.relabel_relabel] using lx
  have rx' : D B Ω (addressReport (y.relabel m) c₁ t₁ a₁) :=
    by simpa only [m,Term.relabel_relabel] using rx
  obtain ⟨gc,gt,gb⟩ := alignSource (t.relabel m) (ctx.relabel m) (cod.relabel m) (k.relabel m)
    c₁ t₁ b₁ matching lx'
  have app := renameInto selected m Ω keepM
  rw [programRename,tripleInputsRename,sucRelabel,auxiliaryRename] at app
  have ready := retape L (ctx.relabel m) (cod.relabel m) (k.relabel m) c₁ t₁ b₁ _ gc gt gb app
  have hh := renameInto head m Ω keepM
  rw [unaryRename] at hh
  have hn := renameInto notL m Ω keepM
  rw [lambdaAt,programRename,twoRename,zRelabel,numeralRename] at hn
  have done : D B Ω (disj.relabel m) := by
    apply exact_OpenPerTickCertifiedAuxBottomOrChild C X s leaf other base T V i cv tv L₀
      c₁ t₁ (dom.relabel m) (cod.relabel m) (fn.relabel m) (arg.relabel m)
      b₁ (cert.relabel l) a₁ q w r (h.relabel m) (disj.relabel m) ready hh hn calls
    · intro δ n Ξ retain bottom
      have ry := renameInto rx' n Ξ retain
      rw [addressReportRename] at ry
      have full := rebuildAddress ((y.relabel m).relabel n) (c₁.relabel n) (t₁.relabel n) (a₁.relabel n)
        (c₁.relabel n) (t₁.relabel n) (rawBottom (t₁.relabel n)) ry ⟨refl _⟩ ⟨refl _⟩ bottom
      have built : D B Ξ (equal ((y.relabel m).relabel n) (packedBottomTerm (c₁.relabel n) (t₁.relabel n))) := by
        rw [equalEqn]
        exact full
      obtain ⟨b⟩ := exact_OpenAtomicRecognition.2 B δ Ξ ((y.relabel m).relabel n) (c₁.relabel n) (t₁.relabel n) built
      change D B Ξ (((atom bottomSource y).relabel m).relabel n ⊔ ((goal.relabel m).relabel n))
      rw [atomRename,atomRename]
      exact ⟨orLeft (Derivation.conjunctionRight b)⟩
    · intro δ n Ξ d e f a child d' e' g a' retain parts fits known
      let p := n ∘ m
      have keepP (φ : Formula α) (hφ : φ ∈ Γ) : φ.relabel p ∈ Ξ := by
        simpa only [p,formulaRelabelComposition] using retain _ (keepM φ hφ)
      have ry := renameInto rx' n Ξ retain
      rw [addressReportRename] at ry
      have app' := renameInto ready n Ξ retain
      rw [programRename,tripleInputsRename,sucRelabel,auxiliaryRename] at app'
      have ec := renameInto gc n Ξ retain
      have et := renameInto gt n Ξ retain
      have ek := renameInto gb n Ξ retain
      rw [eqnRelabel] at ec et ek
      obtain ⟨right⟩ := takeChild δ p Ξ (c₁.relabel n) (t₁.relabel n) (b₁.relabel n) (a₁.relabel n)
        ((cert.relabel l).relabel n) (q.relabel n) (w.relabel n) (r.relabel n)
        d e f a child d' e' g a' keepP
        (by simpa only [p,Term.relabel_relabel] using ry)
        (by simpa only [p,Term.relabel_relabel] using ec)
        (by simpa only [p,Term.relabel_relabel] using et)
        (by simpa only [p,Term.relabel_relabel] using ek)
        (by simpa only [p,Term.relabel_relabel] using app') parts fits known
      change D B Ξ (((atom bottomSource y).relabel m).relabel n ⊔ ((goal.relabel m).relabel n))
      exact ⟨orRight (by simpa only [p,formulaRelabelComposition] using right)⟩
  simpa only [m,formulaRelabelComposition] using done

#print axioms exact_OpenPerTickApplicationDirectCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPerTickAddressedCasesProof
