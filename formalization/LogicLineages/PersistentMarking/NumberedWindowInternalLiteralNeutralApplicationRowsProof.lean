module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileNeutralSourceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralApplicationRowsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameAddress)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportUnfold reportBinder auxiliaryRename)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalLiteralAuxProfileNeutralSourceProof (lambdaAt exact_OpenNeutralHeaderNotLambda)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Exact elimination of a neutral function's accepted application
edge. The caller needs only those two original predicates, not
manually supplied coordinates, selected result or non-lambda tag.
All witness rows are in their original fresh object scopes. -/
theorem exact_OpenNeutralApplicationRows (i : Program 1) (L : Program 3) (x u t : OTerm α)
    (goal : Formula α)
    (neutral : D B Γ (atom neutralSource x))
    (accepted : D B Γ (programGraph (applicationGuard i L) (suc z) ![x,u,t]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx result dom cod fn arg atResult header : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (unary i (suc z) (x.relabel j)) →
      D B Δ (unary i (suc z) (u.relabel j)) →
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
      D B Δ (programGraph L (suc atResult) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
      D B Δ (eqn (t.relabel j) (addressTerm ctx cod atResult)) →
      D B Δ (unary cellHead header fn) → D B Δ (lambdaAt header) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  obtain ⟨out⟩ := forward i L x u t accepted
  let tail := Derivation.conjunctionRight out
  have iX : D B Γ (unary i (suc z) x) := ⟨Derivation.conjunctionLeft out⟩
  have iU : D B Γ (unary i (suc z) u) := ⟨Derivation.conjunctionLeft tail⟩
  apply rowCases L x u t goal ⟨Derivation.conjunctionRight tail⟩
  intro β j Δ ctx result dom cod fn arg keep known
  obtain ⟨parsed⟩ := known
  let n : β → β ⊕ Fin 1 := Sum.inl
  let k : OTerm (β ⊕ Fin 1) := .var (.inr 0)
  let row := reportBinder L ctx cod (auxiliaryTerm dom cod fn arg) (t.relabel j)
  let Ω := row :: Δ.map weaken
  have keepN (f : Formula β) (hf : f ∈ Δ) : f.relabel n ∈ Ω :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have witnessRow : Derivation B Ω row := Derivation.hypothesis List.mem_cons_self
  have target : D B Ω ((goal.relabel j).relabel n) := by
    apply programCases cellHead ![fn.relabel n] _
    intro γ m Ξ head keepM headReport
    let a := m ∘ n
    let b := a ∘ j
    have keepA (f : Formula β) (hf : f ∈ Δ) : f.relabel a ∈ Ξ := by
      simpa only [a,formulaRelabelComposition] using keepM _ (keepN f hf)
    have keepB (f : Formula α) (hf : f ∈ Γ) : f.relabel b ∈ Ξ := by
      simpa only [b,formulaRelabelComposition] using keepA _ (keep f hf)
    have head' : D B Ξ (unary cellHead head (fn.relabel a)) := by
      rw [inputsRename] at headReport
      simpa only [unary,a,Term.relabel_relabel] using headReport
    have p := renameInto (⟨Derivation.conjunctionLeft parsed⟩ :
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg)) a Ξ keepA
    rw [NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof.inputsRename] at p
    have parsed' : D B Ξ
        (parsedApplicationInputs (x.relabel b) (u.relabel b) (ctx.relabel a) (result.relabel a)
          (dom.relabel a) (cod.relabel a) (fn.relabel a) (arg.relabel a)) := by
      simpa only [b,Term.relabel_relabel] using p
    obtain ⟨input⟩ := parsed'
    let addrs := Derivation.conjunctionLeft (Derivation.conjunctionRight
      (Derivation.conjunctionRight (Derivation.conjunctionRight input)))
    have raw : D B Ξ (unary rawLeast (fn.relabel a) (x.relabel b)) :=
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight addrs)⟩
    have nn := renameInto neutral b Ξ keepB
    rw [atomRename] at nn
    have non := exact_OpenNeutralHeaderNotLambda (x.relabel b) (fn.relabel a) head nn raw head'
    have one := renameInto iX b Ξ keepB
    have two := renameInto iU b Ξ keepB
    simp only [unaryRename,sucRelabel,zRelabel] at one two
    have stored : D B Ω (programGraph L (suc k) ![ctx.relabel n,cod.relabel n,
      (auxiliaryTerm dom cod fn arg).relabel n]) := ⟨Derivation.conjunctionLeft witnessRow⟩
    have stored' := renameInto stored m Ξ keepM
    simp only [programRename,tripleInputsRename,sucRelabel,auxiliaryRename,Term.relabel_relabel] at stored'
    have eq : D B Ω (eqn ((t.relabel j).relabel n) (addressTerm (ctx.relabel n) (cod.relabel n) k)) :=
      ⟨Derivation.conjunctionRight witnessRow⟩
    have eq' := renameInto eq m Ξ keepM
    rw [eqnRelabel,renameAddress] at eq'
    have returned := use γ b Ξ (ctx.relabel a) (result.relabel a) (dom.relabel a) (cod.relabel a)
      (fn.relabel a) (arg.relabel a) (k.relabel m) head keepB one two ⟨input⟩ stored'
      (by simpa only [a,b,Term.relabel_relabel,Function.comp_assoc] using eq') head' non
    simpa only [a,b,formulaRelabelComposition,Function.comp_assoc] using returned
  obtain ⟨body⟩ := target
  have envelope : D B Δ (NumberedWindowInternalSparseApplicationOutputCoreTargets.outputReport L ctx cod
      (auxiliaryTerm dom cod fn arg) (t.relabel j)) := ⟨Derivation.conjunctionRight parsed⟩
  rw [reportUnfold] at envelope
  obtain ⟨witness⟩ := envelope
  exact ⟨Derivation.existentialElimination witness body⟩

#print axioms exact_OpenNeutralApplicationRows
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralApplicationRowsProof
