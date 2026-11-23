module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentRawHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (unaryRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (auxiliarySubst)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets (thinFormation)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
  (thinMatchingWindow thinSyntaxWindow thinCoveredWindow)
open NumberedWindowInternalSparseCoveredWindowOpenReportProof (coveredWindow exact_CoveredWindowReport)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards liftInputs)
open NumberedWindowInternalSparseTypedRawLiftGraphProof (wrap)

theorem windowIdentity (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1) :
    thinMatchingWindow C s baseW V = coveredWindow C s (thinSyntaxWindow baseW V) := rfl

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem formationSubst {β : Type} (W : Program 3) (ctx dom cod arg : OTerm α)
    (ts : α → OTerm β) :
    (thinFormation W ctx dom cod arg).subst (fun a => emb (ts a)) =
      thinFormation W (ctx.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) := by
  simp only [thinFormation,allEmbeddedSubst,impSubst,windowSubst,auxiliarySubst,liftTermSubst,rawConsSubst]
  rfl

theorem formationRename {β : Type} (W : Program 3) (ctx dom cod arg : OTerm α) (j : α → β) :
    (thinFormation W ctx dom cod arg).relabel j =
      thinFormation W (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (thinFormation W ctx dom cod arg).subst (fun a => emb (.var (j a))) = _
  rw [formationSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

private theorem form (W : Program 3) (ctx dom cod arg f : OTerm α)
    (supplied : Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg)))
    (typed : Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) f))) :
    Nonempty (Derivation body Γ (windowAt W ctx cod (auxiliaryTerm dom cod f arg))) := by
  obtain ⟨d⟩ := supplied
  obtain ⟨known⟩ := typed
  have h := Derivation.universalElimination (emb f) d
  simp only [thinFormation,instantiate,bindEmbedding,impSubst,windowSubst,auxiliarySubst,liftBind,varBind] at h
  exact ⟨Derivation.implicationElimination h known⟩

private theorem syntaxOnWindow (C : Program 3) (X : Program 2) (s : Settings)
    (baseW : Program 3) (V : Program 1) (ctx ty q : OTerm α)
    (h : Nonempty (Derivation body Γ (windowAt (thinMatchingWindow C s baseW V) ctx ty q))) :
    Nonempty (Derivation body Γ (programGraph V (suc z) ![q])) := by
  rw [windowIdentity] at h
  obtain ⟨read⟩ := exact_CoveredWindowReport C X s (thinSyntaxWindow baseW V) body α Γ ctx ty q
  obtain ⟨guard⟩ := h
  have base := Derivation.conjunctionLeft (Derivation.implicationElimination read guard)
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let side : Program 3 := .composition V (fun _ : Fin 1 => .projection 2)
  obtain ⟨parts⟩ := conjunctionRecover baseW side xs ⟨base⟩
  exact unaryRecover V (.projection 2) (suc z) q xs
    ⟨Derivation.conjunctionRight parts⟩ (projectionValue 2 xs)

/-- One actual raw function row supplies its two real arrow-admissions.
The single fixed-argument formation rule applies to their original q/r,
never to a canonical replacement function. On the same covered window this
derives both syntax guards and the exact wrapped typed raw row. -/
theorem formed (C root other baseW : Program 3) (X : Program 2) (s : Settings) (V : Program 1)
    (ctx dom cod arg q w r : OTerm α) :
    let W := thinMatchingWindow C s baseW V
    let R := typedRaw5 root other W V
    let l := auxiliaryTerm dom cod q arg
    let y := auxiliaryTerm dom cod r arg
    Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg)) →
    Nonempty (Derivation body Γ (programGraph R (suc z) ![ctx,rawCons dom cod,q,w,r])) →
    Nonempty (Derivation body Γ
      (windowAt W ctx cod l ⊓ (windowAt W ctx cod y ⊓
        programGraph R (suc z) ![ctx,cod,l,functionWitnessTerm w,y]))) := by
  intro W R l y ready step
  obtain ⟨rule⟩ := exact_OpenTypedRaw5 body root other W V α Γ ctx (rawCons dom cod) q w r
  obtain ⟨a⟩ := step
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft rule) a
  have endpoints := Derivation.conjunctionRight calls
  obtain ⟨left⟩ := form W ctx dom cod arg q ready ⟨Derivation.conjunctionLeft endpoints⟩
  obtain ⟨right⟩ := form W ctx dom cod arg r ready ⟨Derivation.conjunctionRight endpoints⟩
  obtain ⟨sl⟩ := syntaxOnWindow C X s baseW V ctx cod l ⟨left⟩
  obtain ⟨sr⟩ := syntaxOnWindow C X s baseW V ctx cod y ⟨right⟩
  have lifted : Nonempty (Derivation body Γ (liftInputs root other W V ctx dom cod arg q w r)) :=
    ⟨Derivation.conjunctionIntroduction a
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction sl sr)
        (Derivation.conjunctionIntroduction left right))⟩
  obtain ⟨b⟩ := wrap root other W V ctx dom cod arg q w r lifted
  exact ⟨Derivation.conjunctionIntroduction left (Derivation.conjunctionIntroduction right b)⟩

#print axioms windowIdentity
#print axioms formed
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentRawHopProof
