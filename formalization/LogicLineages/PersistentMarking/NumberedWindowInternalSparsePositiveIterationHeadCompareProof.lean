module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateExplicitChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadCompareProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl trans)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (iterateStep iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph stepGraph loopGraph)
open NumberedWindowInternalSparsePositiveFoldOpenChecks (exact_OpenFoldBase)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof
open NumberedWindowInternalSparsePositiveIterationCoordinateExplicitChecks (exact_OpenStepCoordinates)
open NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem compareAt (raw : Program 5) (least : Program 3) (p : Plan α) (fuel l r : OTerm α)
    (equalAt : Nonempty (Derivation body Γ (sameAt raw least fuel p)))
    (left : Nonempty (Derivation body Γ (oldLoop raw least p l (suc fuel))))
    (right : Nonempty (Derivation body Γ (newLoop raw least p r fuel))) :
    Nonempty (Derivation body Γ (eqn l r)) := by
  have cut := actualFiniteUniversalElimination body α 2 Γ (headMatrix raw least fuel p)
    (fun i => emb (![l,r] i)) equalAt
  rw [headWitness] at cut
  obtain ⟨cut⟩ := cut
  obtain ⟨l⟩ := left
  obtain ⟨r⟩ := right
  exact ⟨Derivation.implicationElimination cut (Derivation.conjunctionIntroduction l r)⟩

theorem compareBase (raw : Program 5) (least : Program 3) (p : Plan α)
    (l r seed seed' : OTerm α)
    (earlier : Nonempty (Derivation body Γ (scratchGraph seed p.originalCertificate p.originalCurrent)))
    (later : Nonempty (Derivation body Γ (scratchGraph seed' p.nextCertificate p.nextCurrent)))
    (takeStep : Nonempty (Derivation body Γ
      (stepGraph raw least seed' z seed p.context p.ty p.originalCurrent p.originalCertificate)))
    (left : Nonempty (Derivation body Γ (oldLoop raw least p l (suc z))))
    (right : Nonempty (Derivation body Γ (newLoop raw least p r z))) :
    Nonempty (Derivation body Γ (eqn l r)) := by
  have zeroOld := closedApply
    (exact_OpenFoldBase body raw least α seed p.context p.ty p.originalCurrent p.originalCertificate) earlier
  have zeroNew := closedApply
    (exact_OpenFoldBase body raw least α seed' p.context p.ty p.nextCurrent p.nextCertificate) later
  have after := loopIntro raw least seed' seed z p.context p.ty p.originalCurrent p.originalCertificate
    zeroOld takeStep
  obtain ⟨e1⟩ := valueUnique (iterateState raw least) l seed'
    (loopArgs (suc z) p.context p.ty p.originalCurrent p.originalCertificate) left after
  obtain ⟨e2⟩ := valueUnique (iterateState raw least) seed' r
    (loopArgs z p.context p.ty p.nextCurrent p.nextCertificate) zeroNew right
  exact ⟨trans e1 e2⟩

private theorem movePrior (raw : Program 5) (least : Program 3)
    (out k earlier later c ty start cert : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn earlier later)))
    (known : Nonempty (Derivation body Γ (stepGraph raw least out k earlier c ty start cert))) :
    Nonempty (Derivation body Γ (stepGraph raw least out k later c ty start cert)) := by
  apply graphInputTransport body α 6 Γ (OrdinaryArithmetic.graphFormula (iterateStep raw least)) out
    (call6 k earlier c ty start cert) (call6 k later c ty start cert) _ known
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl k⟩ (Fin.cases eq (Fin.cases ⟨refl c⟩ (Fin.cases ⟨refl ty⟩
    (Fin.cases ⟨refl start⟩ (Fin.cases ⟨refl cert⟩ (fun u => Fin.elim0 u)))))) i

private theorem carryNext (raw : Program 5) (least : Program 3) (p : Plan α)
    (fuel l r pv qv : OTerm α)
    (equalAt : Nonempty (Derivation body Γ (sameAt raw least fuel p)))
    (pold : Nonempty (Derivation body Γ (oldLoop raw least p pv (suc fuel))))
    (pnew : Nonempty (Derivation body Γ (newLoop raw least p qv fuel)))
    (before : Nonempty (Derivation body Γ (oldLoop raw least p l (suc (suc fuel)))))
    (after : Nonempty (Derivation body Γ (newLoop raw least p r (suc fuel)))) :
    Nonempty (Derivation body Γ (eqn l r)) := by
  have e := compareAt raw least p fuel pv qv equalAt pold pnew
  have earlierStep := loopRead raw least l pv (suc fuel) p.context p.ty
    p.originalCurrent p.originalCertificate pold before
  have laterStep := loopRead raw least r qv fuel p.context p.ty p.nextCurrent p.nextCertificate pnew after
  have alignedPrior := movePrior raw least l (suc fuel) pv qv p.context p.ty
    p.originalCurrent p.originalCertificate e earlierStep
  obtain ⟨coordinates⟩ := exact_OpenStepCoordinates body raw least α l qv p.context p.ty
    (suc fuel) p.originalCurrent p.originalCertificate fuel p.nextCurrent p.nextCertificate
  have aligned := closedApply ⟨Derivation.conjunctionLeft coordinates⟩ alignedPrior
  exact valueUnique (iterateStep raw least) l r
    (call6 fuel qv p.context p.ty p.nextCurrent p.nextCertificate) aligned laterStep

private theorem chooseRight (raw : Program 5) (least : Program 3) (p : Plan α)
    (fuel l r pv : OTerm α)
    (equalAt : Nonempty (Derivation body Γ (sameAt raw least fuel p)))
    (pold : Nonempty (Derivation body Γ (oldLoop raw least p pv (suc fuel))))
    (before : Nonempty (Derivation body Γ (oldLoop raw least p l (suc (suc fuel)))))
    (after : Nonempty (Derivation body Γ (newLoop raw least p r (suc fuel)))) :
    Nonempty (Derivation body Γ (eqn l r)) := by
  apply programCases (iterateState raw least) (loopArgs fuel p.context p.ty p.nextCurrent p.nextCertificate) _
  intro β j Δ qv hJ right
  rw [eqnRelabel]
  rw [loopArgsRename] at right
  have eq := renameInto equalAt j Δ hJ
  rw [sameAtRename] at eq
  have past := moveLoop j Δ hJ raw least pv (suc fuel) p.context p.ty p.originalCurrent p.originalCertificate pold
  have prev := moveLoop j Δ hJ raw least l (suc (suc fuel)) p.context p.ty
    p.originalCurrent p.originalCertificate before
  have later := moveLoop j Δ hJ raw least r (suc fuel) p.context p.ty p.nextCurrent p.nextCertificate after
  simp only [sucRelabel] at past prev later
  exact carryNext raw least (p.map (fun t => t.relabel j)) (fuel.relabel j)
    (l.relabel j) (r.relabel j) (pv.relabel j) qv eq past right prev later

theorem compareNext (raw : Program 5) (least : Program 3) (p : Plan α)
    (fuel l r : OTerm α)
    (equalAt : Nonempty (Derivation body Γ (sameAt raw least fuel p)))
    (before : Nonempty (Derivation body Γ (oldLoop raw least p l (suc (suc fuel)))))
    (after : Nonempty (Derivation body Γ (newLoop raw least p r (suc fuel)))) :
    Nonempty (Derivation body Γ (eqn l r)) := by
  apply programCases (iterateState raw least)
    (loopArgs (suc fuel) p.context p.ty p.originalCurrent p.originalCertificate) _
  intro β j Δ pv hJ left
  rw [eqnRelabel]
  rw [loopArgsRename,sucRelabel] at left
  have eq := renameInto equalAt j Δ hJ
  rw [sameAtRename] at eq
  have prev := moveLoop j Δ hJ raw least l (suc (suc fuel)) p.context p.ty
    p.originalCurrent p.originalCertificate before
  have later := moveLoop j Δ hJ raw least r (suc fuel) p.context p.ty p.nextCurrent p.nextCertificate after
  simp only [sucRelabel] at prev later
  exact chooseRight raw least (p.map (fun t => t.relabel j)) (fuel.relabel j)
    (l.relabel j) (r.relabel j) pv eq left prev later

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadCompareProof
