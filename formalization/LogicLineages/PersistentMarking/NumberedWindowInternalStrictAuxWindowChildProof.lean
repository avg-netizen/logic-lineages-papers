module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowChildProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (outputTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowStepTargets (reportTest intrinsicQuery)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalAuxMeasureStepTargets (childAt measureAt)
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext earlierValue)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rowValue (R C : Program 4) (slot : Nat) (ctx prior old raw ty value : OTerm α)
    (small : Nonempty (Derivation body Γ (ltF raw (suc prior))))
    (selectedField : Nonempty (Derivation body Γ (programGraph (childAt slot) raw ![prior,old,ctx,z])))
    (code : Nonempty (Derivation body Γ (programGraph C (suc ty) ![prior,old,ctx,z])))
    (tested : Nonempty (Derivation body Γ (programGraph (reportTest slot C) (suc z) ![prior,old,ctx,z])))
    (previous : Nonempty (Derivation body Γ (contextTable R old prior ctx)))
    (actual : Nonempty (Derivation body Γ (contextRow R value raw ctx))) :
    Nonempty (Derivation body Γ (windowGraph (intrinsicQuery (selectedIntrinsic R)) ctx ty raw)) := by
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have read := earlierValue R slot raw value prior old ctx selectedField small actual previous
  have testedEquality : Nonempty (Derivation body Γ (programGraph equalityTest (suc z) ![value,suc ty])) := by
    apply compositionRecover equalityTest (Fin.cons (measureAt slot) (Fin.cons C Fin.elim0))
      (suc z) xs ![value,suc ty] tested
    intro i
    exact Fin.cases read (Fin.cases code (fun j => Fin.elim0 j)) i
  have same := equalityOfAcceptance value (suc ty) testedEquality
  have accepted : Nonempty (Derivation body Γ (contextRow R (suc ty) raw ctx)) :=
    outputTransport (scratchRow (constantZero 2) R) value (suc ty) ![raw,ctx,z] same actual
  exact (exact_OpenIntrinsicQuery (selectedIntrinsic R) body α Γ ctx ty raw).mpr
    ((sameContext R (suc ty) ctx raw).mpr accepted)

theorem recoverChild (R C : Program 4) (slot : Nat) (ctx prior old raw ty : OTerm α)
    (small : Nonempty (Derivation body Γ (ltF raw (suc prior))))
    (selectedField : Nonempty (Derivation body Γ (programGraph (childAt slot) raw ![prior,old,ctx,z])))
    (code : Nonempty (Derivation body Γ (programGraph C (suc ty) ![prior,old,ctx,z])))
    (tested : Nonempty (Derivation body Γ (programGraph (reportTest slot C) (suc z) ![prior,old,ctx,z])))
    (previous : Nonempty (Derivation body Γ (contextTable R old prior ctx))) :
    Nonempty (Derivation body Γ (windowGraph (intrinsicQuery (selectedIntrinsic R)) ctx ty raw)) := by
  apply programCases (scratchRow (constantZero 2) R) ![raw,ctx,z] _
  intro β j Δ value keep actual
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel]
  simp only [tripleInputsRename,zRelabel] at actual
  have smaller := renameInto small j Δ keep
  have field' := renameInto selectedField j Δ keep
  have code' := renameInto code j Δ keep
  have tested' := renameInto tested j Δ keep
  have previous' := renameInto previous j Δ keep
  simp only [orderRename,sucRelabel] at smaller
  simp only [programRename,quadInputsRename,zRelabel,sucRelabel] at field' code' tested'
  simp only [contextTable,programRename,tripleInputsRename,zRelabel] at previous'
  exact rowValue R C slot (ctx.relabel j) (prior.relabel j) (old.relabel j) (raw.relabel j) (ty.relabel j)
    value smaller field' code' tested' previous' actual

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowChildProof
