module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursionProof (consValue consForward stepCases)
open ID1Completion.InternalListCodecSupportProof (consGraphRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedFilter (cell)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseScanRetentionTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_ScanRowBranches : ExactScanRowBranches :=
  NumberedWindowInternalSparseScanRetentionRowProof.rowBranches

private abbrev hits (E : Program 4) (h tail ctx ty k : OTerm α) :=
  eqn h k ⊔ (acceptEdge E ctx ty h k ⊔ scanGraph E tail ctx ty k)

private theorem hitsRename {β : Type} (E : Program 4) (h tail ctx ty k : OTerm α) (j : α → β) :
    (hits E h tail ctx ty k).relabel j = hits E (h.relabel j) (tail.relabel j)
      (ctx.relabel j) (ty.relabel j) (k.relabel j) := by
  change (eqn h k).relabel j ⊔ ((acceptEdge E ctx ty h k).relabel j ⊔ (scanGraph E tail ctx ty k).relabel j) = _
  simp only [eqnRelabel,acceptEdge,edgeTape,programRename,quadInputsRename,sucRelabel,zRelabel,scanRename]
  rfl

private theorem third (A B C D : Formula α) (input : Derivation body Γ (A ⊔ (B ⊔ C)))
    (move : Derivation body Γ (C.imp D)) : Nonempty (Derivation body Γ (A ⊔ (B ⊔ D))) := by
  have one : Derivation body (A :: Γ) (A ⊔ (B ⊔ D)) := orLeft (Derivation.hypothesis List.mem_cons_self)
  have two : Derivation body (B :: (B ⊔ C) :: Γ) (A ⊔ (B ⊔ D)) := orRight (orLeft (Derivation.hypothesis List.mem_cons_self))
  have c : Derivation body (C :: (B ⊔ C) :: Γ) C := Derivation.hypothesis List.mem_cons_self
  have three : Derivation body (C :: (B ⊔ C) :: Γ) (A ⊔ (B ⊔ D)) :=
    orRight (orRight (Derivation.implicationElimination (addHyp (addHyp move (B ⊔ C)) C) c))
  have bc : Derivation body ((B ⊔ C) :: Γ) (B ⊔ C) := Derivation.hypothesis List.mem_cons_self
  have rest := disjunctionElimination bc
    (Derivation.implicationIntroduction two) (Derivation.implicationIntroduction three)
  exact ⟨disjunctionElimination input (Derivation.implicationIntroduction one) (Derivation.implicationIntroduction rest)⟩

private theorem forward (E : Program 4) (seen h tail ctx ty k : OTerm α)
    (c : Nonempty (Derivation body Γ (cell seen h tail))) (g : Nonempty (Derivation body Γ (scanGraph E seen ctx ty k))) :
    Nonempty (Derivation body Γ (hits E h tail ctx ty k)) := by
  have step := consForward (constantZero 3) (scanStep E) seen h tail (suc z) (![ctx,ty,k] : Fin 3 → OTerm α) c g
  apply stepCases (constantZero 3) (scanStep E) (suc z) h tail (![ctx,ty,k] : Fin 3 → OTerm α) _ step
  intro β j Δ prev _ tailRun rowRun
  rw [tripleInputsRename] at tailRun rowRun
  simp only [sucRelabel,zRelabel] at rowRun
  rw [hitsRename]
  obtain ⟨rule⟩ := exact_ScanRowBranches E body β Δ (h.relabel j) prev (ctx.relabel j) (ty.relabel j) (k.relabel j)
  obtain ⟨row⟩ := rowRun
  let C := eqn prev (suc z)
  obtain ⟨p⟩ := tailRun
  obtain ⟨moved⟩ := outputTransport (body := body) (Gamma := C :: Δ) (scan E) prev (suc z)
    (scanTape (tail.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)) ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp p C⟩
  exact third _ _ _ _ (Derivation.implicationElimination (Derivation.conjunctionLeft rule) row)
    (Derivation.implicationIntroduction moved)

private theorem backward (E : Program 4) (seen h tail ctx ty k : OTerm α)
    (c : Nonempty (Derivation body Γ (cell seen h tail))) (input : Nonempty (Derivation body Γ (hits E h tail ctx ty k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  apply programCases (scan E) (scanTape tail ctx ty k) _
  intro β j Δ prev keep result
  rw [scanRename]
  simp only [scanTape,quadInputsRename] at result
  have cc := renameInto c j Δ keep
  change Nonempty (Derivation body Δ ((ID1Completion.InternalListCodecSupportProof.consGraph seen h tail).relabel j)) at cc
  rw [consGraphRename] at cc
  have i := renameInto input j Δ keep
  rw [hitsRename] at i
  let Q := scanGraph E (tail.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)
  obtain ⟨d⟩ := result
  obtain ⟨eq⟩ := valueUnique (body := body) (Gamma := Q :: Δ) (scan E) prev (suc z)
    (scanTape (tail.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)) ⟨addHyp d Q⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨i⟩ := i
  obtain ⟨args⟩ := third _ _ _ _ i (Derivation.implicationIntroduction eq)
  obtain ⟨law⟩ := exact_ScanRowBranches E body β Δ (h.relabel j) prev (ctx.relabel j) (ty.relabel j) (k.relabel j)
  exact consValue (constantZero 3) (scanStep E) (seen.relabel j) (h.relabel j) (tail.relabel j) prev (suc z)
    ![ctx.relabel j,ty.relabel j,k.relabel j] cc ⟨d⟩ ⟨Derivation.implicationElimination (Derivation.conjunctionRight law) args⟩

theorem exact_ScanOnCons : ExactScanOnCons := by
  intro E body α Γ seen h tail ctx ty k
  let C := cell seen h tail
  let A := scanGraph E seen ctx ty k
  let B := hits E h tail ctx ty k
  have c : Derivation body (C :: Γ) C := Derivation.hypothesis List.mem_cons_self
  obtain ⟨f⟩ := forward (Γ := A :: C :: Γ) E seen h tail ctx ty k ⟨addHyp c A⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨b⟩ := backward (Γ := B :: C :: Γ) E seen h tail ctx ty k ⟨addHyp c B⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction f) (Derivation.implicationIntroduction b))⟩

#print axioms exact_ScanRowBranches
#print axioms exact_ScanOnCons
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionChecks
