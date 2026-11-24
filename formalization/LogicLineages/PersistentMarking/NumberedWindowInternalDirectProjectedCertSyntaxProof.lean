module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRawListRecursionSyntaxProof (recRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets scratchTargets)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt reports)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)

variable {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem renameUnary (p : Program 1) (n raw : OTerm α)
    (h : Nonempty (Derivation B Γ (unary p (suc n) raw))) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (unary p (suc (n.relabel j)) (raw.relabel j))) := by
  simpa only [unaryRename,sucRelabel] using renameInto h j Δ keep

theorem renameShared (q v : Program 2) (r : Program 3)
    (src dst kRaw dRaw aRaw s t k d a p sk tp : OTerm α)
    (h : Reports q v r B Γ src dst kRaw dRaw aRaw s t k d a p sk tp)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Reports q v r B Δ (src.relabel j) (dst.relabel j) (kRaw.relabel j) (dRaw.relabel j)
      (aRaw.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) (d.relabel j)
      (a.relabel j) (p.relabel j) (sk.relabel j) (tp.relabel j) := by
  refine ⟨renameUnary parser s src h.sourceParsed j keep,
    renameUnary parser t dst h.targetParsed j keep,
    renameUnary parser k kRaw h.keptParsed j keep,
    renameUnary parser d dRaw h.removedParsed j keep,
    renameUnary parser a aRaw h.insertedParsed j keep,
    renameUnary insertedTargets p aRaw h.rawProjection j keep,
    renameUnary scratchTargets p a h.scratchProjection j keep,
    renamePair append sk k d h.sourceAppend j keep,
    renamePair append tp k p h.targetAppend j keep,?_,?_,?_⟩
  · simpa only [sucRelabel,zRelabel] using renamePair q (suc z) s sk h.sourceObserved j keep
  · simpa only [sucRelabel,zRelabel] using renamePair v (suc z) t tp h.targetObserved j keep
  · simpa only [loopAccept,recRename,inputsRename,oneTerm,sucRelabel,zRelabel] using
      renameInto h.scanObserved j Δ keep

private theorem movePositive (r : Program 3) (row dom cert old key : OTerm α)
    (x : Nonempty (Derivation B Γ (unary (field 0) old row)))
    (y : Nonempty (Derivation B Γ (unary (field 0) key row)))
    (h : Nonempty (Derivation B Γ (programGraph r oneTerm ![dom,cert,old]))) :
    Nonempty (Derivation B Γ (programGraph r oneTerm ![dom,cert,key])) := by
  obtain ⟨e⟩ := valueUnique (field 0) old key ![row] x y
  unfold programGraph at h ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula r) oneTerm
    ![dom,cert,old] ![dom,cert,key] _ h
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Nonempty (Derivation B Γ (equal dom dom))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl dom⟩
  · refine Fin.cases ?_ (fun l => ?_) j
    · change Nonempty (Derivation B Γ (equal cert cert))
      rw [equalEqn]
      exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl cert⟩
    · obtain rfl := Fin.eq_zero l
      change Nonempty (Derivation B Γ (equal old key))
      rw [equalEqn]
      exact ⟨e⟩

theorem pinTarget (r : Program 3) (raw row removed old key dom cert : OTerm α)
    (hit : NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Γ raw row removed old dom cert)
    (guard : Nonempty (Derivation B Γ (unary (guardAt 4) (suc z) row)))
    (actual : Nonempty (Derivation B Γ (unary (field 0) key row))) :
    NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Γ raw row removed key dom cert := by
  obtain ⟨g⟩ := guard
  obtain ⟨f⟩ := actual
  obtain ⟨d⟩ := hit.dominatorField
  obtain ⟨c⟩ := hit.certificateField
  obtain ⟨bridge⟩ := exactOpenTriple B α Γ 4 row key dom cert
  have checked : Derivation B Γ (reports 4 row key dom cert) :=
    Derivation.conjunctionIntroduction g
      (Derivation.conjunctionIntroduction f (Derivation.conjunctionIntroduction d c))
  have packed := Derivation.implicationElimination (Derivation.conjunctionRight bridge) checked
  obtain ⟨original⟩ := hit.original
  have rest := Derivation.conjunctionRight original
  obtain ⟨positive⟩ := movePositive r row dom cert old key hit.targetField ⟨f⟩
    ⟨Derivation.conjunctionRight rest⟩
  exact ⟨hit.parsed,⟨f⟩,hit.dominatorField,hit.certificateField,
    ⟨Derivation.conjunctionIntroduction packed
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft rest) positive)⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertSyntaxProof
