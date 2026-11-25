module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports packedBody rawConsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (readNode)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalFreshProbeParsedEmitter (addressTag addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem renameFree {β : Type} (t n : OTerm α) (j : α → β) :
    (freeTerm t n).relabel j = freeTerm (t.relabel j) (n.relabel j) := by
  simp only [freeTerm,packedBody,rawConsRename,zRelabel]

theorem renameBottom {β : Type} (t : OTerm α) (j : α → β) :
    (bottomTerm t).relabel j = bottomTerm (t.relabel j) := by
  simp only [bottomTerm,packedBody,rawConsRename,numeralRename,zRelabel]

theorem renameAddress {β : Type} (c t k : OTerm α) (j : α → β) :
    (addressTerm c t k).relabel j = addressTerm (c.relabel j) (t.relabel j) (k.relabel j) := by
  change (rawCons (numeral 3) (packedBody [c,t,k])).relabel j =
    rawCons (numeral 3) (packedBody [c.relabel j,t.relabel j,k.relabel j])
  simp only [packedBody,rawConsRename,numeralRename,zRelabel]

/-- The three reported output coordinates agree with their corresponding
fields on the literal source, by functionality of each actual selector. -/
theorem alignSource (x c t k a b d : OTerm α)
    (eq : D B Γ (eqn x (addressTerm c t k))) (held : D B Γ (addressReport x a b d)) :
    D B Γ (eqn a c) ∧ D B Γ (eqn b t) ∧ D B Γ (eqn d k) := by
  obtain ⟨h⟩ := held
  let first := Derivation.conjunctionRight h
  let rest := Derivation.conjunctionRight first
  let src := addressTerm c t k
  obtain ⟨_,context,type,least⟩ := literalAddress (body := B) (Γ := Γ) c t k
  exact ⟨valueUnique rawContext a c ![src]
      (headTransport rawContext a x src ![] eq ⟨Derivation.conjunctionLeft first⟩) context,
    valueUnique rawResult b t ![src]
      (headTransport rawResult b x src ![] eq ⟨Derivation.conjunctionLeft rest⟩) type,
    valueUnique rawLeast d k ![src]
      (headTransport rawLeast d x src ![] eq ⟨Derivation.conjunctionRight rest⟩) least⟩

/-- Adjust the reported coordinate values by internal equalities and
reconstruct the original literal address. No synthetic address is
injected into the accepted graph. -/
theorem rebuildAddress (y a b d c t k : OTerm α)
    (held : D B Γ (addressReport y a b d))
    (e₁ : D B Γ (eqn a c)) (e₂ : D B Γ (eqn b t)) (e₃ : D B Γ (eqn d k)) :
    D B Γ (eqn y (addressTerm c t k)) := by
  obtain ⟨h⟩ := held
  let fields := Derivation.conjunctionRight h
  let tail := Derivation.conjunctionRight fields
  have tag : D B Γ (unary addressTag (numeral 3) y) := literalGraph 3 ![y]
  have reports : Reports B Γ y cellTail [c,t,k] :=
    ⟨outputTransport rawContext a c ![y] e₁ ⟨Derivation.conjunctionLeft fields⟩,
     outputTransport rawResult b t ![y] e₂ ⟨Derivation.conjunctionLeft tail⟩,
     outputTransport rawLeast d k ![y] e₃ ⟨Derivation.conjunctionRight tail⟩,
     True.intro⟩
  exact readNode addressTag y (numeral 3) [c,t,k] tag ⟨Derivation.conjunctionLeft h⟩ reports

theorem replaceRawSource (raw : Program 5) (c t q q' w r : OTerm α)
    (eq : D B Γ (eqn q q')) (held : D B Γ (programGraph raw (suc z) ![c,t,q,w,r])) :
    D B Γ (programGraph raw (suc z) ![c,t,q',w,r]) := by
  unfold programGraph at held ⊢
  apply graphInputTransport B α 5 Γ (OrdinaryArithmetic.graphFormula raw) (suc z)
    ![c,t,q,w,r] ![c,t,q',w,r] _ held
  intro i
  rw [onEquality]
  change D B Γ (eqn ((![c,t,q,w,r] : Fin 5 → OTerm α) i) ((![c,t,q',w,r] : Fin 5 → OTerm α) i))
  have self (x : OTerm α) : D B Γ (eqn x x) := ⟨ID1Completion.InternalTagArithmeticSupportProof.refl x⟩
  exact Fin.cases (self c) (Fin.cases (self t)
    (Fin.cases eq (Fin.cases (self w) (Fin.cases (self r) (fun e => Fin.elim0 e))))) i

#print axioms alignSource
#print axioms rebuildAddress
#print axioms replaceRawSource
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
