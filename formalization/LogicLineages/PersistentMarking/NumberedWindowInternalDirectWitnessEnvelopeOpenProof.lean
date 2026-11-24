module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelope
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalDirectWitnessEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode readNode)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open SourceComputabilityFormulaSupportProof (numeral)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem canonicalReports (tag : Nat) (a b c : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (reports tag (tripleTerm tag a b c) a b c)) := by
  let n := tripleTerm tag a b c
  have report : Nonempty (Derivation B Γ (unary (guardAt tag) (suc z) n)) ∧
      Reports B Γ n cellTail [a,b,c] :=
    packedNode (literal 1 tag) (numeral tag) [a,b,c] (literalGraph tag ![n])
  obtain ⟨g⟩ := report.1
  obtain ⟨h₀⟩ := report.2.1
  obtain ⟨h₁⟩ := report.2.2.1
  obtain ⟨h₂⟩ := report.2.2.2.1
  exact ⟨Derivation.conjunctionIntroduction g
    (Derivation.conjunctionIntroduction h₀ (Derivation.conjunctionIntroduction h₁ h₂))⟩

private theorem reportsRead (tag : Nat) (w a b c : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (reports tag w a b c))) :
    Nonempty (Derivation B Γ (eqn w (tripleTerm tag a b c))) := by
  obtain ⟨p⟩ := h
  have gs := Derivation.conjunctionLeft p
  have h₀₁₂ := Derivation.conjunctionRight p
  have h₁₂ := Derivation.conjunctionRight h₀₁₂
  have fs : Reports B Γ w cellTail [a,b,c] :=
    ⟨⟨Derivation.conjunctionLeft h₀₁₂⟩,⟨Derivation.conjunctionLeft h₁₂⟩,
      ⟨Derivation.conjunctionRight h₁₂⟩,trivial⟩
  exact readNode (literal 1 tag) w (numeral tag) [a,b,c]
    (literalGraph tag ![w]) ⟨gs⟩ fs

private theorem reportsTransport (tag : Nat) (w q a b c : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (eqn w q)))
    (facts : Nonempty (Derivation B Γ (reports tag w a b c))) :
    Nonempty (Derivation B Γ (reports tag q a b c)) := by
  obtain ⟨p⟩ := facts
  have tails := Derivation.conjunctionRight p
  have last := Derivation.conjunctionRight tails
  obtain ⟨g⟩ := moveUnary (guardAt tag) (suc z) w q h ⟨Derivation.conjunctionLeft p⟩
  obtain ⟨h₀⟩ := moveUnary (field 0) a w q h ⟨Derivation.conjunctionLeft tails⟩
  obtain ⟨h₁⟩ := moveUnary (field 1) b w q h ⟨Derivation.conjunctionLeft last⟩
  obtain ⟨h₂⟩ := moveUnary (field 2) c w q h ⟨Derivation.conjunctionRight last⟩
  exact ⟨Derivation.conjunctionIntroduction g
    (Derivation.conjunctionIntroduction h₀ (Derivation.conjunctionIntroduction h₁ h₂))⟩

theorem exactOpenTriple : ExactOpenTriple := by
  intro B α Γ tag w a b c
  dsimp only
  rw [equalEqn]
  let e := eqn w (tripleTerm tag a b c)
  let g := reports tag w a b c
  have he : Derivation B (e :: Γ) e := Derivation.hypothesis List.mem_cons_self
  have hg : Derivation B (g :: Γ) g := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forw⟩ := reportsTransport tag (tripleTerm tag a b c) w a b c
    ⟨symm he⟩ (canonicalReports tag a b c)
  obtain ⟨back⟩ := reportsRead tag w a b c ⟨hg⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forw)
    (Derivation.implicationIntroduction back)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelope
