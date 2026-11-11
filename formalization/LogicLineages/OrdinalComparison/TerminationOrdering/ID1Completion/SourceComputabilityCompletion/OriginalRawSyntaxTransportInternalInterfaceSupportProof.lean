module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Normalize public composition while the ternary Program remains symbolic,
so the complete traversal AST is never expanded by tuple conversion. -/
theorem zeroFirstComponents (k raw : OTerm alpha) :
    ∀ a : Fin 3, Nonempty (Derivation body Delta
      (programGraph ((![constant 2 0,Program.projection 0,.projection 1] : Fin 3 → Program 2) a)
        (![numeral 0,k,raw] a) (Fin.cons k (Fin.cons raw Fin.elim0)))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons k (Fin.cons raw Fin.elim0)
  intro a
  exact Fin.cases (constantValue 0 xs) (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (fun q => Fin.elim0 q))) a

theorem zeroFirstForward (p : Program 3) (out k raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph2 (.composition p ![constant 2 0,.projection 0,.projection 1]) out k raw))) :
    Nonempty (Derivation body Delta (graph3 p out (numeral 0) k raw)) :=
  compositionRecover p ![constant 2 0,.projection 0,.projection 1] out
    (Fin.cons k (Fin.cons raw Fin.elim0))
    (Fin.cons (numeral 0) (Fin.cons k (Fin.cons raw Fin.elim0))) h (zeroFirstComponents k raw)

theorem zeroFirstBackward (p : Program 3) (out k raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 p out (numeral 0) k raw))) :
    Nonempty (Derivation body Delta
      (graph2 (.composition p ![constant 2 0,.projection 0,.projection 1]) out k raw)) :=
  compositionValue p ![constant 2 0,.projection 0,.projection 1] out
    (Fin.cons k (Fin.cons raw Fin.elim0))
    (Fin.cons (numeral 0) (Fin.cons k (Fin.cons raw Fin.elim0))) h (zeroFirstComponents k raw)

theorem zeroTwoComponents (raw : OTerm alpha) :
    ∀ a : Fin 3, Nonempty (Derivation body Delta
      (programGraph ((![constant 1 0,constant 1 0,Program.projection 0] : Fin 3 → Program 1) a)
        (![numeral 0,numeral 0,raw] a) (Fin.cons raw Fin.elim0))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  intro a
  exact Fin.cases (constantValue 0 xs) (Fin.cases (constantValue 0 xs)
    (Fin.cases (projectionValue 0 xs) (fun q => Fin.elim0 q))) a

theorem zeroTwoForward (p : Program 3) (out raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph1 (.composition p ![constant 1 0,constant 1 0,.projection 0]) out raw))) :
    Nonempty (Derivation body Delta (graph3 p out (numeral 0) (numeral 0) raw)) :=
  compositionRecover p ![constant 1 0,constant 1 0,.projection 0] out
    (Fin.cons raw Fin.elim0)
    (Fin.cons (numeral 0) (Fin.cons (numeral 0) (Fin.cons raw Fin.elim0))) h (zeroTwoComponents raw)

theorem zeroTwoBackward (p : Program 3) (out raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 p out (numeral 0) (numeral 0) raw))) :
    Nonempty (Derivation body Delta
      (graph1 (.composition p ![constant 1 0,constant 1 0,.projection 0]) out raw)) :=
  compositionValue p ![constant 1 0,constant 1 0,.projection 0] out
    (Fin.cons raw Fin.elim0)
    (Fin.cons (numeral 0) (Fin.cons (numeral 0) (Fin.cons raw Fin.elim0))) h (zeroTwoComponents raw)

/-- Public shift selects zero for its unused erased-type argument. Full
parameter independence remains a separate machine theorem. -/
theorem shiftInterfaceZero (positive : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (out k raw : OTerm alpha) :
    Nonempty (Derivation positive Delta
      ((graph3 (fold .shift) out (numeral 0) k raw).iff (graph2 shiftRaw out k raw))) := by
  let A := graph3 (fold .shift) out (numeral 0) k raw
  let B := graph2 shiftRaw out k raw
  obtain ⟨hf⟩ := zeroFirstBackward (body := positive) (Delta := A :: Delta) (fold .shift) out k raw
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := zeroFirstForward (body := positive) (Delta := B :: Delta) (fold .shift) out k raw
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem rankInterfaceZero (positive : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (out raw : OTerm alpha) :
    Nonempty (Derivation positive Delta
      ((graph3 (fold .rank) out (numeral 0) (numeral 0) raw).iff (graph1 variableRankRaw out raw))) := by
  let A := graph3 (fold .rank) out (numeral 0) (numeral 0) raw
  let B := graph1 variableRankRaw out raw
  obtain ⟨hf⟩ := zeroTwoBackward (body := positive) (Delta := A :: Delta) (fold .rank) out raw
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := zeroTwoForward (body := positive) (Delta := B :: Delta) (fold .rank) out raw
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceSupportProof
