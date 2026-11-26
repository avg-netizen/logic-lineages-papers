module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual finite numeral Program is evaluated by graph composition and
successor introduction, not by native arithmetic reflection. -/
theorem constantValue {n : Nat} (value : Nat) (xs : Fin n → OTerm alpha) :
    Nonempty (Derivation body Delta (programGraph (constant n value) (numeral value) xs)) := by
  induction value with
  | zero => exact InternalLessThanSupportProof.zeroConstantValue xs
  | succ value ih =>
    exact unaryValue .succ (constant n value) (numeral (value + 1)) (numeral value) xs
      (successorValue (Fin.cons (numeral value) Fin.elim0)) ih

/-- Recover the literal original pair, with raw variable index unchanged. -/
theorem variableConstructorPair (raw i : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 variableConstructor raw i))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 0) i)) :=
  binaryRecover InternalPairing.pairing (constant 1 0) (.projection 0) raw (numeral 0) i
    (Fin.cons i Fin.elim0) h (constantValue 0 (Fin.cons i Fin.elim0))
    (projectionValue 0 (Fin.cons i Fin.elim0))

theorem variableConstructorValue (raw i : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 0) i))) :
    Nonempty (Derivation body Delta (graph1 variableConstructor raw i)) :=
  binaryValue InternalPairing.pairing (constant 1 0) (.projection 0) raw (numeral 0) i
    (Fin.cons i Fin.elim0) h (constantValue 0 (Fin.cons i Fin.elim0))
    (projectionValue 0 (Fin.cons i Fin.elim0))

theorem bottomConstructorPair (raw d : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 bottomConstructor raw d))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) d)) :=
  binaryRecover InternalPairing.pairing (constant 1 3) (.projection 0) raw (numeral 3) d
    (Fin.cons d Fin.elim0) h (constantValue 3 (Fin.cons d Fin.elim0))
    (projectionValue 0 (Fin.cons d Fin.elim0))

theorem bottomConstructorValue (raw d : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) d))) :
    Nonempty (Derivation body Delta (graph1 bottomConstructor raw d)) :=
  binaryValue InternalPairing.pairing (constant 1 3) (.projection 0) raw (numeral 3) d
    (Fin.cons d Fin.elim0) h (constantValue 3 (Fin.cons d Fin.elim0))
    (projectionValue 0 (Fin.cons d Fin.elim0))

theorem variableActionComponents (raw d k i : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 variableConstructor raw i))) :
    ∀ a : Fin 3, Nonempty (Derivation body Delta
      (programGraph ((![Program.projection 0,.projection 1,
        .composition variableConstructor (fun _ : Fin 1 => .projection 2)] : Fin 3 → Program 3) a)
        (![d,k,raw] a) (Fin.cons d (Fin.cons k (Fin.cons i Fin.elim0))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons i Fin.elim0))
  intro a
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (unaryValue variableConstructor (.projection 2) raw i xs h (projectionValue 2 xs))
      (fun q => Fin.elim0 q))) a

theorem variableActionForward (mode : Mode) (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation body Delta (graph3 (variableAction mode) out d k i))) :
    Nonempty (Derivation body Delta (graph3 (leaf mode) out d k raw)) :=
  compositionRecover (leaf mode) ![.projection 0,.projection 1,
    .composition variableConstructor (fun _ : Fin 1 => .projection 2)] out
    (Fin.cons d (Fin.cons k (Fin.cons i Fin.elim0)))
    (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))) ho
    (variableActionComponents raw d k i hr)

theorem variableActionBackward (mode : Mode) (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf mode) out d k raw))) :
    Nonempty (Derivation body Delta (graph3 (variableAction mode) out d k i)) :=
  compositionValue (leaf mode) ![.projection 0,.projection 1,
    .composition variableConstructor (fun _ : Fin 1 => .projection 2)] out
    (Fin.cons d (Fin.cons k (Fin.cons i Fin.elim0)))
    (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))) ho
    (variableActionComponents raw d k i hr)

/-- The constructor proves the zero tag and the exact index selector. -/
theorem variableLeafSelectors (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i))) :
    Nonempty (Derivation body Delta
      (graph3 (sameOf (leftOf (.projection 2)) (constant 3 0)) (numeral 1) d k raw)) ∧
    Nonempty (Derivation body Delta (graph3 (rightOf (.projection 2)) i d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hp := variableConstructorPair raw i hr
  have hl := unaryValue InternalUnpair.left (.projection 2) (numeral 0) raw xs
    (pairLeft raw (numeral 0) i hp) (projectionValue 2 xs)
  have hi := unaryValue InternalUnpair.right (.projection 2) i raw xs
    (pairRight raw (numeral 0) i hp) (projectionValue 2 xs)
  exact ⟨InternalApplicationStepPeelSupportProof.sameAccept
    (leftOf (.projection 2)) (constant 3 0) (numeral 0) xs hl (constantValue 0 xs),hi⟩

/-- Comparison is performed in the object arithmetic on that exact index. -/
theorem variableBelowValue (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess i k))) :
    Nonempty (Derivation body Delta (graph3
      (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
      (numeral 1) d k raw)) :=
  binaryValue InternalLessThan.ltTest (rightOf (.projection 2)) (.projection 1)
    (numeral 1) i k (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0)))
    (InternalLessThanSupportProof.acceptOfLess i k hlt)
    (variableLeafSelectors raw d k i hr).2
    (projectionValue 1 (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))))

theorem variableNotBelowValue (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess i k).not)) :
    Nonempty (Derivation body Delta (graph3
      (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
      (numeral 0) d k raw)) :=
  binaryValue InternalLessThan.ltTest (rightOf (.projection 2)) (.projection 1)
    (numeral 0) i k (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0)))
    (InternalLessThanSupportProof.rejectOfNotLess i k hlt)
    (variableLeafSelectors raw d k i hr).2
    (projectionValue 1 (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
