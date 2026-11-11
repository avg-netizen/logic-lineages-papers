module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionTotalityProof InternalRecursionClosureProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Simultaneous symbolic witnesses for any finite family of the ORIGINAL
programs. Each witness is bound by original totality and existential elimination. -/
theorem programsCases {m n : Nat} (ps : Fin n → Program m)
    (xs : Fin m → OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin n → OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      (∀ i, Nonempty (Derivation body Theta
        (programGraph (ps i) (ys i) (fun a => (xs a).relabel j)))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  supplyOutputs body m n (fun i => OrdinaryArithmetic.graphFormula (ps i))
    (fun i => (actualOriginalPrograms body m (ps i)).1) alpha Delta xs psi step

/-- Reconstruct an arbitrary numeric pair from two selector graphs. The value
of the parent query is supplied internally when this is used by the parsers. -/
theorem selectorPair {n : Nat} (query : Program n) (raw left right : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hl : Nonempty (Derivation body Delta (programGraph (leftOf query) left xs)))
    (hr : Nonempty (Derivation body Delta (programGraph (rightOf query) right xs))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw left right)) :=
  reconstructPair raw left right
    (unaryRecover InternalUnpair.left query left raw xs hl hq)
    (unaryRecover InternalUnpair.right query right raw xs hr hq)

/-- A tag and one literal pair payload reconstruct the exact original unary AST. -/
theorem unaryConstructorValue (tag : Nat) (raw payload metadata child : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing raw (numeral tag) payload)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing payload metadata child))) :
    Nonempty (Derivation body Delta
      (graph2 (pairOf (constant 2 tag) (pairOf (.projection 0) (.projection 1)))
        raw metadata child)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons metadata (Fin.cons child Fin.elim0)
  exact binaryValue InternalPairing.pairing (constant 2 tag)
    (pairOf (.projection 0) (.projection 1)) raw (numeral tag) payload xs ht
    (constantValue tag xs)
    (binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
      payload metadata child xs hp (projectionValue 0 xs) (projectionValue 1 xs))

/-- The ordered first and second children stay distinct during reconstruction. -/
theorem binaryConstructorValue (tag : Nat)
    (raw payload children metadata first second : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing raw (numeral tag) payload)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing payload metadata children)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing children first second))) :
    Nonempty (Derivation body Delta
      (graph3 (pairOf (constant 3 tag)
        (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2))))
        raw metadata first second)) := by
  let xs : Fin 3 → OTerm alpha :=
    Fin.cons metadata (Fin.cons first (Fin.cons second Fin.elim0))
  exact binaryValue InternalPairing.pairing (constant 3 tag)
    (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2)))
    raw (numeral tag) payload xs ht (constantValue tag xs)
    (binaryValue InternalPairing.pairing (.projection 0)
      (pairOf (.projection 1) (.projection 2)) payload metadata children xs hp
      (projectionValue 0 xs)
      (binaryValue InternalPairing.pairing (.projection 1) (.projection 2)
        children first second xs hc (projectionValue 1 xs) (projectionValue 2 xs)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
