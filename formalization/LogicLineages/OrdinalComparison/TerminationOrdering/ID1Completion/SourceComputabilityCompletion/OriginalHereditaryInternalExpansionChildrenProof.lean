module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport (constant arityOf sameOf)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryExpansion
open InternalApplicationCertificateConstructorsSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalTagArithmeticSyntaxProof (z)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal arity-one branch inversion, without decoding or source premises. -/
theorem unaryRow (xs : Fin 2 → OTerm alpha) (jobs : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf (.projection 0)) (numeral 1) xs)))
 (hj : Nonempty (Derivation body Delta (programGraph childJobs jobs xs))) :
 Nonempty (Derivation body Delta (programGraph (OriginalHereditaryExpansion.consOf firstJob (constant 2 0)) jobs xs)) := by
 exact branchNumeralElim 1 1 (arityOf (.projection 0)) _ _ jobs xs ha hj

/-- Literal arity-two branch inversion; both raw child jobs remain present. -/
theorem binaryRow (xs : Fin 2 → OTerm alpha) (jobs : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf (.projection 0)) (numeral 2) xs)))
 (hj : Nonempty (Derivation body Delta (programGraph childJobs jobs xs))) :
 Nonempty (Derivation body Delta (programGraph
   (OriginalHereditaryExpansion.consOf firstJob (OriginalHereditaryExpansion.consOf secondJob (constant 2 0))) jobs xs)) := by
 have h := branchNumeralElim 2 1 (arityOf (.projection 0)) _ _ jobs xs ha hj
 exact branchNumeralElim 2 2 (arityOf (.projection 0)) _ _ jobs xs ha h

/-- Every other numeric arity takes the literal empty child row. -/
theorem otherRow (k : Nat) (h1 : k ≠ 1) (h2 : k ≠ 2)
 (xs : Fin 2 → OTerm alpha) (jobs : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf (.projection 0)) (numeral k) xs)))
 (hj : Nonempty (Derivation body Delta (programGraph childJobs jobs xs))) :
 Nonempty (Derivation body Delta (programGraph (constant 2 0) jobs xs)) := by
 have h := branchNumeralElim k 1 (arityOf (.projection 0)) _ _ jobs xs ha hj
 simp only [if_neg h1] at h
 have hh := branchNumeralElim k 2 (arityOf (.projection 0)) _ _ jobs xs ha h
 simpa only [if_neg h2] using hh

/-- The one-entry row is an actual numeric cons graph. -/
theorem unaryCons (xs : Fin 2 → OTerm alpha) (jobs first : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf (.projection 0)) (numeral 1) xs)))
 (hj : Nonempty (Derivation body Delta (programGraph childJobs jobs xs)))
 (hf : Nonempty (Derivation body Delta (programGraph firstJob first xs))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs first z)) :=
 binaryRecover InternalListCodec.consCode firstJob (constant 2 0) jobs first z xs
   (unaryRow xs jobs ha hj) hf (constantValue 0 xs)

/-- Given the genuine second singleton, recover the first cons without
assuming anything about the child row's source semantics. -/
theorem binaryCons (xs : Fin 2 → OTerm alpha) (jobs first second tail : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf (.projection 0)) (numeral 2) xs)))
 (hj : Nonempty (Derivation body Delta (programGraph childJobs jobs xs)))
 (hf : Nonempty (Derivation body Delta (programGraph firstJob first xs)))
 (hs : Nonempty (Derivation body Delta (programGraph secondJob second xs)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs first tail)) := by
 have htail : Nonempty (Derivation body Delta
   (programGraph (OriginalHereditaryExpansion.consOf secondJob (constant 2 0)) tail xs)) :=
   binaryValue InternalListCodec.consCode secondJob (constant 2 0) tail second z xs
     ht hs (constantValue 0 xs)
 exact binaryRecover InternalListCodec.consCode firstJob (OriginalHereditaryExpansion.consOf secondJob (constant 2 0))
   jobs first tail xs (binaryRow xs jobs ha hj) hf htail

/-- Only literal lambda tag one extends the first child's context. -/
theorem firstParameterAtTag (k : Nat) (xs : Fin 2 → OTerm alpha) (out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 0)) (numeral k) xs)))
 (hp : Nonempty (Derivation body Delta (programGraph firstParameter out xs))) :
 Nonempty (Derivation body Delta (programGraph
   (if k = 1 then pairOf (leftOf (.projection 1))
       (OriginalHereditaryExpansion.consOf (leftOf (rightOf (.projection 0))) (rightOf (.projection 1)))
    else .projection 1) out xs)) :=
 branchNumeralElim k 1 (leftOf (.projection 0)) _ _ out xs ht hp

theorem firstParameterSameValue (k : Nat) (hk : k ≠ 1) (xs : Fin 2 → OTerm alpha) (out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 0)) (numeral k) xs)))
 (hp : Nonempty (Derivation body Delta (programGraph (.projection 1) out xs))) :
 Nonempty (Derivation body Delta (programGraph firstParameter out xs)) := by
 apply branchNumeralIntro k 1 (leftOf (.projection 0)) _ _ out xs ht
 simpa only [if_neg hk] using hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
