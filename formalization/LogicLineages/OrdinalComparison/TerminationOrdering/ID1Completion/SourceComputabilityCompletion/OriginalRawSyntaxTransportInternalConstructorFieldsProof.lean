module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-! Literal field selection from all eight original raw constructors. Every
metadata field is arbitrary object arithmetic, and numbered base, types and
extras retain their original distinct positions. -/

theorem variableTag {n : Nat} (query : Program n) (raw index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 0) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 1 0))) query raw (numeral 0) (Fin.cons index Fin.elim0) xs hc hq (constantValue 0 _)

theorem variableIndex {n : Nat} (query : Program n) (raw index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (query)) index xs)) :=
  pathValue (PairPath.right (PairPath.here (.projection 0))) query raw index (Fin.cons index Fin.elim0) xs hc hq (projectionValue 0 (Fin.cons index Fin.elim0))

theorem lambdaTag {n : Nat} (query : Program n) (raw domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 1) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 2 1))) query raw (numeral 1) (Fin.cons domain (Fin.cons child Fin.elim0)) xs hc hq (constantValue 1 _)

theorem lambdaDomain {n : Nat} (query : Program n) (raw domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (query))) domain xs)) :=
  pathValue (PairPath.right (PairPath.left (PairPath.here (.projection 0)))) query raw domain (Fin.cons domain (Fin.cons child Fin.elim0)) xs hc hq (projectionValue 0 (Fin.cons domain (Fin.cons child Fin.elim0)))

theorem lambdaBody {n : Nat} (query : Program n) (raw domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (query))) child xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.here (.projection 1)))) query raw child (Fin.cons domain (Fin.cons child Fin.elim0)) xs hc hq (projectionValue 1 (Fin.cons domain (Fin.cons child Fin.elim0)))

theorem applicationTag {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 2) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 3 2))) query raw (numeral 2) (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))) xs hc hq (constantValue 2 _)

theorem applicationDomain {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (query))) domain xs)) :=
  pathValue (PairPath.right (PairPath.left (PairPath.here (.projection 0)))) query raw domain (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))) xs hc hq (projectionValue 0 (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))

theorem applicationFunction {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (query)))) fn xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 1))))) query raw fn (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))) xs hc hq (projectionValue 1 (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))

theorem applicationArgument {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf (query)))) arg xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.here (.projection 2))))) query raw arg (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))) xs hc hq (projectionValue 2 (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))

theorem bottomTag {n : Nat} (query : Program n) (raw tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 3) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 1 3))) query raw (numeral 3) (Fin.cons tau Fin.elim0) xs hc hq (constantValue 3 _)

theorem bottomType {n : Nat} (query : Program n) (raw tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (query)) tau xs)) :=
  pathValue (PairPath.right (PairPath.here (.projection 0))) query raw tau (Fin.cons tau Fin.elim0) xs hc hq (projectionValue 0 (Fin.cons tau Fin.elim0))

theorem ordinaryTag {n : Nat} (query : Program n) (raw head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 4) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 2 4))) query raw (numeral 4) (Fin.cons head (Fin.cons base Fin.elim0)) xs hc hq (constantValue 4 _)

theorem ordinaryHead {n : Nat} (query : Program n) (raw head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (query))) head xs)) :=
  pathValue (PairPath.right (PairPath.left (PairPath.here (.projection 0)))) query raw head (Fin.cons head (Fin.cons base Fin.elim0)) xs hc hq (projectionValue 0 (Fin.cons head (Fin.cons base Fin.elim0)))

theorem ordinaryBase {n : Nat} (query : Program n) (raw head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (query))) base xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.here (.projection 1)))) query raw base (Fin.cons head (Fin.cons base Fin.elim0)) xs hc hq (projectionValue 1 (Fin.cons head (Fin.cons base Fin.elim0)))

theorem numberedTag {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 5) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 6 5))) query raw (numeral 5) (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (constantValue 5 _)

theorem numberedLabel {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (query))) label xs)) :=
  pathValue (PairPath.right (PairPath.left (PairPath.here (.projection 0)))) query raw label (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (projectionValue 0 (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))

theorem numberedHead {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (query)))) head xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 1))))) query raw head (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (projectionValue 1 (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))

theorem numberedType {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (rightOf (query))))) tau xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 2)))))) query raw tau (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (projectionValue 2 (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))

theorem numberedBase {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (rightOf (rightOf (query)))))) base xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 3))))))) query raw base (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (projectionValue 3 (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))

theorem numberedTypes {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (rightOf (rightOf (rightOf (query))))))) types xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 4)))))))) query raw types (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (projectionValue 4 (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))

theorem numberedExtras {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf (rightOf (rightOf (rightOf (query))))))) extras xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.right (PairPath.right (PairPath.right (PairPath.here (.projection 5)))))))) query raw extras (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))) xs hc hq (projectionValue 5 (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))

theorem nilTag {n : Nat} (query : Program n) (raw  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 6) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 0 6))) query raw (numeral 6) (Fin.elim0) xs hc hq (constantValue 6 _)

theorem nilPayload {n : Nat} (query : Program n) (raw  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (query)) (numeral 0) xs)) :=
  pathValue (PairPath.right (PairPath.here (constant 0 0))) query raw (numeral 0) (Fin.elim0) xs hc hq (constantValue 0 _)

theorem consTag {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (query)) (numeral 7) xs)) :=
  pathValue (PairPath.left (PairPath.here (constant 3 7))) query raw (numeral 7) (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))) xs hc hq (constantValue 7 _)

theorem consType {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (query))) tau xs)) :=
  pathValue (PairPath.right (PairPath.left (PairPath.here (.projection 0)))) query raw tau (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))) xs hc hq (projectionValue 0 (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))

theorem consHead {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (query)))) head xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 1))))) query raw head (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))) xs hc hq (projectionValue 1 (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))

theorem consTail {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf (query)))) tail xs)) :=
  pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.here (.projection 2))))) query raw tail (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))) xs hc hq (projectionValue 2 (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
