module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafDepthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafMeaningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variableCode (n : Nat) (raw bound fuel types heads labels tupleBound index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓ (InternalLessThan.strictLess index bound)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalVariable n body alpha Delta raw bound types heads labels tupleBound index hc
  constructor
  · intro h
    exact he.mp (andLeft h)
  · intro h
    exact andIntro (he.mpr h) (LeafDepthProof.variableCode n raw index fuel (andLeft h) hc)

theorem bottom (n : Nat) (raw bound fuel types heads labels tupleBound typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓ (graph2 contains (numeral 1) types typ)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalBottom n body alpha Delta raw bound types heads labels tupleBound typ hc
  constructor
  · intro h
    exact he.mp (andLeft h)
  · intro h
    exact andIntro (he.mpr h) (LeafDepthProof.bottom n raw typ fuel (andLeft h) hc)

theorem nil (n : Nat) (raw bound fuel types heads labels tupleBound : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalNil n body alpha Delta raw bound types heads labels tupleBound hc
  constructor
  · intro h
    exact he.mp (andLeft h)
  · intro h
    exact andIntro (he.mpr h) (LeafDepthProof.nil n raw fuel h hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafMeaningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafMeaningProof
