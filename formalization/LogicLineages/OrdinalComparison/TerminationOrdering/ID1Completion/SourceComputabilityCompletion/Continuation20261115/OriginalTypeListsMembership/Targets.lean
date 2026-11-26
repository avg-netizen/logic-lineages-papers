module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Every actual entry of the original inner raw list belongs to the original
allowed-type list. Quantification and membership are internal, not native. -/
def memberMatrix {alpha : Type} (types allowed : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph2 contains (numeral 1) (types.relabel Sum.inl) (.var (.inr 0))).imp
    (graph2 contains (numeral 1) (allowed.relabel Sum.inl) (.var (.inr 0)))
def allMembers {alpha : Type} (types allowed : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (memberMatrix types allowed)
/-- Full all-raw internal membership characterization of the ORIGINAL typeLists
program. The actual length observation is the existing raw-list length program.
The strict successor bound is precisely length≤bound. Empty lists, repetitions,
zero codes and arbitrary allowed lists are included. No decoded-image hypothesis,
external membership equivalence, or caller-provided enumeration induction is used. -/
def InternalMembership : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (bound allowed out types len : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 OriginalTypeListsEnumeration.enumeration out bound allowed)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out types)) ↔
   Nonempty (Derivation body Delta
    (InternalLessThan.strictLess len (suc bound) ⊓ allMembers types allowed)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.Targets
