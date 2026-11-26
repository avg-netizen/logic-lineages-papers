module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

/-- Exact all-output zero-list graph, not merely acceptance rejection. -/
def NilGraph : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (out needle : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 contains out (numeral 0) needle)) ↔
  Nonempty (Derivation body Delta (equal out (numeral 0)))

/-- Exact cons recursion in a genuine different-head branch. The original
list-code graph and symbolic inequality are retained, and output is arbitrary. -/
def MissGraph : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (code head tail needle out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
  Nonempty (Derivation body Delta (equal head needle).not) →
  (Nonempty (Derivation body Delta (graph2 contains out code needle)) ↔
   Nonempty (Derivation body Delta (graph2 contains out tail needle)))

/-- The same exact class AST accepts iff the original target and actual
membership accept, at outputs obtained from the actual L/D subprograms.
No native calibration is an internal premise and no decoder law is asserted. -/
def ClassFactor : Prop := ∀ (T L D : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter list needle : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 L list seed parameter)) →
  Nonempty (Derivation body Delta (graph2 D needle candidate parameter)) →
  (Nonempty (Derivation body Delta
      (graph3 (classTest T L D) (numeral 1) seed candidate parameter)) ↔
   Nonempty (Derivation body Delta
      (graph2 T (numeral 1) candidate parameter ⊓
       graph2 contains (numeral 1) list needle)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Targets
