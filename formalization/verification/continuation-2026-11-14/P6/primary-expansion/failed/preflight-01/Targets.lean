module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric
open TwoSol20261113.CalibratedPrimary.Membership

/-- Generic numeric AST calibration; no original exchange-correctness claim. -/
def AnyNative : Prop := ∀ (E : Program 3) (reached input parameter : Nat),
  evaluate (anyEdge E) (List.Vector.ofFn ![reached,input,parameter]) =
    (((decodeNumbers reached).getD []).any
      (fun a => decide (evaluate E (List.Vector.ofFn ![a,input,parameter]) = 1))).toNat

def FilterNative : Prop := ∀ (E : Program 3) (pool reached parameter : Nat),
  evaluate (filterReached E) (List.Vector.ofFn ![pool,reached,parameter]) =
    numbersNumber (((decodeNumbers pool).getD []).filter (fun r =>
      ((decodeNumbers reached).getD []).any
        (fun a => decide (evaluate E (List.Vector.ofFn ![a,r,parameter]) = 1))))

def ExpansionNative : Prop := ∀ (E : Program 3) (pool reached parameter : Nat),
  evaluate (expand E) (List.Vector.ofFn ![pool,reached,parameter]) =
    numbersNumber (((decodeNumbers reached).getD []) ++
      (((decodeNumbers pool).getD []).filter (fun r =>
        ((decodeNumbers reached).getD []).any
          (fun a => decide (evaluate E (List.Vector.ofFn ![a,r,parameter]) = 1)))))

/-- Exact bridge to ORIGINAL step, conditional only on a plainly generic native
edge supplier. This does NOT assert existence or internal correctness of E. -/
def OriginalStepCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Source.Ty)
    (E : Program 3) (parameter : Nat),
  (∀ a r : NumberedUniformPackedDecoding.RawPacked n,
    evaluate E (List.Vector.ofFn ![Encodable.encode a,Encodable.encode r,parameter]) =
      (NumberedExchangeCode.packedCodeExchange arity symbols S a r).toNat) →
  ∀ pool reached : List (NumberedUniformPackedDecoding.RawPacked n),
    evaluate (expand E) (List.Vector.ofFn ![entriesCode pool,entriesCode reached,parameter]) =
      entriesCode (ContextUniformPrimary.step arity symbols S pool reached)

/-- Independent INTERNAL preservation at arbitrary runtime lists and edge AST.
Actual old membership survives actual expansion; no native calibration or
exchange correctness occurs among the premises. -/
def InternalPreservation : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (pool reached parameter out needle : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (expand E) out pool reached parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached needle)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Targets
