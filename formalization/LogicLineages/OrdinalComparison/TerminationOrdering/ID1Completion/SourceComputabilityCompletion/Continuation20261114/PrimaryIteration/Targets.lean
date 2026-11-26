module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric
open TwoSol20261113.CalibratedPrimary.Membership

/-- Actual repeated expansion on all raw numeric list codes, retaining the
fixed pool, order and duplicates. No semantic correctness of E is asserted. -/
def IterationNative : Prop := ∀ (E : Program 3) (count pool reached parameter : Nat),
  evaluate (iterate E) (List.Vector.ofFn ![count,pool,reached,parameter]) =
    numbersNumber (((fun xs : List Nat => xs ++ (((decodeNumbers pool).getD []).filter
      (fun r => xs.any (fun a => decide (evaluate E (List.Vector.ofFn ![a,r,parameter]) = 1)))) )^[count])
        ((decodeNumbers reached).getD []))

/-- Literal ORIGINAL primaryList, singleton seed, actual vertices (including
repeats), and their LENGTH cutoff. Conditional only on the explicitly generic
native original-edge supplier; no pool selection or internal law is hidden. -/
def OriginalPrimaryCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Source.Ty) (E : Program 3) (parameter : Nat),
  (∀ a r : NumberedUniformPackedDecoding.RawPacked n,
    evaluate E (List.Vector.ofFn ![Encodable.encode a,Encodable.encode r,parameter]) =
      (NumberedExchangeCode.packedCodeExchange arity symbols S a r).toNat) →
  ∀ q : NumberedUniformPackedDecoding.RawPacked n,
    let pool := ContextUniformPrimary.vertices arity symbols S Gamma q
    evaluate (run E) (List.Vector.ofFn ![pool.length,entriesCode pool,Encodable.encode q,parameter]) =
      entriesCode (ContextUniformPrimary.primaryList arity symbols S Gamma q)

/-- Genuine object-arithmetic induction at arbitrary symbolic COUNT and all
runtime list outputs. No external-natural count or native calibration premise. -/
def InternalPreservation : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool reached parameter out needle : OTerm alpha),
  Nonempty (Derivation body Delta (graph4 (iterate E) out count pool reached parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached needle)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle))

/-- The unchanged singleton seed survives the ACTUAL run for arbitrary
symbolic count. No internal pool/exchange correctness or cutoff adequacy claimed. -/
def InternalSeedMembership : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool seed parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph4 (run E) out count pool seed parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out seed))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Targets
