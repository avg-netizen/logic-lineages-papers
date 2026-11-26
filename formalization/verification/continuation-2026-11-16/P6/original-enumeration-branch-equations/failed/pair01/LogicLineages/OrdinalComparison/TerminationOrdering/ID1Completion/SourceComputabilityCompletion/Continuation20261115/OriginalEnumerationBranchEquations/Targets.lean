module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
/-- The literal zero-fuel enumeration is the empty-list code, for arbitrary raw parameters. -/
def InternalZero : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (node param vb out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb z)) →
  (Nonempty (Derivation body Delta
    (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) ↔
   Nonempty (Derivation body Delta (eqn out z)))
/-- Both original child nodes and their values are internal witnesses, in prior/opened order.
No cache agreement, precomputed child outputs, or valid-code images are supplied. -/
def successorOutput {alpha : Type} (n : Nat)
    (out param vb f ts hs ls tb : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 InternalPairing.pairing (.var (.inr (0 : Fin 4)))
        (vb.relabel Sum.inl) (f.relabel Sum.inl) ⊓
      graph2 InternalPairing.pairing (.var (.inr (1 : Fin 4)))
        (suc (vb.relabel Sum.inl)) (f.relabel Sum.inl) ⊓
      graph2 (OriginalEnumerationRecursion.enumeration n) (.var (.inr (2 : Fin 4)))
        (.var (.inr (0 : Fin 4))) (param.relabel Sum.inl) ⊓
      graph2 (OriginalEnumerationRecursion.enumeration n) (.var (.inr (3 : Fin 4)))
        (.var (.inr (1 : Fin 4))) (param.relabel Sum.inl) ⊓
      programGraph (OriginalEnumerationConstructorLayer.layer n) (out.relabel Sum.inl)
        ![ts.relabel Sum.inl, hs.relabel Sum.inl, ls.relabel Sum.inl,
          tb.relabel Sum.inl, vb.relabel Sum.inl, .var (.inr 2), .var (.inr 3)])
/-- The original positive-fuel recurrence, with only observed node and parameter codecs. -/
def InternalSuccessor : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node param vb f ts hs ls tb p2 p3 out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)) →
  (Nonempty (Derivation body Delta
    (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) ↔
   Nonempty (Derivation body Delta (successorOutput n out param vb f ts hs ls tb)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Targets
