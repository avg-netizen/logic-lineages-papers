module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115
/-- No fresh bounds AST: every child observation uses the actual existing bounds. -/
def invalidResult {alpha : Type} (n : Nat) (raw out : OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeValidityGuard.check n) (numeral 0) raw ⊓ eqn out (numeral 0)
def leafResult {alpha : Type} (n : Nat) (raw out : OTerm alpha) (size : Nat) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      graph2 InternalPairing.pairing out (numeral size) (numeral 0))
def unaryResult {alpha : Type} (n : Nat) (raw child out : OTerm alpha) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      InternalFiniteBlocks.block
        (graph1 (OriginalCodeBoundsRecursion.bounds n) (.var (.inr (0 : Fin 3))) (child.relabel Sum.inl) ⊓
         graph2 InternalPairing.pairing (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
         graph2 InternalPairing.pairing (out.relabel Sum.inl) (suc (.var (.inr 1))) (.var (.inr 2))))
/-- Fin7 witnesses: left pair,size,label; right pair,size,label; maximum label.
Only actual cons omits the term constructor's +1 size contribution. -/
def binaryResult {alpha : Type} (n : Nat) (cons : Bool) (raw left right out : OTerm alpha) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      InternalFiniteBlocks.block
        (graph1 (OriginalCodeBoundsRecursion.bounds n) (.var (.inr (0 : Fin 7))) (left.relabel Sum.inl) ⊓
         graph2 InternalPairing.pairing (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
         graph1 (OriginalCodeBoundsRecursion.bounds n) (.var (.inr 3)) (right.relabel Sum.inl) ⊓
         graph2 InternalPairing.pairing (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) ⊓
         graph2 OriginalBoundsRecombination.maximum (.var (.inr 6)) (.var (.inr 2)) (.var (.inr 5)) ⊓
         graph2 InternalPairing.pairing (out.relabel Sum.inl)
           (if cons then OrdinaryArithmetic.addTerm (.var (.inr 1)) (.var (.inr 4))
            else suc (OrdinaryArithmetic.addTerm (.var (.inr 1)) (.var (.inr 4)))) (.var (.inr 6))))
/-- Fin8 adds the actual maximum of the root label and both ordered child labels. -/
def numberedResult {alpha : Type} (n : Nat) (raw label base extra out : OTerm alpha) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      InternalFiniteBlocks.block
        (graph1 (OriginalCodeBoundsRecursion.bounds n) (.var (.inr (0 : Fin 8))) (base.relabel Sum.inl) ⊓
         graph2 InternalPairing.pairing (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
         graph1 (OriginalCodeBoundsRecursion.bounds n) (.var (.inr 3)) (extra.relabel Sum.inl) ⊓
         graph2 InternalPairing.pairing (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) ⊓
         graph2 OriginalBoundsRecombination.maximum (.var (.inr 6)) (.var (.inr 2)) (.var (.inr 5)) ⊓
         graph2 OriginalBoundsRecombination.maximum (.var (.inr 7)) (label.relabel Sum.inl) (.var (.inr 6)) ⊓
         graph2 InternalPairing.pairing (out.relabel Sum.inl)
           (suc (OrdinaryArithmetic.addTerm (.var (.inr 1)) (.var (.inr 4)))) (.var (.inr 7))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors
