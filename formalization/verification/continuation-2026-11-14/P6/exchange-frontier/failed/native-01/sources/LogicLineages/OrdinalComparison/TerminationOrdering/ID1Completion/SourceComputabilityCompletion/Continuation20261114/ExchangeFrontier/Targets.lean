module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)
def NativeFlatten : Prop := ∀ (D : Program 2) (d : Nat → Nat → List Nat),
  (∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (d node param)) →
  ∀ (nodes : List Nat) (param : Nat),
    evaluate (flatten D) (List.Vector.ofFn ![numbersNumber nodes,param]) =
      numbersNumber (nodes.flatMap (fun node => d node param))
def NativeBindList : Prop := ∀ (D : Program 2) (d : Nat → Nat → List Nat),
  (∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (d node param)) →
  ∀ (depth seed param : Nat),
    evaluate (bindList D) (List.Vector.ofFn ![depth,seed,param]) =
      numbersNumber (Nat.rec [seed] (fun _ nodes => nodes.flatMap (fun node => d node param)) depth)
/-- Genuine original source-rank bound and exhaustion. This native fact does not
supply internal rank correctness for an opaque selected dependency program. -/
def OriginalRankExhaustion : Prop := ∀ (n : Nat)
    (source target : NumberedAuxiliaryCoding.Code (Fin n)),
  (∀ (depth : Nat) (x y : NumberedAuxiliaryCoding.Code (Fin n)),
    (x,y) ∈ originalFrontier source target depth →
    NumberedLeastCodeRepresentative.codeNumber x + depth ≤ NumberedLeastCodeRepresentative.codeNumber source) ∧
  originalFrontier source target (NumberedLeastCodeRepresentative.codeNumber source + 1) = []
def InternalFlattenCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2)
    (nodes node tail param deps rest out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes node tail)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 (flatten D) rest tail param)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out deps rest)) →
  Nonempty (Derivation body Delta (graph2 (flatten D) out nodes param))
def InternalBindSuccessor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2)
    (depth seed param previous out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (bindList D) previous depth seed param)) →
  (Nonempty (Derivation body Delta (graph3 (bindList D) out (suc depth) seed param)) ↔
   Nonempty (Derivation body Delta (graph2 (flatten D) out previous param)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Targets
