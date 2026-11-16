module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original typed depth, extended by zero on every decoder failure.
This is not a size bound and not merely an encoded-image calibration. -/
def NativeDepth : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (depth n) v = ((NumberedNumericDecoding.decodeCode n (v.get 0)).map
    NumberedAuxiliaryEnumeration.depth).getD 0

def invalidResult {alpha : Type} (n : Nat) (raw out : OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeValidityGuard.check n) (numeral 0) raw ⊓ eqn out (numeral 0)
def leafResult {alpha : Type} (n : Nat) (raw out : OTerm alpha) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ eqn out (numeral 1))
/-- Child depth is internally quantified; no external recursive-value supplier. -/
def unaryResult {alpha : Type} (n : Nat) (raw child out : OTerm alpha) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      InternalFiniteBlocks.block
        (graph1 (depth n) (.var (.inr (0 : Fin 1))) (child.relabel Sum.inl) ⊓
          eqn (out.relabel Sum.inl) (suc (.var (.inr 0)))))
/-- Both ordered child depths and their actual numeric maximum are internal. -/
def binaryResult {alpha : Type} (n : Nat) (raw left right out : OTerm alpha) : Formula alpha :=
  invalidResult n raw out ⊔
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      InternalFiniteBlocks.block
        (graph1 (depth n) (.var (.inr (0 : Fin 3))) (left.relabel Sum.inl) ⊓
          graph1 (depth n) (.var (.inr (1 : Fin 3))) (right.relabel Sum.inl) ⊓
          graph2 OriginalBoundsRecombination.maximum (.var (.inr (2 : Fin 3))) (.var (.inr 0)) (.var (.inr 1)) ⊓
          eqn (out.relabel Sum.inl) (suc (.var (.inr 2)))))

/-- Original variable constructor, including the explicit invalid-root branch. -/
def InternalVariable : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out index : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (leafResult n raw out)))

/-- Original lambda constructor, including the explicit invalid-root branch. -/
def InternalLambda : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out typ child : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw typ child)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (unaryResult n raw child out)))

/-- Original application constructor, including the explicit invalid-root branch. -/
def InternalApplication : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out typ left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw typ left right)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (binaryResult n raw left right out)))

/-- Original bottom constructor, including the explicit invalid-root branch. -/
def InternalBottom : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out typ : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw typ)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (leafResult n raw out)))

/-- Original ordinary constructor, including the explicit invalid-root branch. -/
def InternalOrdinary : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out head child : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (unaryResult n raw child out)))

/-- Original numbered constructor, including the explicit invalid-root branch. -/
def InternalNumbered : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out label head typ base types extra : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,base,types,extra])) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (binaryResult n raw base extra out)))

/-- Original nil constructor, including the explicit invalid-root branch. -/
def InternalNil : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out  : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (leafResult n raw out)))

/-- Original cons constructor, including the explicit invalid-root branch. -/
def InternalCons : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out typ left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ left right)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (binaryResult n raw left right out)))

/-- Arbitrary malformed raw codes, not restricted to one of the eight images. -/
def InternalMalformed : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 0) raw)) →
  (Nonempty (Derivation body Delta (graph1 (depth n) out raw)) ↔
   Nonempty (Derivation body Delta (eqn out (numeral 0))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
