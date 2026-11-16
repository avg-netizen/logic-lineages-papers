module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original variable block, with its strict runtime variable bound. -/
def variableCase {alpha : Type} (variableBound code : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (InternalLessThan.strictLess (.var (.inr (0 : Fin 1))) (variableBound.relabel Sum.inl) ⊓
      graph1 OriginalRawSyntaxTransport.variableConstructor (code.relabel Sum.inl) (.var (.inr 0)))
/-- Lambda bodies use the separately supplied opened enumeration, never prior. -/
def lambdaCase {alpha : Type} (types opened code : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 contains (numeral 1) (types.relabel Sum.inl) (.var (.inr (0 : Fin 2))) ⊓
      graph2 contains (numeral 1) (opened.relabel Sum.inl) (.var (.inr (1 : Fin 2))) ⊓
      graph2 OriginalRawSyntaxTransport.lambdaConstructor (code.relabel Sum.inl)
        (.var (.inr 0)) (.var (.inr 1)))
/-- Both child positions retain membership in the same prior list. -/
def typedBinaryCase {alpha : Type} (constructor : Program 3)
    (types prior code : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 contains (numeral 1) (types.relabel Sum.inl) (.var (.inr (0 : Fin 3))) ⊓
      graph2 contains (numeral 1) (prior.relabel Sum.inl) (.var (.inr (1 : Fin 3))) ⊓
      graph2 contains (numeral 1) (prior.relabel Sum.inl) (.var (.inr (2 : Fin 3))) ⊓
      programGraph constructor (code.relabel Sum.inl) ![.var (.inr 0),.var (.inr 1),.var (.inr 2)])
def bottomCase {alpha : Type} (types code : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 contains (numeral 1) (types.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⊓
      graph1 OriginalRawSyntaxTransport.bottomConstructor (code.relabel Sum.inl) (.var (.inr 0)))
/-- Membership uses ORIGINAL encoded heads; constructors use the actual converted
raw head. The all-raw malformed-to-zero conversion behavior is retained. -/
def ordinaryCase {alpha : Type} (n : Nat) (heads prior code : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 contains (numeral 1) (heads.relabel Sum.inl) (.var (.inr (0 : Fin 3))) ⊓
      graph1 (OriginalEncodedHeadConversion.convert n) (.var (.inr (1 : Fin 3))) (.var (.inr 0)) ⊓
      graph2 contains (numeral 1) (prior.relabel Sum.inl) (.var (.inr (2 : Fin 3))) ⊓
      graph2 OriginalRawSyntaxTransport.ordinaryConstructor (code.relabel Sum.inl)
        (.var (.inr 1)) (.var (.inr 2)))
/-- Original numbered witnesses: label, encoded head, converted raw head, result
type, base, type list, extras, actual type-list length. All are bound internally.
Both base and extras use prior; type-list length and members are actual graphs
and object-language formulas, not native assertions or supplied membership. -/
def numberedCase {alpha : Type} (n : Nat)
    (labels heads types tupleBound prior code : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (InternalLessThan.strictLess (.var (.inr (0 : Fin 8))) (suc (labels.relabel Sum.inl)) ⊓
      graph2 contains (numeral 1) (heads.relabel Sum.inl) (.var (.inr (1 : Fin 8))) ⊓
      graph1 (OriginalEncodedHeadConversion.convert n) (.var (.inr (2 : Fin 8))) (.var (.inr 1)) ⊓
      graph2 contains (numeral 1) (types.relabel Sum.inl) (.var (.inr (3 : Fin 8))) ⊓
      graph2 contains (numeral 1) (prior.relabel Sum.inl) (.var (.inr (4 : Fin 8))) ⊓
      OriginalContextInsertion.lengthGraph (.var (.inr (7 : Fin 8))) (.var (.inr (5 : Fin 8))) ⊓
      InternalLessThan.strictLess (.var (.inr (7 : Fin 8))) (suc (tupleBound.relabel Sum.inl)) ⊓
      OriginalTypeListsMembership.Targets.allMembers (.var (.inr (5 : Fin 8))) (types.relabel Sum.inl) ⊓
      graph2 contains (numeral 1) (prior.relabel Sum.inl) (.var (.inr (6 : Fin 8))) ⊓
      programGraph OriginalRawSyntaxTransport.numberedConstructor (code.relabel Sum.inl)
        ![.var (.inr 0),.var (.inr 2),.var (.inr 3),.var (.inr 4),.var (.inr 5),.var (.inr 6)])
/-- Exact eight original constructor alternatives in source order. The input
order is types, encoded heads, labels, tuple bound, variable bound, prior, opened. -/
def alternatives {alpha : Type} (n : Nat) (xs : Fin 7 → OTerm alpha) (code : OTerm alpha) : Formula alpha :=
  variableCase (xs 4) code ⊔
    (lambdaCase (xs 0) (xs 6) code ⊔
    (typedBinaryCase OriginalRawSyntaxTransport.applicationConstructor (xs 0) (xs 5) code ⊔
    (bottomCase (xs 0) code ⊔
    (ordinaryCase n (xs 1) (xs 5) code ⊔
    (numberedCase n (xs 2) (xs 1) (xs 0) (xs 3) (xs 5) code ⊔
    (programGraph OriginalRawSyntaxTransport.nilConstructor code Fin.elim0 ⊔
      typedBinaryCase OriginalRawSyntaxTransport.consConstructor (xs 0) (xs 5) code))))))
/-- Full internal semantic one-layer characterization, not merely a disjunction
of opaque component memberships. Only the actual original layer graph is a
premise; component outputs, constructor arguments, head conversion, original
type-list length and all membership witnesses are internally discharged. -/
def InternalLayerFields : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n) out xs)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) ↔
   Nonempty (Derivation body Delta (alternatives n xs code)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
