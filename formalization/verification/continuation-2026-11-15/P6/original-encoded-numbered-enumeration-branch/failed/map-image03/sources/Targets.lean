module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Literal original typed numbered branch. In particular heads use their ORIGINAL
Encodable instance, not a silently substituted map headNumber input. -/
def NativeBranch : Prop := ∀ (n : Nat) (labels : List Nat)
    (heads : List (NumberedAuxiliaryCoding.HeadCode (Fin n))) (types : List Source.Ty)
    (bases : List (NumberedAuxiliaryCoding.Code (Fin n))) (tuples : List (List Source.Ty))
    (extras : List (NumberedAuxiliaryCoding.Code (Fin n))),
  evaluate (branch n) (List.Vector.ofFn ![Encodable.encode labels,Encodable.encode heads,
    Encodable.encode types,Encodable.encode bases,Encodable.encode tuples,Encodable.encode extras]) =
  Encodable.encode (labels.flatMap (fun k => heads.flatMap (fun h => types.flatMap (fun t =>
    bases.flatMap (fun b => tuples.flatMap (fun ts => extras.map
      (fun e => NumberedAuxiliaryCoding.Code.numbered k h t b ts e)))))))

/-- Seven ordered witnesses: label, encoded head, raw head, result type, base,
type tuple, extras. The constructor consumes raw head; input membership uses
encoded head. Actual conversion connects the two, including malformed→raw0. -/
def fields {alpha : Type} (n : Nat)
    (labels heads types bases tuples extras code k encodedHead rawHead t b ts e : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) labels k ⊓ graph2 contains (numeral 1) heads encodedHead ⊓
  graph2 contains (numeral 1) types t ⊓ graph2 contains (numeral 1) bases b ⊓
  graph2 contains (numeral 1) tuples ts ⊓ graph2 contains (numeral 1) extras e ⊓
  graph1 (OriginalEncodedHeadConversion.convert n) rawHead encodedHead ⊓
  programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,rawHead,t,b,ts,e]

def witnessMatrix {alpha : Type} (n : Nat)
    (labels heads types bases tuples extras code : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  fields n (labels.relabel Sum.inl) (heads.relabel Sum.inl) (types.relabel Sum.inl)
    (bases.relabel Sum.inl) (tuples.relabel Sum.inl) (extras.relabel Sum.inl) (code.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
    (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))

/-- Constructive introduction from six actual input memberships and actual
conversion/constructor graphs. No native image, validity or injectivity premise. -/
def InternalIntroduction : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat)
    (labels heads types bases tuples extras out code k encodedHead rawHead t b ts e : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph (branch n) out ![labels,heads,types,bases,tuples,extras])) →
  Nonempty (Derivation body Delta (fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))

/-- Every actual output member internally has all seven original witnesses.
No supplied mapped-list image or converted-head witness is assumed. -/
def InternalElimination : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat)
    (labels heads types bases tuples extras out code : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph (branch n) out ![labels,heads,types,bases,tuples,extras])) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) →
  Nonempty (Derivation body Delta (InternalFiniteBlocks.block
    (witnessMatrix n labels heads types bases tuples extras code)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
