module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Exact original numbered branch, including actual original HeadCode/Code/Ty
and nested List Ty Encodable instances. Labels may be any list; the original
layer instantiates List.range(labels+1), and shares prior in base/extras slots. -/
def NativeBranch : Prop := ∀ (n : Nat) (labels : List Nat)
    (heads : List (NumberedAuxiliaryCoding.HeadCode (Fin n))) (types : List Source.Ty)
    (bases : List (NumberedAuxiliaryCoding.Code (Fin n))) (tuples : List (List Source.Ty))
    (extras : List (NumberedAuxiliaryCoding.Code (Fin n))),
  evaluate branch (List.Vector.ofFn ![Encodable.encode labels,Encodable.encode heads,
    Encodable.encode types,Encodable.encode bases,Encodable.encode tuples,Encodable.encode extras]) =
  Encodable.encode (labels.flatMap (fun k => heads.flatMap (fun h => types.flatMap (fun t =>
    bases.flatMap (fun b => tuples.flatMap (fun ts => extras.map
      (fun e => NumberedAuxiliaryCoding.Code.numbered k h t b ts e)))))))
/-- Exact all-raw membership introduction AND elimination for the original
constructor graph. No native-image, validity, membership or list-distinctness
assumption. Both directions retain the same six ordered constructor fields. -/
def InternalMembership : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (labels heads types bases tuples extras out code k h t b ts e : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph branch out ![labels,heads,types,bases,tuples,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,h,t,b,ts,e])) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) ↔
   Nonempty (Derivation body Delta
    (graph2 contains (numeral 1) labels k ⊓ graph2 contains (numeral 1) heads h ⊓
     graph2 contains (numeral 1) types t ⊓ graph2 contains (numeral 1) bases b ⊓
     graph2 contains (numeral 1) tuples ts ⊓ graph2 contains (numeral 1) extras e)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.Targets
