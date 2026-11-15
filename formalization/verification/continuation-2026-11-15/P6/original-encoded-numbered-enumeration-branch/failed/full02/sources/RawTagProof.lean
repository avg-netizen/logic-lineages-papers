module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atProduct (a b c d e f out code product : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![a,b,c,d,e,f])))
    (hp : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.product123456 product ![a,b,c,d,e,f])))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) code)) := by
  have hmap := ProductFrameProof.rawBranchRecover a b c d e f out product hp hv
  have hi := MapElimProof.recover OriginalNumberedEnumerationBranch.tagPayload product out code hmap hm
  apply MapImageEliminationProof.cases OriginalNumberedEnumerationBranch.tagPayload product code _ hi
  intro beta j Theta payload hj hmem htag
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  exact pairLeft (code.relabel j) (numeral 5) payload (TupleProof.tagRecover payload (code.relabel j) htag)

theorem tag (a b c d e f out code : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![a,b,c,d,e,f])))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) code)) := by
  apply programCases OriginalNumberedEnumerationBranch.product123456 ![a,b,c,d,e,f] _
  intro beta j Theta product hj hp
  have hx : (fun i => (![a,b,c,d,e,f] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hp
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [programRename] at hvj
  rw [hx] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact atProduct (a.relabel j) (b.relabel j) (c.relabel j) (d.relabel j) (e.relabel j) (f.relabel j)
    (out.relabel j) (code.relabel j) product hvj hp hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawTagProof
