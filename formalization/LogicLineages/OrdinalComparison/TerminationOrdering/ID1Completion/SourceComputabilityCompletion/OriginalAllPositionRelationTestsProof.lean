module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationTestsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (sameAccept)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalContextInsertion
open OriginalClassContextAllPositionInternalProof (scanHit)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem testsFromScan (R : Program 2) (seed candidate parameter gamma count : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
 (hh : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed candidate parameter))) :
 Nonempty (Derivation body Delta (graph3 (allTests R) (suc z) seed candidate parameter)) := by
 let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
 have hright := unaryValue InternalUnpair.right (.projection 2) gamma parameter xs hg (projectionValue 2 xs)
 have hcount := unaryValue length (rightOf (.projection 2)) count gamma xs hl hright
 apply compositionValue (scan R)
   ![.composition length (fun _ : Fin 1 => rightOf (.projection 2)),.projection 0,.projection 1,.projection 2]
   (suc z) xs (Fin.cons count xs) hh
 intro i
 exact Fin.cases hcount (Fin.cases (projectionValue 0 xs)
   (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k)))) i

theorem allTestsRow (R : Program 2) (seed other candidate parameter : OTerm alpha)
 (hit : Nonempty (Derivation body Delta (graph3 (allTests R) (suc z) seed other parameter))) :
 Nonempty (Derivation body Delta ((graph3 (allTests R) (suc z) seed candidate parameter).iff
   (graph3 (allTests R) (suc z) other candidate parameter))) := by
 apply programCases InternalUnpair.right (Fin.cons parameter Fin.elim0) _
 intro beta j Theta gamma hj hg
 apply programCases length (Fin.cons gamma Fin.elim0) _
 intro beta' k Xi count hk hl
 simp only [OriginalTypedDecoderTransportLogicalProof.iffRename,graph3Rename,sucRelabel,zRelabel]
 have hit := renameInto (renameInto hit j Theta hj) k Xi hk
 simp only [graph3Rename,sucRelabel,zRelabel] at hit
 have hg := renameInto hg k Xi hk
 simp only [programRename,consTermRename,emptyRename] at hg
 simp only [consTermRename,emptyRename] at hl
 let s := (seed.relabel j).relabel k
 let o := (other.relabel j).relabel k
 let c := (candidate.relabel j).relabel k
 let p := (parameter.relabel j).relabel k
 have row := OriginalAllPositionRelationScanProof.scanRow R count s o c p (scanHit R s o p (gamma.relabel k) count hg hl hit)
 let A := graph3 (allTests R) (suc z) s c p
 let B := graph3 (allTests R) (suc z) o c p
 have forward : Nonempty (Derivation body (A :: Xi) B) := by
   have sc := scanHit R s c p (gamma.relabel k) count (withHyp hg A) (withHyp hl A)
     (show Nonempty (Derivation body (A :: Xi) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact testsFromScan R o c p (gamma.relabel k) count (withHyp hg A) (withHyp hl A) (iffForward (withHyp row A) sc)
 have backward : Nonempty (Derivation body (B :: Xi) A) := by
   have oc := scanHit R o c p (gamma.relabel k) count (withHyp hg B) (withHyp hl B)
     (show Nonempty (Derivation body (B :: Xi) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact testsFromScan R s c p (gamma.relabel k) count (withHyp hg B) (withHyp hl B) (iffBackward (withHyp row B) oc)
 obtain ⟨hf⟩ := forward
 obtain ⟨hb⟩ := backward
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem allTestsRefl (R : Program 2) (seed parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (graph3 (allTests R) (suc z) seed seed parameter)) := by
 apply programCases InternalUnpair.right (Fin.cons parameter Fin.elim0) _
 intro beta j Theta gamma hj hg
 apply programCases length (Fin.cons gamma Fin.elim0) _
 intro beta' k Xi count hk hl
 simp only [graph3Rename,sucRelabel,zRelabel]
 have hg := renameInto hg k Xi hk
 simp only [programRename,consTermRename,emptyRename] at hg
 simp only [consTermRename,emptyRename] at hl
 exact testsFromScan R ((seed.relabel j).relabel k) ((seed.relabel j).relabel k)
   ((parameter.relabel j).relabel k) (gamma.relabel k) count hg hl
   (OriginalAllPositionRelationReflexiveProof.scanRefl R count ((seed.relabel j).relabel k) ((parameter.relabel j).relabel k))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationTestsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationTestsProof
