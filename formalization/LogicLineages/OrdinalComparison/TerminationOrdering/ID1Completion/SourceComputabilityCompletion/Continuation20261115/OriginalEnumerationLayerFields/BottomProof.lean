module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem mapAt (xs : Fin 7 → OTerm alpha) (out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.bottoms out xs))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalRawSyntaxTransport.bottomConstructor) out (xs 0))) :=
  unaryRecover (InternalListMap.map OriginalRawSyntaxTransport.bottomConstructor) (.projection 0)
    out (xs 0) xs (by
      have he : (fun _ : Fin 1 => (ComputabilityKnowledge.GorbowPRProgram.Program.projection 0 : ComputabilityKnowledge.GorbowPRProgram.Program 7)) = ![.projection 0] := by
        funext i
        fin_cases i
        rfl
      rw [he]
      exact hg) (projectionValue 0 xs)

theorem forward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.bottoms out xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.bottomCase (xs 0) code)) := by
  have hi := MapElimProof.recover OriginalRawSyntaxTransport.bottomConstructor (xs 0) out code (mapAt xs out hg) hm
  apply MapImageEliminationProof.cases OriginalRawSyntaxTransport.bottomConstructor (xs 0) code _ hi
  intro beta j Theta t hj hmem hctor
  rw [BottomSyntaxProof.caseRename]
  exact BottomSyntaxProof.introduce ((xs 0).relabel j) (code.relabel j) ![t] (andIntro hmem hctor)

theorem backward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.bottoms out xs)))
    (hw : Nonempty (Derivation body Delta (Targets.bottomCase (xs 0) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have hmap := mapAt xs out hg
  apply BottomSyntaxProof.cases (xs 0) code _ hw
  intro beta j Theta ys hj hf
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hmap j Theta hj
  rw [graph1Rename] at hgj
  exact MapIntroProof.introduce OriginalRawSyntaxTransport.bottomConstructor
    ((xs 0).relabel j) z (out.relabel j) (code.relabel j) z (ys 0) hgj (andLeft hf) (andRight hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomProof
