module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadClassValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadIdentityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (refl symm cancelSuc sucNeZeroApply)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atTarget (f g symbol tag payload : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f (numeral 5) symbol)))
    (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing g tag payload)))
    (hv : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass (suc (suc symbol)) g))) :
    Nonempty (Derivation body Delta (eqn f g)) := by
  apply formulaCases (eqn tag (numeral 4))
  · obtain ⟨hbad⟩ := HeadClassValueProof.applicationValue g tag payload (suc (suc symbol))
      (withHyp hg _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
    exact ⟨Derivation.explosion (sucNeZeroApply (cancelSuc hbad))⟩
  · let A := (eqn tag (numeral 4)).not
    have h4 : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply formulaCases (eqn tag (numeral 5))
    · let B := eqn tag (numeral 5)
      have h5 : Nonempty (Derivation body (B :: A :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hgp := headTransport InternalPairing.pairing g tag (numeral 5) ![payload] h5 (withHyp (withHyp hg A) B)
      have hgv := HeadClassValueProof.rankedValue g payload hgp
      obtain ⟨he⟩ := valueUnique OriginalHeadClass.headClass (suc (suc symbol)) (suc (suc payload)) ![g]
        (withHyp (withHyp hv A) B) hgv
      have he' : Nonempty (Derivation body (B :: A :: Delta) (eqn symbol payload)) := ⟨cancelSuc (cancelSuc he)⟩
      have hfp := withHyp (withHyp hf A) B
      have hfr := outputTransport InternalUnpair.right symbol payload ![f] he' (pairRight f (numeral 5) symbol hfp)
      have hfp' := reconstructPair f (numeral 5) payload (pairLeft f (numeral 5) symbol hfp) hfr
      exact valueUnique InternalPairing.pairing f g ![numeral 5,payload] hfp' hgp
    · obtain ⟨hbad⟩ := HeadClassValueProof.otherValue g tag payload (suc (suc symbol))
        (withHyp (withHyp hg A) _) (withHyp h4 _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp (withHyp hv A) _)
      exact ⟨Derivation.explosion (sucNeZeroApply hbad)⟩

def queries : Fin 4 → Program 2 :=
  ![.composition InternalUnpair.right (fun _ => .projection 0),
    .composition InternalUnpair.left (fun _ => .projection 1),
    .composition InternalUnpair.right (fun _ => .projection 1),
    .composition OriginalHeadClass.headClass (fun _ => .projection 1)]

theorem rankedEqual (f g : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 5) f)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (suc z) f g))) :
    Nonempty (Derivation body Delta (eqn f g)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![f,g] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![f,g] i).relabel j) = ![f.relabel j,g.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  let xs := ![f.relabel j,g.relabel j]
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (f.relabel j) xs (hq 0) (projectionValue 0 xs)
  have hgl := unaryRecover InternalUnpair.left (.projection 1) (ys 1) (g.relabel j) xs (hq 1) (projectionValue 1 xs)
  have hgr := unaryRecover InternalUnpair.right (.projection 1) (ys 2) (g.relabel j) xs (hq 2) (projectionValue 1 xs)
  have hgv := unaryRecover OriginalHeadClass.headClass (.projection 1) (ys 3) (g.relabel j) xs (hq 3) (projectionValue 1 xs)
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at he'
  have hfp := reconstructPair (f.relabel j) (numeral 5) (ys 0) ht' hfr
  have hgp := reconstructPair (g.relabel j) (ys 1) (ys 2) hgl hgr
  have hfv := HeadClassValueProof.rankedValue (f.relabel j) (ys 0) hfp
  obtain ⟨heq⟩ := (OriginalHeadClass.InternalProof.internalEquivalence body beta Theta
    (f.relabel j) (g.relabel j) (suc (suc (ys 0))) (ys 3) hfv hgv).mp he'
  have hgv' := outputTransport OriginalHeadClass.headClass (ys 3) (suc (suc (ys 0))) ![g.relabel j] ⟨symm heq⟩ hgv
  exact atTarget (f.relabel j) (g.relabel j) (ys 0) (ys 1) (ys 2) hfp hgp hgv'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadIdentityProof
