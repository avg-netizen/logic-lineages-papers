module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParserSupportProof
open OriginalTypedDecoderTransport
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Supply both literal extended contexts, the transformed child, and the
original requested arrow fields. All are actual program-totality witnesses. -/
theorem lambdaWitnesses (erasing : Bool)
    (domain gamma extended d cutoff child typ : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (childGamma childExtended childOut requestedDomain codomain : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepCons childGamma (domain.relabel j) (gamma.relabel j))) →
      Nonempty (Derivation body Theta (StepCons childExtended (domain.relabel j) (extended.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) childOut (d.relabel j)
          (suc (cutoff.relabel j)) (child.relabel j))) →
      Nonempty (Derivation body Theta (StepArrowFields (typ.relabel j) requestedDomain codomain)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 5 → Program 7 :=
    ![.composition InternalListCodec.consCode ![.projection 0,.projection 1],
      .composition InternalListCodec.consCode ![.projection 0,.projection 2],
      .composition (fold (selectedMode erasing)) ![.projection 3,succOf (.projection 4),.projection 5],
      OriginalTypedDecoder.headOf (.projection 6),OriginalTypedDecoder.tailOf (.projection 6)]
  let inputs : Fin 7 → OTerm alpha := ![domain,gamma,extended,d,cutoff,child,typ]
  apply programsCases ps inputs psi
  intro beta j Theta ys hj hs
  let xs : Fin 7 → OTerm beta := fun i => (inputs i).relabel j
  have hg := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 0) (domain.relabel j) (gamma.relabel j) xs (hs 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have he := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 2)
    (ys 1) (domain.relabel j) (extended.relabel j) xs (hs 1) (projectionValue 0 xs) (projectionValue 2 xs)
  have hk : Nonempty (Derivation body Theta
      (programGraph (succOf (.projection 4)) (suc (cutoff.relabel j)) xs)) :=
    unaryValue .succ (.projection 4) (suc (cutoff.relabel j)) (cutoff.relabel j) xs
      (successorValue ![cutoff.relabel j]) (projectionValue 4 xs)
  have hf := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 3,succOf (.projection 4),.projection 5] (ys 2) xs
    ![d.relabel j,suc (cutoff.relabel j),child.relabel j] (hs 2)
    (fun i => Fin.cases (projectionValue 3 xs)
      (Fin.cases hk (Fin.cases (projectionValue 5 xs) (fun k => Fin.elim0 k))) i)
  have ht := arrowFields (.projection 6) (typ.relabel j) (ys 3) (ys 4) xs
    (projectionValue 6 xs) (hs 3) (hs 4)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj hg he hf ht

/-- The original H and its exact output fields are supplied once and retained
unchanged; only the base raw argument list is transformed. -/
theorem ordinaryWitnesses (H : Program 1) (erasing : Bool)
    (head base d cutoff : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (headData result types baseOut : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 H headData (head.relabel j))) →
      Nonempty (Derivation body Theta (StepArrowFields headData result types)) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) baseOut (d.relabel j)
          (cutoff.relabel j) (base.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let hp : Program 4 := .composition H (fun _ : Fin 1 => .projection 0)
  let ps : Fin 4 → Program 4 :=
    ![hp,OriginalTypedDecoder.headOf hp,OriginalTypedDecoder.tailOf hp,
      .composition (fold (selectedMode erasing)) ![.projection 2,.projection 3,.projection 1] ]
  let inputs : Fin 4 → OTerm alpha := ![head,base,d,cutoff]
  apply programsCases ps inputs psi
  intro beta j Theta ys hj hs
  let xs : Fin 4 → OTerm beta := fun i => (inputs i).relabel j
  have hh := unaryRecover H (.projection 0) (ys 0) (head.relabel j) xs (hs 0) (projectionValue 0 xs)
  have ht := arrowFields hp (ys 0) (ys 1) (ys 2) xs (hs 0) (hs 1) (hs 2)
  have hf := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 2,.projection 3,.projection 1] (ys 3) xs
    ![d.relabel j,cutoff.relabel j,base.relabel j] (hs 3)
    (fun i => Fin.cases (projectionValue 2 xs)
      (Fin.cases (projectionValue 3 xs) (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) hj hh ht hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
