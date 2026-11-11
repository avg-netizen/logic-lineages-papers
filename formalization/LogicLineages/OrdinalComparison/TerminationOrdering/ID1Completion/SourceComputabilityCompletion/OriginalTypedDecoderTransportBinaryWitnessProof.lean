module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryWitnessProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationWitnesses (erasing : Bool)
    (domain typ fn arg d cutoff : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (arrow fnOut argOut : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepCons arrow (domain.relabel j) (typ.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) fnOut (d.relabel j) (cutoff.relabel j) (fn.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) argOut (d.relabel j) (cutoff.relabel j) (arg.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 3 → Program 6 :=
    ![.composition InternalListCodec.consCode ![.projection 0,.projection 1],
      .composition (fold (selectedMode erasing)) ![.projection 4,.projection 5,.projection 2],
      .composition (fold (selectedMode erasing)) ![.projection 4,.projection 5,.projection 3] ]
  let inputs : Fin 6 → OTerm alpha := ![domain,typ,fn,arg,d,cutoff]
  apply programsCases ps inputs psi
  intro beta j Theta ys hj hs
  let xs : Fin 6 → OTerm beta := fun i => (inputs i).relabel j
  have ht := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 0) (domain.relabel j) (typ.relabel j) xs (hs 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 4,.projection 5,.projection 2] (ys 1) xs
    ![d.relabel j,cutoff.relabel j,fn.relabel j] (hs 1)
    (fun i => Fin.cases (projectionValue 4 xs)
      (Fin.cases (projectionValue 5 xs) (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k))) i)
  have ha := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 4,.projection 5,.projection 3] (ys 2) xs
    ![d.relabel j,cutoff.relabel j,arg.relabel j] (hs 2)
    (fun i => Fin.cases (projectionValue 4 xs)
      (Fin.cases (projectionValue 5 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k))) i)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj ht hf ha

theorem numberedWitnesses (H : Program 1) (erasing : Bool)
    (head base extras d cutoff : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (headData headResult baseTypes baseOut extrasOut : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 H headData (head.relabel j))) →
      Nonempty (Derivation body Theta (StepArrowFields headData headResult baseTypes)) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) baseOut (d.relabel j) (cutoff.relabel j) (base.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) extrasOut (d.relabel j) (cutoff.relabel j) (extras.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let hp : Program 5 := .composition H (fun _ : Fin 1 => .projection 0)
  let ps : Fin 5 → Program 5 :=
    ![hp,OriginalTypedDecoder.headOf hp,OriginalTypedDecoder.tailOf hp,
      .composition (fold (selectedMode erasing)) ![.projection 3,.projection 4,.projection 1],
      .composition (fold (selectedMode erasing)) ![.projection 3,.projection 4,.projection 2] ]
  let inputs : Fin 5 → OTerm alpha := ![head,base,extras,d,cutoff]
  apply programsCases ps inputs psi
  intro beta j Theta ys hj hs
  let xs : Fin 5 → OTerm beta := fun i => (inputs i).relabel j
  have hh := unaryRecover H (.projection 0) (ys 0) (head.relabel j) xs (hs 0) (projectionValue 0 xs)
  have ht := arrowFields hp (ys 0) (ys 1) (ys 2) xs (hs 0) (hs 1) (hs 2)
  have hb := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 3,.projection 4,.projection 1] (ys 3) xs
    ![d.relabel j,cutoff.relabel j,base.relabel j] (hs 3)
    (fun i => Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i)
  have he := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 3,.projection 4,.projection 2] (ys 4) xs
    ![d.relabel j,cutoff.relabel j,extras.relabel j] (hs 4)
    (fun i => Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k))) i)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj hh ht hb he

theorem consWitnesses (erasing : Bool)
    (types head tail d cutoff : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (requestedDomain tailTypes headOut tailOut : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepArrowFields (types.relabel j) requestedDomain tailTypes)) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) headOut (d.relabel j) (cutoff.relabel j) (head.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) tailOut (d.relabel j) (cutoff.relabel j) (tail.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 4 → Program 5 :=
    ![OriginalTypedDecoder.headOf (.projection 0),OriginalTypedDecoder.tailOf (.projection 0),
      .composition (fold (selectedMode erasing)) ![.projection 3,.projection 4,.projection 1],
      .composition (fold (selectedMode erasing)) ![.projection 3,.projection 4,.projection 2] ]
  let inputs : Fin 5 → OTerm alpha := ![types,head,tail,d,cutoff]
  apply programsCases ps inputs psi
  intro beta j Theta ys hj hs
  let xs : Fin 5 → OTerm beta := fun i => (inputs i).relabel j
  have ht := arrowFields (.projection 0) (types.relabel j) (ys 0) (ys 1) xs
    (projectionValue 0 xs) (hs 0) (hs 1)
  have hh := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 3,.projection 4,.projection 1] (ys 2) xs
    ![d.relabel j,cutoff.relabel j,head.relabel j] (hs 2)
    (fun i => Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i)
  have hl := compositionRecover (fold (selectedMode erasing))
    ![Program.projection 3,.projection 4,.projection 2] (ys 3) xs
    ![d.relabel j,cutoff.relabel j,tail.relabel j] (hs 3)
    (fun i => Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k))) i)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) hj ht hh hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryWitnessProof
