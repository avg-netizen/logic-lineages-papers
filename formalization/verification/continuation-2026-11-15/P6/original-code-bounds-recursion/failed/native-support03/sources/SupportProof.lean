module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem acceptedValue (n : Nat) (raw answers param out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) out raw))) :
    Nonempty (Derivation body Delta (graph3 (accepted n) out raw answers param)) :=
  unaryValue (OriginalCodeValidityGuard.check n) (.projection 0) out raw ![raw,answers,param]
    hg (projectionValue 0 ![raw,answers,param])

theorem positiveValue (n : Nat) (raw answers param out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalBoundsRecombination.recombine n) out raw answers))) :
    Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param)) := by
  have hv := binaryValue (OriginalBoundsRecombination.recombine n) (.projection 0) (.projection 1)
    out raw answers ![raw,answers,param] hr
    (projectionValue 0 ![raw,answers,param]) (projectionValue 1 ![raw,answers,param])
  exact successorBranchIntro (accepted n) (InternalLessThan.constantOne 3)
    (.composition (OriginalBoundsRecombination.recombine n) ![.projection 0,.projection 1])
    out z ![raw,answers,param] (acceptedValue n raw answers param (numeral 1) hg) hv

theorem zeroValue (n : Nat) (raw answers param : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc z) raw answers param)) :=
  zeroBranchIntro (accepted n) (InternalLessThan.constantOne 3)
    (.composition (OriginalBoundsRecombination.recombine n) ![.projection 0,.projection 1])
    (suc z) ![raw,answers,param] (acceptedValue n raw answers param z hg)
    (InternalLessThanSupportProof.oneConstantValue ![raw,answers,param])

theorem recombineSuccess (n : Nat) (raw answers out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hv : Nonempty (Derivation body Delta (graph2
      (.composition OriginalBoundsRecombination.merge
        ![.composition (OriginalBoundsRecombination.root n) (fun _ : Fin 1 => .projection 0),
          .composition OriginalBoundsRecombination.collect (fun _ : Fin 1 => .projection 1)]) out raw answers))) :
    Nonempty (Derivation body Delta (graph2 (OriginalBoundsRecombination.recombine n) (suc out) raw answers)) := by
  let inner : Program 2 := .composition OriginalBoundsRecombination.merge
    ![.composition (OriginalBoundsRecombination.root n) (fun _ : Fin 1 => .projection 0),
      .composition OriginalBoundsRecombination.collect (fun _ : Fin 1 => .projection 1)]
  have hc := unaryValue (OriginalCodeValidityGuard.check n) (.projection 0) (suc z) raw ![raw,answers]
    hg (projectionValue 0 ![raw,answers])
  have hs := unaryValue .succ inner (suc out) out ![raw,answers]
    (successorValue (Fin.cons out Fin.elim0)) hv
  exact successorBranchIntro
    (.composition (OriginalCodeValidityGuard.check n) (fun _ : Fin 1 => .projection 0))
    (OriginalRawSyntaxTransport.constant 2 0) (.composition .succ (fun _ : Fin 1 => inner))
    (suc out) z ![raw,answers] hc hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.SupportProof
