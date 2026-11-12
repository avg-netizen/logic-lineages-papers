module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalRawSyntaxTransport OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawVariableRankSupportProof OriginalRawVariableRankLeafProof
open OriginalVariableErasureCertificateRawProof (equalRefl bottomCodePair)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof

open InternalApplicationStepPeelSupportProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem coordinates (s d cutoff : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (typ raw tag rawE bottomRaw : OTerm beta),
 (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
 Nonempty (Derivation body Theta (graph1 InternalUnpair.left typ (s.relabel rho))) →
 Nonempty (Derivation body Theta (graph1 InternalUnpair.right raw (s.relabel rho))) →
 Nonempty (Derivation body Theta (graph1 rawTag tag raw)) →
 Nonempty (Derivation body Theta (graph3 eraseRaw rawE (d.relabel rho) (cutoff.relabel rho) raw)) →
 Nonempty (Derivation body Theta (graph1 bottomConstructor bottomRaw typ)) →
 Nonempty (Derivation body Theta (psi.relabel rho))) : Nonempty (Derivation body Delta psi) := by
 let ty : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)
 let raw : Program 3 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 0)
 let tag : Program 3 := .composition rawTag (fun _ : Fin 1 => raw)
 let er : Program 3 := .composition eraseRaw ![.projection 1,.projection 2,raw]
 let bot : Program 3 := .composition bottomConstructor (fun _ : Fin 1 => ty)
 let qs : Fin 5 → Program 3 := ![ty,raw,tag,er,bot]
 let xs : Fin 3 → OTerm alpha := ![s,d,cutoff]
 apply InternalApplicationStepPeelSupportProof.queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 3 → OTerm beta := ![s.relabel rho,d.relabel rho,cutoff.relabel rho]
 have hx : (fun i => (xs i).relabel rho) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
 rw [hx] at hq
 have ht := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (s.relabel rho) xx (hq 0) (projectionValue 0 xx)
 have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (s.relabel rho) xx (hq 1) (projectionValue 0 xx)
 have hg := unaryRecover rawTag raw (ys 2) (ys 1) xx (hq 2) (hq 1)
 have he := InternalOriginalUniformVertexPathSupportProof.ternaryRecover eraseRaw (.projection 1) (.projection 2) raw
  (ys 3) (d.relabel rho) (cutoff.relabel rho) (ys 1) xx (hq 3) (projectionValue 1 xx) (projectionValue 2 xx) (hq 1)
 have hb := unaryRecover bottomConstructor ty (ys 4) (ys 0) xx (hq 4) (hq 0)
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hrho ht hr hg he hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankQueryProof
