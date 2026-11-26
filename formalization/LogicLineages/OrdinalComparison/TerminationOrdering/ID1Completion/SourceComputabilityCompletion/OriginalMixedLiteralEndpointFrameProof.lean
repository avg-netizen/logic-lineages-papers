module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atFrame (H G : Program 1) (M W : Program 2)
 (s t parameter fn targetFn arg d e arrow : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalMixedExistentialCongruenceDefinitions.ApplicationFrame
  (OriginalUniverseDecoder.source H G M W) s t parameter fn targetFn arg d e arrow)))
 (ht : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) targetFn parameter))) :
 Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph
  (OriginalMixedLiteralEndpointDefinitions.endpoint H G M W) (numeral 1) d e fn targetFn arg parameter)) := by
 let zero : Program 2 := InternalAcceptance.constantZero 2
 let lift : Program 2 := .composition stepLift (fun _ : Fin 1 => zero)
 let qs : Fin 3 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1),lift]
 let xs : Fin 2 → OTerm alpha := ![fn,arg]
 apply queryCases qs xs _
 intro beta j ys Theta incl hq
 simp only [InternalParameterizedApplicationStepCheckerSyntaxProof.endpointGraphRename,
  GuardedSourceSyntaxProof.numeralRename]
 have hf' := renameInto hf j Theta incl
 rw [OriginalMixedExistentialCongruenceApplicationProof.frameRename] at hf'
 have ht' := renameInto ht j Theta incl
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
 let xx : Fin 2 → OTerm beta := ![fn.relabel j,arg.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
  funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have hq' (i : Fin 3) : Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
  simpa only [hx] using hq i
 have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (fn.relabel j) xx (hq' 0) (projectionValue 0 xx)
 have har := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (arg.relabel j) xx (hq' 1) (projectionValue 1 xx)
 have hz := InternalAcceptanceConjunctionProof.constantZeroValue (body := body) (Gamma := Theta) xx
 have hl := unaryRecover stepLift zero (ys 2) z xx (hq' 2) hz
 have hh := OriginalMixedExistentialCongruenceApplicationProof.frameHop (OriginalUniverseDecoder.source H G M W)
  (s.relabel j) (t.relabel j) (parameter.relabel j) (fn.relabel j) (targetFn.relabel j)
  (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) (ys 2) z hf' hl
 have hfl := andLeft (andRight (andRight (andRight (andRight hf'))))
 have hal := andRight (andRight (andRight (andRight (andRight (andRight hf')))))
 have hcs := andIntro (andLeft (andRight (andRight (andRight hf'))))
  (andIntro (reconstructPair (fn.relabel j) (arrow.relabel j) (ys 0) hfl hfr)
   (andIntro (reconstructPair (arg.relabel j) (d.relabel j) (ys 1) hal har)
    (applicationForward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
      (ys 0) (ys 1) (s.relabel j) hfr har (andLeft (andRight hf')))))
 exact OriginalMixedLiteralEndpointValidityProof.actualEndpointFromTargetSource H G M W body beta Theta
  (s.relabel j) (t.relabel j) (ys 2) (parameter.relabel j) (fn.relabel j) (targetFn.relabel j)
  z (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) (ys 0) (ys 1) hcs hh ht'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointFrameProof
