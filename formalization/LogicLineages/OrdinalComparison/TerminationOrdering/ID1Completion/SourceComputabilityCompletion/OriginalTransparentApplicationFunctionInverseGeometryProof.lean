module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeel
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityClosure (applicationConstructors)
open OriginalTransparentApplicationFunctionInverseSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tagAtInput (p : Program 1) (state input : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 p input state)))
 (ht : Nonempty (Derivation body Delta (graph1 (constructorTag p) positionTerm state))) :
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag positionTerm input)) := by
 apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
 intro beta j Theta raw hj hr
 simp only [consTermRename,emptyRename] at hr
 have hp' := renameInto hp j Theta hj
 have ht' := renameInto ht j Theta hj
 rw [graph1Rename] at hp'
 simp only [graph1Rename,positionTerm,GuardedSourceSyntaxProof.numeralRename,sucRelabel,zRelabel] at ht'
 simp only [graph1Rename,positionTerm,GuardedSourceSyntaxProof.numeralRename,sucRelabel,zRelabel]
 let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
 have hrstate := unaryValue InternalUnpair.right p raw (input.relabel j) xs hr hp'
 have htag := unaryRecover InternalUnpair.left (rightOf p) positionTerm raw xs ht' hrstate
 let ys : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
 exact unaryValue InternalUnpair.left (rightOf (.projection 0)) positionTerm raw ys htag
   (unaryValue InternalUnpair.right (.projection 0) raw (input.relabel j) ys hr (projectionValue 0 ys))

theorem packedTransport (d' e' fp ap' d e ap t : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (eqn d' d)))
 (he : Nonempty (Derivation body Delta (eqn e' e)))
 (ha : Nonempty (Derivation body Delta (eqn ap' ap)))
 (ht : Nonempty (Derivation body Delta (graph4 packedApplication t d' e' fp ap'))) :
 Nonempty (Derivation body Delta (graph4 packedApplication t d e fp ap)) := by
 apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 4 Delta
   (OrdinaryArithmetic.graphFormula packedApplication) t
   (Fin.cons d' (Fin.cons e' (Fin.cons fp (Fin.cons ap' Fin.elim0))))
   (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) _ ht
 intro i
 let xs : Fin 4 → OTerm alpha := Fin.cons d' (Fin.cons e' (Fin.cons fp (Fin.cons ap' Fin.elim0)))
 let ys : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
 have hh : ∀ k : Fin 4, Nonempty (Derivation body Delta (eqn (xs k) (ys k))) := by
  intro k
  exact Fin.cases hd (Fin.cases he (Fin.cases ⟨InternalTagArithmeticSupportProof.refl fp⟩
    (Fin.cases ha (fun l => Fin.elim0 l)))) k
 change Nonempty (Derivation body Delta (InternalControlGraph.equal _ _))
 rw [InternalControlGraphSupportProof.equalEqn]
 exact hh i


theorem targetAtState (state s t arrow d e fp ap fn arg targetFn : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg s)))
 (hs : Nonempty (Derivation body Delta (graph1 source s state)))
 (ht : Nonempty (Derivation body Delta (graph1 target t state)))
 (hg : Nonempty (Derivation body Delta (graph1 structuralGuard (suc z) state)))
 (hf : Nonempty (Derivation body Delta (graph1 targetFunctionCode targetFn state))) :
 Nonempty (Derivation body Delta (graph4 application t d e targetFn arg ⊓ graph1 InternalUnpair.left arrow targetFn)) := by
 have guards := guardParts state hg
 have htag := sameLeft (constructorTag target) (two 1) positionTerm (Fin.cons state Fin.elim0)
   (andLeft (andRight (andRight (andRight guards)))) (twoValue _)
 have htinput := tagAtInput target state t ht htag
 apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases t z _ htinput
 intro beta j Theta payload ar dt et fpt apt fnt argt hj htc hpayload hfr har hfl hal
 have hc' := renameInto hc j Theta hj
 simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
 have hs' := renameInto hs j Theta hj
 have ht' := renameInto ht j Theta hj
 have hg' := renameInto hg j Theta hj
 have hf' := renameInto hf j Theta hj
 simp only [graph1Rename,sucRelabel,zRelabel] at hs' ht' hg' hf'
 simp only [conjunctionRename,graph4Rename,graph1Rename]
 let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
 have sf := packedFieldsAt source (state.relabel j) (s.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
   hs' (andRight (andRight (andRight hc')))
 have tf := packedFieldsAt target (state.relabel j) (t.relabel j) dt et fpt apt ht'
   (andRight (andRight (andRight htc)))
 have gp := guardParts (state.relabel j) hg'
 have hegraph := sameRight (outerType source) (outerType target) (e.relabel j) xs
   (andLeft (andRight (andRight (andRight (andRight gp))))) (andLeft sf)
 have hdgraph := sameRight (appDomain source) (appDomain target) (d.relabel j) xs
   (andLeft (andRight (andRight (andRight (andRight (andRight gp)))))) (andLeft (andRight (andRight sf)))
 have hagraph := sameRight (argumentPayload source) (argumentPayload target) (ap.relabel j) xs
   (andRight (andRight (andRight (andRight (andRight (andRight gp)))))) (andRight (andRight (andRight (andRight sf))))
 have heq := valueUnique (outerType target) et (e.relabel j) xs (andLeft tf) hegraph
 have hdq := valueUnique (appDomain target) dt (d.relabel j) xs (andLeft (andRight (andRight tf))) hdgraph
 have haq := valueUnique (argumentPayload target) apt (ap.relabel j) xs (andRight (andRight (andRight (andRight tf)))) hagraph
 have hpacked := packedTransport dt et fpt apt (d.relabel j) (e.relabel j) (ap.relabel j) (t.relabel j)
   hdq heq haq (andRight (andRight (andRight htc)))
 have harrow := binaryValue InternalListCodec.consCode domain codomain (arrow.relabel j) (d.relabel j) (e.relabel j) xs
   (andLeft hc') (andLeft (andRight (andRight sf))) (andLeft sf)
 have htargetpair := binaryRecover InternalPairing.pairing arrowType (functionPayload target)
   (targetFn.relabel j) (arrow.relabel j) fpt xs hf' harrow (andLeft (andRight (andRight (andRight tf))))
 have hargpair := andLeft (andRight (andRight hc'))
 exact andIntro (applicationBackward (d.relabel j) (e.relabel j) (targetFn.relabel j) (arg.relabel j)
   fpt (ap.relabel j) (t.relabel j) (pairRight _ _ _ htargetpair) (pairRight _ _ _ hargpair) hpacked)
   (pairLeft _ _ _ htargetpair)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseGeometryProof
