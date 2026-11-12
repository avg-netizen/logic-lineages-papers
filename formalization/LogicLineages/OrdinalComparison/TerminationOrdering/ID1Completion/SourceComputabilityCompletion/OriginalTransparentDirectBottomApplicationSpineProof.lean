module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomApplicationSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual application recurrence increments the function-spine depth.
Thus an original bottom target has strictly smaller depth, irrespective of
whether the source's function-spine flag is set. -/
theorem atConstructors (s t cert parameter typ arrow d e fp ap fn arg : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg s)))
    (hb : Nonempty (Derivation body Delta
      (graph1 BottomRepresentative.bottomCode t typ))) :
    Nonempty (Derivation body Delta
      (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
        (suc z) s t cert parameter)) := by
  let f : Program 2 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 0)
  let a : Program 2 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 1)
  let flag : Program 2 := leftOf f
  let depth : Program 2 := rightOf f
  let next : Program 2 := .composition .succ (fun _ : Fin 1 => depth)
  let mark : Program 2 := pairOf flag next
  let qs : Fin 5 → Program 2 := ![f,a,flag,depth,mark]
  let xs : Fin 2 → OTerm alpha := ![fn,arg]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph4Rename,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  simp only [InternalApplicationValidityClosure.applicationConstructors,
    conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at hb'
  let xx : Fin 2 → OTerm beta := ![fn.relabel j,arg.relabel j]
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have hh : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
    intro i
    simpa only [hxs] using hq i
  have hfm := unaryRecover BottomSpineMeasure.measure (.projection 0)
    (ys 0) (fn.relabel j) xx (hh 0) (projectionValue 0 xx)
  have ham := unaryRecover BottomSpineMeasure.measure (.projection 1)
    (ys 1) (arg.relabel j) xx (hh 1) (projectionValue 1 xx)
  have hflag := unaryRecover InternalUnpair.left f (ys 2) (ys 0) xx (hh 2) (hh 0)
  have hdepth := unaryRecover InternalUnpair.right f (ys 3) (ys 0) xx (hh 3) (hh 0)
  have hsuc : Nonempty (Derivation body Theta (graph1 Program.succ (suc (ys 3)) (ys 3))) :=
    successorValue (Fin.cons (ys 3) Fin.elim0)
  have hn := unaryValue Program.succ depth (suc (ys 3)) (ys 3) xx hsuc (hh 3)
  have hp := binaryRecover InternalPairing.pairing flag next (ys 4) (ys 2) (suc (ys 3)) xx
    (hh 4) (hh 2) hn
  have hm := BottomSpineMeasureInternalProof.backward
    (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (fn.relabel j) (arg.relabel j) (s.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (suc (ys 3)) (ys 4)
    (andIntro hc' (andIntro hfm (andIntro ham (andIntro hflag (andIntro hdepth hsuc))))) hp
  have ht := OriginalSpineNonBottomMeasureProof.bottomMeasure (t.relabel j) (typ.relabel j) hb'
  have hpair := BottomSourceClosedProof.numeralPair (body := body) (Delta := Theta) 1 0
  have htd := pairRight (numeral (Nat.pair 1 0)) (suc z) z hpair
  have htf := pairLeft (numeral (Nat.pair 1 0)) (suc z) z hpair
  have hsd := pairRight (ys 4) (ys 2) (suc (ys 3)) hp
  let Q : Formula beta := graph1 InternalUnpair.left (suc z) (ys 4)
  have hconditions : Nonempty (Derivation body Theta
      (Q.imp (graph1 InternalUnpair.left (suc z) (numeral (Nat.pair 1 0)) ⊓
        InternalOriginalOrderSyntaxProof.ltF z (suc (ys 3))))) := by
    obtain ⟨hf⟩ := withHyp htf Q
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hf
      (InternalQuotientComparisonProof.zeroLessSuccessor (ys 3)))⟩
  exact PositiveSpineRulesProof.spineValue BottomSpineMeasure.measure
    (ys 4) (numeral (Nat.pair 1 0)) (suc (ys 3)) z
    (Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
      (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))))
    hm ht hsd htd hconditions

/-- Exact raw-tag application case; no source-validity or representative
premise is required to prove its spine guard against an original bottom. -/
theorem applicationSpine (s t cert parameter typ : OTerm alpha)
    (htag : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaConstructor.tag (numeral 2) s)))
    (hb : Nonempty (Derivation body Delta
      (graph1 BottomRepresentative.bottomCode t typ))) :
    Nonempty (Derivation body Delta
      (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
        (suc z) s t cert parameter)) := by
  apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases s parameter _ htag
  intro beta j Theta payload arrow d e fp ap fn arg hj hc _ _ _ _ _
  simp only [graph4Rename,sucRelabel,zRelabel]
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at hb'
  exact atConstructors (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
    (typ.relabel j) arrow d e fp ap fn arg hc hb'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomApplicationSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomApplicationSpineProof
