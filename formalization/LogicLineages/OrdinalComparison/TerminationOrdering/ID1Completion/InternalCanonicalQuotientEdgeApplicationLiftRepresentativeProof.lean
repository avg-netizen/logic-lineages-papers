module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalCanonicalQuotientEdgeApplicationLift InternalCanonicalQuotientEdgeApplicationLiftTargets
open InternalCanonicalQuotientEdgeApplicationLiftRepresentativeSupportProof
open InternalCanonicalResultFoldInvariantConsumerProof InternalCanonicalResultFoldInvariantInductionProof
open InternalCanonicalResultFoldInvariantApplicationSupportProof
open InternalCanonicalResultFoldInvariantSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The supplied actual N graph plus its derived success certify a child. -/
theorem certifiedAt (data : Data) (out input typ : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid (suc z) input)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) out input))) :
    Nonempty (Derivation body Gamma
      (InternalCanonicalResultFoldInvariant.certifiedOutput data.oldValidity
        data.oldEdge.targetRepresentative data.member out input typ)) := by
  have hs := consumerFromExistence data.oldValidity data.oldEdge.targetRepresentative data.member
    out input typ (certifiedOutputExists data.oldValidity data.oldEdge.targetRepresentative data.member
      input typ (andIntro hv hl)) hn
  exact andIntro (andIntro (andLeft hs) hn) (andRight hs)

/-- No new premises survive: these are internally queried payloads and N(a). -/
theorem representativeAtWitnesses (data : Data)
    (arrow d e f a parent x out fp ap b : OTerm α)
    (h : Nonempty (Derivation body Gamma (representativePremises data arrow d e f a parent x out)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (har : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hb : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) b a))) :
    Nonempty (Derivation body Gamma (representativeConclusion data parent out e)) := by
  have harrow := andLeft h
  have hvf := andLeft (andRight h)
  have hlf := andLeft (andRight (andRight h))
  have hva := andLeft (andRight (andRight (andRight h)))
  have hla := andLeft (andRight (andRight (andRight (andRight h))))
  have hm := andLeft (andRight (andRight (andRight (andRight (andRight h)))))
  have hn := andLeft (andRight (andRight (andRight (andRight (andRight (andRight h))))))
  have hp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
  have hj := andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
  have hparent := rawValidity data.oldValidity data.member arrow d e f a parent
    harrow hlf hla hm hvf hva hp
  have hfunction := reconstructPair f arrow fp hlf hfr
  have hargument := reconstructPair a d ap hla har
  have hpacked := applicationForward d e f a fp ap parent hfr har hp
  have hg := packedGuard (InternalCanonicalDescentSelection.validity data).sourceValid data.member
    arrow d e fp ap f a parent harrow hfunction hargument hpacked hparent hvf hva hm
  have hcfunction := certifiedAt data x f arrow hvf hlf hn
  have hcargument := certifiedAt data b a d hva hla hb
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons a Fin.elim0)))
  have hcombine : Nonempty (Derivation body Gamma
      (graph4 (InternalCanonicalResultFoldCalibration.combine data) out d e x b)) := by
    apply compositionRecover (InternalCanonicalResultFoldCalibration.combine data)
      ![.projection 0,.projection 1,.projection 2,
        .composition (InternalCanonicalResultFoldCalibration.normalizer data)
          (fun _ : Fin 1 => .projection 3)] out xs
      (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons b Fin.elim0)))) hj
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases
        (unaryValue (InternalCanonicalResultFoldCalibration.normalizer data) (.projection 3)
          b a xs hb (projectionValue 3 xs)) (fun q => Fin.elim0 q)))) i
  have hfold := InternalApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    (InternalCanonicalResultFoldCalibration.rootGuard data)
    (InternalCanonicalResultFoldCalibration.leaf data)
    (InternalCanonicalResultFoldCalibration.combine data)
    arrow d e fp ap f a parent x b out harrow hfunction hargument hpacked hg
    (andLeft hcfunction) (andLeft hcargument) hcombine
  exact andIntro hparent (certifiedAt data out parent e hparent
    (rawLeft d e f a parent hp) (andRight hfold))

/-- Original totality eliminates all three witnesses capture-avoidably. -/
theorem representativeApplication (data : Data) (arrow d e f a parent x out : OTerm α)
    (h : Nonempty (Derivation body Gamma (representativePremises data arrow d e f a parent x out))) :
    Nonempty (Derivation body Gamma (representativeConclusion data parent out e)) := by
  let qs : Fin 3 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1),
    .composition (InternalCanonicalResultFoldCalibration.normalizer data)
      (fun _ : Fin 1 => .projection 1)]
  let xs : Fin 2 → OTerm α := Fin.cons f (Fin.cons a Fin.elim0)
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [representativeConclusion,conjunctionRename,graph1Rename,
    InternalOriginalStepGuard.one, sucRelabel,zRelabel,certifiedOutputRename]
  have h' := renameInto h j Delta hj
  simp only [representativePremises,applicationGraph,conjunctionRename,graph1Rename,
    graph2Rename,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at h'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm β := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (f.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have har := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (a.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  have hb := unaryRecover (InternalCanonicalResultFoldCalibration.normalizer data) (.projection 1)
    (ys 2) (a.relabel j) xx (hq 2) (projectionValue 1 xx)
  exact representativeAtWitnesses data (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (parent.relabel j) (x.relabel j) (out.relabel j)
    (ys 0) (ys 1) (ys 2) h' hfr har hb

theorem actualOriginalCanonicalRepresentativeApplicationTransport :
    ActualOriginalCanonicalRepresentativeApplicationTransport := by
  intro body data α Gamma arrow d e f a parent x out
  obtain ⟨h⟩ := representativeApplication (body := body)
    (Gamma := representativePremises data arrow d e f a parent x out :: Gamma)
    data arrow d e f a parent x out ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeProof
