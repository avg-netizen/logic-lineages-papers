module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldRepresentativeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldTargets
open InternalParameterizedCanonicalResultFoldSyntaxProof InternalParameterizedCanonicalResultFoldOpeningProof
open InternalParameterizedCanonicalResultFoldConsumerProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- All three extra witnesses are actual internal program outputs. Neither
the original argument nor its normalized value is assumed fixed by N. -/
theorem representativeAtWitnesses (data : Data)
    (arrow d e fn arg parent x out parameter fp ap b : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (representativePremises data arrow d e fn arg parent x out parameter)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap arg)))
    (hb : Nonempty (Derivation body Gamma (foldGraph data b arg parameter))) :
    Nonempty (Derivation body Gamma (representativeConclusion data parent out e parameter)) := by
  have harrow := andLeft h
  have hvf := andLeft (andRight h)
  have hlf := andLeft (andRight (andRight h))
  have hva := andLeft (andRight (andRight (andRight h)))
  have hla := andLeft (andRight (andRight (andRight (andRight h))))
  have hm := andLeft (andRight (andRight (andRight (andRight (andRight h)))))
  have hn := andLeft (andRight (andRight (andRight (andRight (andRight (andRight h))))))
  have hp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
  have hj := andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
  have hparent := rawValidity data arrow d e fn arg parent parameter harrow hlf hla hm hvf hva hp
  have hfunction := reconstructPair fn arrow fp hlf hfr
  have hargument := reconstructPair arg d ap hla har
  have hpacked := applicationForward d e fn arg fp ap parent hfr har hp
  have hc := andIntro harrow (andIntro hfunction (andIntro hargument hpacked))
  have hg := rootGuardValue data arrow d e fp ap fn arg parent parameter hc hparent hvf hva hm
  have hcf := certifiedAt data x fn arrow parameter hvf hlf hn
  have hca := certifiedAt data b arg d parameter hva hla hb
  let xs : Fin 5 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons arg (Fin.cons parameter Fin.elim0))))
  have hcombine : Nonempty (Derivation body Gamma
      (programGraph (combine data) out
        (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons b (Fin.cons parameter Fin.elim0))))))) := by
    apply compositionRecover (combine data)
      ![.projection 0,.projection 1,.projection 2,
        .composition (foldN data) ![.projection 3,.projection 4],.projection 4] out xs
      (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons b (Fin.cons parameter Fin.elim0))))) hj
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases
        (binaryValue (foldN data) (.projection 3) (.projection 4)
          b arg parameter xs hb (projectionValue 3 xs) (projectionValue 4 xs))
        (Fin.cases (projectionValue 4 xs) (fun q => Fin.elim0 q))))) i
  have hfold := InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    (rootGuard data) (leaf data) (combine data) parameter
    arrow d e fp ap fn arg parent x b out harrow hfunction hargument hpacked hg
    (andLeft hcf) (andLeft hca) hcombine
  exact andIntro hparent (certifiedAt data out parent e parameter hparent
    (rawLeft d e fn arg parent hp) (andRight hfold))

theorem representativeApplication (data : Data)
    (arrow d e fn arg parent x out parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (representativePremises data arrow d e fn arg parent x out parameter))) :
    Nonempty (Derivation body Gamma (representativeConclusion data parent out e parameter)) := by
  let qs : Fin 3 → Program 3 := ![rightOf (.projection 0),rightOf (.projection 1),
    .composition (foldN data) ![.projection 1,.projection 2] ]
  let xs : Fin 3 → OTerm α := Fin.cons fn (Fin.cons arg (Fin.cons parameter Fin.elim0))
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  rw [representativeConclusionRename]
  have h' := renameInto h j Delta hj
  rw [representativePremisesRename] at h'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 3 → OTerm β :=
    Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (fn.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have har := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (arg.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  have hb := binaryRecover (foldN data) (.projection 1) (.projection 2)
    (ys 2) (arg.relabel j) (parameter.relabel j) xx (hq 2)
    (projectionValue 1 xx) (projectionValue 2 xx)
  exact representativeAtWitnesses data (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fn.relabel j) (arg.relabel j) (parent.relabel j) (x.relabel j) (out.relabel j)
    (parameter.relabel j) (ys 0) (ys 1) (ys 2) h' hfr har hb

theorem actualParameterizedCanonicalRepresentativeApplicationTransport :
    ActualParameterizedCanonicalRepresentativeApplicationTransport := by
  intro body data α Gamma arrow d e fn arg parent x out parameter
  obtain ⟨h⟩ := representativeApplication (body := body)
    (Gamma := representativePremises data arrow d e fn arg parent x out parameter :: Gamma)
    data arrow d e fn arg parent x out parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldRepresentativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldRepresentativeProof
