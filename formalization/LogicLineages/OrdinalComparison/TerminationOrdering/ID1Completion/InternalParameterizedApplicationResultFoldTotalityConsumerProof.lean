module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationResultFoldTotality InternalParameterizedApplicationResultFoldTotalityTargets
open InternalParameterizedApplicationResultFoldTotalitySyntaxProof InternalParameterizedApplicationResultFoldTotalityBindingProof
open InternalParameterizedApplicationResultFoldTotalityInductionProof
open InternalParameterizedApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalApplicationValidityClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The certified witness produced by internal induction gives unconditional
whole-state acceptance. No inference from external evaluation occurs. -/
theorem goodRunAccepted (guard leaf : Program 2) (combine : Program 5)
    (input parameter : OTerm α) :
    Nonempty (Derivation body Gamma (goodRunAcceptedP guard leaf combine input parameter)) := by
  apply hasCertifiedOutputCases guard leaf combine input parameter _
    (certifiedOutputExists guard leaf combine input parameter)
  intro β j Delta out hj hc
  rw [goodRunAcceptedRename]
  exact andLeft hc

/-- Retain the consumer's actual supplied output graph, even for output zero. -/
theorem certifyActualOutput (guard leaf : Program 2) (combine : Program 5)
    (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (foldGraphP guard leaf combine out input parameter))) :
    Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out input parameter)) :=
  andIntro (goodRunAccepted guard leaf combine input parameter) h

theorem actualOriginalParameterizedResultFoldOutputSuccess :
    ActualOriginalParameterizedResultFoldOutputSuccess := by
  intro body guard leaf combine α Gamma out input parameter
  obtain ⟨h⟩ := goodRunAccepted (body := body)
    (Gamma := foldGraphP guard leaf combine out input parameter :: Gamma)
    guard leaf combine input parameter
  exact ⟨Derivation.implicationIntroduction h⟩

/-- The original application closure now consumes only actual child folds;
their success is supplied by the already proved internal totality theorem. -/
theorem applicationForward (guard leaf : Program 2) (combine : Program 5)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (foldGraphP guard leaf combine functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (foldGraphP guard leaf combine argumentOut arg parameter)))
    (hcomb : Nonempty (Derivation body Gamma
      (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut
        (Fin.cons argumentOut (Fin.cons parameter Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma (foldGraphP guard leaf combine out parent parameter)) := by
  have h := InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    guard leaf combine parameter arrow d e fp ap fn arg parent functionOut argumentOut out
    (andLeft hc) (andLeft (andRight hc)) (andLeft (andRight (andRight hc)))
    (andRight (andRight (andRight hc))) hg
    (certifyActualOutput guard leaf combine functionOut fn parameter hf)
    (certifyActualOutput guard leaf combine argumentOut arg parameter ha) hcomb
  exact andRight h

/-- Reverse the application equation by taking the actual C witness and
identifying its parent-fold output with the supplied one by functionality. -/
theorem applicationBackward (guard leaf : Program 2) (combine : Program 5)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (foldGraphP guard leaf combine functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (foldGraphP guard leaf combine argumentOut arg parameter)))
    (hp : Nonempty (Derivation body Gamma (foldGraphP guard leaf combine out parent parameter))) :
    Nonempty (Derivation body Gamma
      (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut
        (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))))) := by
  apply programCases combine
    (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))) _
  intro β j Delta produced hj hcomb
  simp only [programRename,consTermRename,emptyRename]
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [foldGraphRename] at hf' ha' hp'
  simp only [consTermRename,emptyRename] at hcomb
  have hproduced := applicationForward guard leaf combine
    (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) produced (parameter.relabel j)
    hc' hg' hf' ha' hcomb
  have he := valueUnique (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
    produced (out.relabel j)
    (Fin.cons (parent.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hproduced hp'
  exact outputTransport combine produced (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (functionOut.relabel j)
      (Fin.cons (argumentOut.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))))) he hcomb

theorem actualOriginalParameterizedResultFoldApplicationEquation :
    ActualOriginalParameterizedResultFoldApplicationEquation := by
  intro body guard leaf combine α Gamma arrow d e fp ap fn arg parent functionOut argumentOut out parameter
  let premise := applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph2 guard (suc z) parent parameter ⊓
      (foldGraphP guard leaf combine functionOut fn parameter ⊓
        foldGraphP guard leaf combine argumentOut arg parameter))
  let fold := foldGraphP guard leaf combine out parent parameter
  let combined := programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut
    (Fin.cons argumentOut (Fin.cons parameter Fin.elim0)))))
  have hp : Nonempty (Derivation body (fold :: premise :: Gamma) premise) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hfold : Nonempty (Derivation body (fold :: premise :: Gamma) fold) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := applicationBackward guard leaf combine arrow d e fp ap fn arg parent
    functionOut argumentOut out parameter (andLeft hp) (andLeft (andRight hp))
    (andLeft (andRight (andRight hp))) (andRight (andRight (andRight hp))) hfold
  have hp' : Nonempty (Derivation body (combined :: premise :: Gamma) premise) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcombined : Nonempty (Derivation body (combined :: premise :: Gamma) combined) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := applicationForward guard leaf combine arrow d e fp ap fn arg parent
    functionOut argumentOut out parameter (andLeft hp') (andLeft (andRight hp'))
    (andLeft (andRight (andRight hp'))) (andRight (andRight (andRight hp'))) hcombined
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
