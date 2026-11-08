module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
open InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
open InternalApplicationValidityClosure
open InternalParameterizedApplicationCertifiedResultFoldClosureApplicationQueryProof
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationClosure (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (arrow d e fp ap fn arg parent functionOut argumentOut out : OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hguard : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hfunction : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine functionOut fn parameter)))
    (hargument : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine argumentOut arg parameter)))
    (hcombine : Nonempty (Derivation body Gamma (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons parameter Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out parent parameter)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow (Fin.cons fn
      (Fin.cons arg (Fin.cons parent (Fin.cons functionOut (Fin.cons argumentOut
        (Fin.cons out Fin.elim0))))))))))) _
  intro β j ys Delta hj hq
  rw [certifiedFoldPRename]
  have harrow' := renameInto harrow j Delta hj
  have hfn' := renameInto hfn j Delta hj
  have harg' := renameInto harg j Delta hj
  have hparent' := renameInto hparent j Delta hj
  have hguard' := renameInto hguard j Delta hj
  have hfunction' := renameInto hfunction j Delta hj
  have hargument' := renameInto hargument j Delta hj
  have hcombine' := renameInto hcombine j Delta hj
  simp only [programRename,consTermRename,emptyRename,sucRelabel,zRelabel,certifiedFoldPRename]
    at harrow' hfn' harg' hparent' hguard' hfunction' hargument' hcombine'
  simp only [consTermRename,emptyRename] at hq
  exact InternalParameterizedApplicationCertifiedResultFoldClosureApplicationQueryProof.applicationFromQueries guard leaf combine (parameter.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (arrow.relabel j) (fn.relabel j) (arg.relabel j)
    (parent.relabel j) (functionOut.relabel j) (argumentOut.relabel j) (out.relabel j) ys
    harrow' hfn' harg' hparent' hguard' hfunction' hargument' hcombine' hq

theorem actualOriginalParameterizedCertifiedResultFoldApplicationClosure :
    InternalParameterizedApplicationCertifiedResultFoldClosureTargets.ActualOriginalParameterizedCertifiedResultFoldApplicationClosure := by
  intro body guard leaf combine α Gamma arrow d e fp ap fn arg parent functionOut argumentOut out parameter
  let premise := applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph2 guard (suc z) parent parameter ⊓
      (certifiedFoldP guard leaf combine functionOut fn parameter ⊓
        (certifiedFoldP guard leaf combine argumentOut arg parameter ⊓
          programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))))))
  have h : Nonempty (Derivation body (premise :: Gamma) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hc := andLeft h
  have hv := andRight h
  obtain ⟨result⟩ := applicationClosure guard leaf combine parameter arrow d e fp ap fn arg parent
    functionOut argumentOut out (andLeft hc) (andLeft (andRight hc))
    (andLeft (andRight (andRight hc))) (andRight (andRight (andRight hc)))
    (andLeft hv) (andLeft (andRight hv)) (andLeft (andRight (andRight hv)))
    (andRight (andRight (andRight hv)))
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof
