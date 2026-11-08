module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationValidityClosure
open InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationClosure (guard leaf : Program 1) (combine : Program 4)
    (arrow d e fp ap fn arg parent functionOut argumentOut out : OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hguard : Nonempty (Derivation body Gamma (graph1 guard (suc z) parent)))
    (hfunction : Nonempty (Derivation body Gamma (certifiedFold guard leaf combine functionOut fn)))
    (hargument : Nonempty (Derivation body Gamma (certifiedFold guard leaf combine argumentOut arg)))
    (hcombine : Nonempty (Derivation body Gamma (graph4 combine out d e functionOut argumentOut))) :
    Nonempty (Derivation body Gamma (certifiedFold guard leaf combine out parent)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow (Fin.cons fn
      (Fin.cons arg (Fin.cons parent (Fin.cons functionOut (Fin.cons argumentOut
        (Fin.cons out Fin.elim0))))))))))) _
  intro β j ys Delta hj hq
  rw [certifiedFoldRename]
  have harrow' := renameInto harrow j Delta hj
  have hfn' := renameInto hfn j Delta hj
  have harg' := renameInto harg j Delta hj
  have hparent' := renameInto hparent j Delta hj
  have hguard' := renameInto hguard j Delta hj
  have hfunction' := renameInto hfunction j Delta hj
  have hargument' := renameInto hargument j Delta hj
  have hcombine' := renameInto hcombine j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel,certifiedFoldRename]
    at harrow' hfn' harg' hparent' hguard' hfunction' hargument' hcombine'
  simp only [consTermRename,emptyRename] at hq
  exact applicationFromQueries guard leaf combine (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (arrow.relabel j) (fn.relabel j) (arg.relabel j)
    (parent.relabel j) (functionOut.relabel j) (argumentOut.relabel j) (out.relabel j) ys
    harrow' hfn' harg' hparent' hguard' hfunction' hargument' hcombine' hq

theorem actualOriginalCertifiedResultFoldApplicationClosure :
    InternalApplicationCertifiedResultFoldClosureTargets.ActualOriginalCertifiedResultFoldApplicationClosure := by
  intro body guard leaf combine α arrow d e fp ap fn arg parent functionOut argumentOut out
  let premise := applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph1 guard (suc z) parent ⊓
      (certifiedFold guard leaf combine functionOut fn ⊓
        (certifiedFold guard leaf combine argumentOut arg ⊓
          graph4 combine out d e functionOut argumentOut)))
  have h : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hc := andLeft h
  have hv := andRight h
  obtain ⟨result⟩ := applicationClosure guard leaf combine arrow d e fp ap fn arg parent
    functionOut argumentOut out (andLeft hc) (andLeft (andRight hc))
    (andLeft (andRight (andRight hc))) (andRight (andRight (andRight hc)))
    (andLeft hv) (andLeft (andRight hv)) (andLeft (andRight (andRight hv)))
    (andRight (andRight (andRight hv)))
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationProof
