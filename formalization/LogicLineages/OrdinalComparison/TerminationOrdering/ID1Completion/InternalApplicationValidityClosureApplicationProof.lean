module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack InternalApplicationValidityClosure
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityClosureApplicationQueryProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationClosure (node leaf : Program 1)
    (arrow d e fp ap fn arg parent : OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hnode : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hfnValid : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) fn)))
    (hargValid : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) arg))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) parent)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow
      (Fin.cons fn (Fin.cons arg (Fin.cons parent Fin.elim0)))))))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename,sucRelabel,zRelabel]
  have harrow' := renameInto harrow j Delta hj
  have hfn' := renameInto hfn j Delta hj
  have harg' := renameInto harg j Delta hj
  have hparent' := renameInto hparent j Delta hj
  have hnode' := renameInto hnode j Delta hj
  have hfnValid' := renameInto hfnValid j Delta hj
  have hargValid' := renameInto hargValid j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
    at harrow' hfn' harg' hparent' hnode' hfnValid' hargValid'
  simp only [consTermRename,emptyRename] at hq
  exact applicationFromQueries node leaf (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j) ys
    harrow' hfn' harg' hparent' hnode' hfnValid' hargValid' hq

theorem actualOriginalValidatorApplicationClosure :
    InternalApplicationValidityClosureTargets.ActualOriginalValidatorApplicationClosure := by
  intro body node leaf α arrow d e fp ap fn arg parent
  let premise := applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph1 node (suc z) e ⊓
      (graph1 (validator node leaf) (suc z) fn ⊓ graph1 (validator node leaf) (suc z) arg))
  have h : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hc := andLeft h
  have hv := andRight h
  obtain ⟨result⟩ := applicationClosure node leaf arrow d e fp ap fn arg parent
    (andLeft hc) (andLeft (andRight hc)) (andLeft (andRight (andRight hc)))
    (andRight (andRight (andRight hc)))
    (andLeft hv) (andLeft (andRight hv)) (andRight (andRight hv))
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationProof
