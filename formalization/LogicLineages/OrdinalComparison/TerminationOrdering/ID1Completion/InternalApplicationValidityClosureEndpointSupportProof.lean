module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack InternalApplicationValidityClosure
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof InternalRecursionClosureLogicProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original raw application graph uses precisely the two supplied right
selector outputs. The original reverse unpair theorem supplies its typed
children, so no decoding or payload equality premise is needed. -/
theorem applicationClosureAtPayloads (node leaf : Program 1)
    (arrow d e f a parent fp ap : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (haright : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hn : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hf : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) parent)) := by
  have hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap f a parent)) :=
    andIntro har (andIntro (reconstructPair f arrow fp hfl hfr)
      (andIntro (reconstructPair a d ap hal haright)
        (applicationForward d e f a fp ap parent hfr haright hp)))
  exact closedApply
    (InternalApplicationValidityClosureApplicationProof.actualOriginalValidatorApplicationClosure
      body node leaf α arrow d e fp ap f a parent)
    (andIntro hc (andIntro hn (andIntro hf ha)))

/-- The argument payload is an internal totality witness, scoped only inside
the continuation. All existing premises are transported to that scope. -/
theorem applicationClosureAtFunctionPayload (node leaf : Program 1)
    (arrow d e f a parent fp : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hn : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hf : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) parent)) := by
  apply programCases InternalUnpair.right (Fin.cons a Fin.elim0) _
  intro β j Delta ap hj hap
  simp only [graph1Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hap
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hfr' := renameInto hfr j Delta hj
  have hn' := renameInto hn j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
    at har' hfl' hal' hfr' hn' hf' ha' hp'
  exact applicationClosureAtPayloads node leaf (arrow.relabel j) (d.relabel j)
    (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) (fp.relabel j) ap
    har' hfl' hal' hfr' hap hn' hf' ha' hp'

/-- Application closure on original raw values. Both payload witnesses are
obtained from actual internal Program totality and eliminated internally. -/
theorem rawApplicationClosure (node leaf : Program 1)
    (arrow d e f a parent : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hn : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hf : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) parent)) := by
  apply programCases InternalUnpair.right (Fin.cons f Fin.elim0) _
  intro β j Delta fp hj hfp
  simp only [graph1Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hfp
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hn' := renameInto hn j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
    at har' hfl' hal' hn' hf' ha' hp'
  exact applicationClosureAtFunctionPayload node leaf (arrow.relabel j) (d.relabel j)
    (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) fp
    har' hfl' hal' hfp hn' hf' ha' hp'

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointSupportProof
