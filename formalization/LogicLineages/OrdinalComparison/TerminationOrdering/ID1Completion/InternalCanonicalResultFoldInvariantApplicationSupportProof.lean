module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalCanonicalResultFoldInvariant InternalCanonicalResultFoldOpening
open InternalApplicationValidityStack InternalApplicationValidityClosure
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The unchanged packed constructor has its literal codomain as left field. -/
theorem packedLeft (d e fp ap parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e parent)) := by
  let tail : Program 4 := pairOf (two 4)
    (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3)))
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply programCases tail xs _
  intro β j Delta value hj hv
  rw [graph1Rename]
  have hp' := renameInto hp j Delta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hv
  exact pairLeft (parent.relabel j) (e.relabel j) value
    (binaryRecover InternalPairing.pairing (.projection 1) tail
      (parent.relabel j) (e.relabel j) value
      (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
        (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0))))
      hp' (projectionValue (n := 4) 1 (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
        (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0))))) hv)

/-- Totality supplies both original child payloads; no typed input is needed. -/
theorem rawLeft (d e f a parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e parent)) := by
  let qs : Fin 2 → Program 4 := ![rightOf (.projection 2),rightOf (.projection 3)]
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0)))
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  rw [graph1Rename]
  have hp' := renameInto hp j Delta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  have hf := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (f.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0))))
    (hq 0) (projectionValue (n := 4) 2 (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)))))
  have ha := unaryRecover InternalUnpair.right (.projection 3) (ys 1) (a.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0))))
    (hq 1) (projectionValue (n := 4) 3 (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)))))
  exact packedLeft (d.relabel j) (e.relabel j) (ys 0) (ys 1) (parent.relabel j)
    (applicationForward (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j)
      (ys 0) (ys 1) (parent.relabel j) hf ha hp')

/-- Membership is recovered from G at the original parent, never assumed. -/
theorem memberFromGuard (V member : Program 1) (d e fp ap parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hg : Nonempty (Derivation body Gamma (graph1 (rootGuard V member) (suc z) parent))) :
    Nonempty (Derivation body Gamma (graph1 member (suc z) e)) := by
  let xs : Fin 1 → OTerm α := Fin.cons parent Fin.elim0
  have h1 := conjunctionRecover _ _ xs hg
  have h2 := conjunctionRecover _ _ xs (andRight h1)
  have h3 := conjunctionRecover _ _ xs (andRight h2)
  have he := unaryValue InternalUnpair.left (.projection 0) e parent xs
    (packedLeft d e fp ap parent hp) (projectionValue 0 xs)
  exact unaryRecover member rootCodomain (suc z) e xs (andRight h3) he

/-- Close BOTH original recursive validators at the actual raw output. -/
theorem rawValidity (old : InternalOriginalStepGuard.Data) (member : Program 1)
    (arrow d e f a raw : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hm : Nonempty (Derivation body Gamma (graph1 member (suc z) e)))
    (hf : Nonempty (Derivation body Gamma (graph1 (validity old member) (suc z) f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (validity old member) (suc z) a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application raw d e f a))) :
    Nonempty (Derivation body Gamma (graph1 (validity old member) (suc z) raw)) := by
  have hfs := conjunctionRecover _ _ (Fin.cons f Fin.elim0) hf
  have has := conjunctionRecover _ _ (Fin.cons a Fin.elim0) ha
  have ht := InternalApplicationValidityClosureEndpointSupportProof.rawApplicationClosure
    (InternalLessThan.constantOne 1) old.targetValid arrow d e f a raw har hfl hal
    (InternalLessThanSupportProof.oneConstantValue (Fin.cons e Fin.elim0))
    (andLeft hfs) (andLeft has) hp
  have hu := InternalApplicationValidityClosureEndpointSupportProof.rawApplicationClosure
    member old.sourceValid arrow d e f a raw har hfl hal hm (andRight hfs) (andRight has) hp
  exact conjunctionAccept _ _ (Fin.cons raw Fin.elim0) ht hu

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
