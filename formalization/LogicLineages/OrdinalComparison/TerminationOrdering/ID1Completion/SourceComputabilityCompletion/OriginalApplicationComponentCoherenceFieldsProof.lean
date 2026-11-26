module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeel
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover both type fields and both payloads from the unchanged original packed
application constructor, without interpreting any child as a typed term. -/
theorem packedFields (d e fp ap parent : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Delta
      (graph1 (outerType (.projection 0)) e parent ⊓
        (graph1 (appDomain (.projection 0)) d parent ⊓
          (graph1 (functionPayload (.projection 0)) fp parent ⊓
            graph1 (argumentPayload (.projection 0)) ap parent)))) := by
  let children : Program 4 := pairOf (.projection 2) (.projection 3)
  let middle : Program 4 := pairOf (.projection 0) children
  let node : Program 4 := pairOf (two 4) middle
  let qs : Fin 3 → Program 4 := ![children,middle,node]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [conjunctionRename,graph1Rename]
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hm := binaryRecover InternalPairing.pairing (.projection 0) children
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 4) middle
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have hpar := binaryRecover InternalPairing.pairing (.projection 1) node
    (parent.relabel j) (e.relabel j) (ys 2) xx hp' (projectionValue 1 xx) (hq 2)
  let ss : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
  have fields := fieldsAtPairs (.projection 0) (parent.relabel j) (parent.relabel j)
    (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
    (projectionValue 0 ss) hc hm hn hpar
  exact andIntro (andLeft fields) (andRight (andRight fields))

/-- Original typed child selectors. These use the unchanged raw pair,
list-cons and unpair programs, rather than a replacement application AST. -/
def functionSelector : Program 1 :=
  pairOf (consOf (appDomain (.projection 0)) (outerType (.projection 0)))
    (functionPayload (.projection 0))
def argumentSelector : Program 1 :=
  pairOf (appDomain (.projection 0)) (argumentPayload (.projection 0))

/-- Restore the full original child codes from their original outer types.
Without these types, raw application is injective only on payloads. -/
theorem rawTypedFields (arrow d e fn arg parent : OTerm alpha)
    (har : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)))
    (hal : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d arg)))
    (hp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg))) :
    Nonempty (Derivation body Delta
      (graph1 (appDomain (.projection 0)) d parent ⊓
        (graph1 (outerType (.projection 0)) e parent ⊓
          (graph1 functionSelector fn parent ⊓ graph1 argumentSelector arg parent)))) := by
  let qs : Fin 2 → Program 4 := ![rightOf (.projection 2),rightOf (.projection 3)]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fn (Fin.cons arg Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [conjunctionRename,graph1Rename]
  have hp' := renameInto hp j Theta hj
  have har' := renameInto har j Theta hj
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  rw [graph4Rename] at hp'
  rw [graph2Rename] at har'
  rw [graph1Rename] at hfl' hal'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) Fin.elim0)))
  have hf := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (fn.relabel j) xx
    (hq 0) (projectionValue 2 xx)
  have ha := unaryRecover InternalUnpair.right (.projection 3) (ys 1) (arg.relabel j) xx
    (hq 1) (projectionValue 3 xx)
  have hpacked := applicationForward (d.relabel j) (e.relabel j) (fn.relabel j)
    (arg.relabel j) (ys 0) (ys 1) (parent.relabel j) hf ha hp'
  have fields := packedFields (d.relabel j) (e.relabel j)
    (ys 0) (ys 1) (parent.relabel j) hpacked
  have he := andLeft fields
  have hd := andLeft (andRight fields)
  have hfp := andLeft (andRight (andRight fields))
  have hap := andRight (andRight (andRight fields))
  let ss : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
  have ht := binaryValue InternalListCodec.consCode (appDomain (.projection 0))
    (outerType (.projection 0)) (arrow.relabel j) (d.relabel j) (e.relabel j) ss har' hd he
  have hfn := binaryValue InternalPairing.pairing
    (consOf (appDomain (.projection 0)) (outerType (.projection 0)))
    (functionPayload (.projection 0)) (fn.relabel j) (arrow.relabel j) (ys 0) ss
    (reconstructPair (fn.relabel j) (arrow.relabel j) (ys 0) hfl' hf) ht hfp
  have harg := binaryValue InternalPairing.pairing (appDomain (.projection 0))
    (argumentPayload (.projection 0)) (arg.relabel j) (d.relabel j) (ys 1) ss
    (reconstructPair (arg.relabel j) (d.relabel j) (ys 1) hal' ha) hd hap
  exact andIntro hd (andIntro he (andIntro hfn harg))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
