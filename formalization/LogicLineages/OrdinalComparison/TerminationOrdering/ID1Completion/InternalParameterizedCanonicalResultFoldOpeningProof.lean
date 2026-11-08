module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalApplicationStepPeelComponentsProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationValidityClosure
open InternalParameterizedCanonicalResultFold
open InternalParameterizedApplicationResultStack (wireP)
open InternalParameterizedApplicationResultStackWiringProof
open InternalParameterizedApplicationResultStackSyntaxProof (appendParameterOne)
open InternalCanonicalResultFoldOpening (rootDomain rootCodomain functionChild argumentChild)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem wireOneValue (P : Program 2) (selector : Program 1)
    (out parent parameter selected : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 P out selected parameter)))
    (hs : Nonempty (Derivation body Gamma (graph1 selector selected parent))) :
    Nonempty (Derivation body Gamma (graph2 (wireP P (fun _ : Fin 1 => selector)) out parent parameter)) := by
  apply wireValue P (fun _ : Fin 1 => selector) out parent parameter (Fin.cons selected Fin.elim0)
  · simpa only [appendParameterOne] using hp
  · intro i
    obtain rfl := Fin.eq_zero i
    exact hs

theorem wireOneRecover (P : Program 2) (selector : Program 1)
    (out parent parameter selected : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (graph2 (wireP P (fun _ : Fin 1 => selector)) out parent parameter)))
    (hs : Nonempty (Derivation body Gamma (graph1 selector selected parent))) :
    Nonempty (Derivation body Gamma (graph2 P out selected parameter)) := by
  have h := wireRecover P (fun _ : Fin 1 => selector) out parent parameter
    (Fin.cons selected Fin.elim0) hp (by
      intro i
      obtain rfl := Fin.eq_zero i
      exact hs)
  simpa only [appendParameterOne] using h

/-- The three original selectors are determined solely by the unchanged
application constructors, with no validity or semantic decoding premise. -/
theorem selectorGraphs (arrow d e fp ap fn arg parent : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent))) :
    Nonempty (Derivation body Gamma
      (graph1 functionChild fn parent ⊓
        (graph1 argumentChild arg parent ⊓ graph1 rootCodomain e parent))) := by
  let ch : Program 4 := pairOf (.projection 2) (.projection 3)
  let mid : Program 4 := pairOf (.projection 0) ch
  let pay : Program 4 := pairOf (two 4) mid
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases (![ch,mid,pay] : Fin 3 → Program 4) xs _
  intro β j ys Delta hj hq
  simp only [conjunctionRename,graph1Rename]
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm β := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hch := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hmid := binaryRecover InternalPairing.pairing (.projection 0) ch
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hpay := binaryRecover InternalPairing.pairing (two 4) mid
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have hparent := binaryRecover InternalPairing.pairing (.projection 1) pay
    (parent.relabel j) (e.relabel j) (ys 2) xx
    (andRight (andRight (andRight hc'))) (projectionValue 1 xx) (hq 2)
  let ss : Fin 1 → OTerm β := Fin.cons (parent.relabel j) Fin.elim0
  have fields := fieldsAtPairs (.projection 0) (parent.relabel j) (parent.relabel j)
    (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
    (projectionValue 0 ss) hch hmid hpay hparent
  have he := andLeft fields
  have hd := andLeft (andRight (andRight fields))
  have hfp := andLeft (andRight (andRight (andRight fields)))
  have hap := andRight (andRight (andRight (andRight fields)))
  have harrow := binaryValue InternalListCodec.consCode rootDomain rootCodomain
    (arrow.relabel j) (d.relabel j) (e.relabel j) ss (andLeft hc') hd he
  have hfn := binaryValue InternalPairing.pairing (consOf rootDomain rootCodomain)
    (InternalApplicationStepPeel.functionPayload (.projection 0))
    (fn.relabel j) (arrow.relabel j) (fp.relabel j) ss
    (andLeft (andRight hc')) harrow hfp
  have harg := binaryValue InternalPairing.pairing rootDomain
    (InternalApplicationStepPeel.argumentPayload (.projection 0))
    (arg.relabel j) (d.relabel j) (ap.relabel j) ss
    (andLeft (andRight (andRight hc'))) hd hap
  exact andIntro hfn (andIntro harg he)

theorem rootGuardRecover (data : Data) (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (validity data) (suc z) parent parameter ⊓
        (graph2 (validity data) (suc z) fn parameter ⊓
          (graph2 (validity data) (suc z) arg parameter ⊓
            graph2 data.member (suc z) e parameter)))) := by
  have hs := selectorGraphs arrow d e fp ap fn arg parent hc
  let xs : Fin 2 → OTerm α := Fin.cons parent (Fin.cons parameter Fin.elim0)
  have h1 := conjunctionRecover _ _ xs hg
  have h2 := conjunctionRecover _ _ xs (andRight h1)
  have h3 := conjunctionRecover _ _ xs (andRight h2)
  exact andIntro (andLeft h1)
    (andIntro (wireOneRecover (validity data) functionChild (suc z) parent parameter fn
      (andLeft h2) (andLeft hs))
      (andIntro (wireOneRecover (validity data) argumentChild (suc z) parent parameter arg
        (andLeft h3) (andLeft (andRight hs)))
        (wireOneRecover data.member rootCodomain (suc z) parent parameter e
          (andRight h3) (andRight (andRight hs)))))

theorem rootGuardValue (data : Data) (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) arg parameter)))
    (hm : Nonempty (Derivation body Gamma (graph2 data.member (suc z) e parameter))) :
    Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter)) := by
  have hs := selectorGraphs arrow d e fp ap fn arg parent hc
  let xs : Fin 2 → OTerm α := Fin.cons parent (Fin.cons parameter Fin.elim0)
  exact conjunctionAccept _ _ xs hv
    (conjunctionAccept _ _ xs
      (wireOneValue (validity data) functionChild (suc z) parent parameter fn hf (andLeft hs))
      (conjunctionAccept _ _ xs
        (wireOneValue (validity data) argumentChild (suc z) parent parameter arg ha (andLeft (andRight hs)))
        (wireOneValue data.member rootCodomain (suc z) parent parameter e hm (andRight (andRight hs)))))

theorem memberFromGuard (data : Data) (d e fp ap parent parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter))) :
    Nonempty (Derivation body Gamma (graph2 data.member (suc z) e parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons parent (Fin.cons parameter Fin.elim0)
  have h1 := conjunctionRecover _ _ xs hg
  have h2 := conjunctionRecover _ _ xs (andRight h1)
  have h3 := conjunctionRecover _ _ xs (andRight h2)
  have he := unaryValue InternalUnpair.left (.projection 0) e parent (Fin.cons parent Fin.elim0)
    (InternalCanonicalResultFoldInvariantApplicationSupportProof.packedLeft d e fp ap parent hp)
    (projectionValue 0 (Fin.cons parent Fin.elim0))
  exact wireOneRecover data.member rootCodomain (suc z) parent parameter e (andRight h3) he

theorem rawLeft (d e f a parent : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e parent)) :=
  InternalCanonicalResultFoldInvariantApplicationSupportProof.rawLeft d e f a parent hp

/-- Original Program totality obtains both payloads; the exact source
application closure then proves validity at the unchanged parameter. -/
theorem rawValidity (data : Data) (arrow d e f a parent parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hm : Nonempty (Derivation body Gamma (graph2 data.member (suc z) e parameter)))
    (hf : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) f parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) a parameter)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) parent parameter)) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
  let xs : Fin 2 → OTerm α := Fin.cons f (Fin.cons a Fin.elim0)
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [graph2Rename,sucRelabel,zRelabel]
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hm' := renameInto hm j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel] at har' hfl' hal' hm' hf' ha' hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm β := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (f.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have haright := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (a.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  have hc := andIntro har'
    (andIntro (reconstructPair (f.relabel j) (arrow.relabel j) (ys 0) hfl' hfr)
      (andIntro (reconstructPair (a.relabel j) (d.relabel j) (ys 1) hal' haright)
        (applicationForward (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j)
          (ys 0) (ys 1) (parent.relabel j) hfr haright hp')))
  exact InternalOriginalUniformDescentSelectionApplicationProof.sourceApplicationClosure data
    (arrow.relabel j) (d.relabel j) (e.relabel j) (ys 0) (ys 1)
    (f.relabel j) (a.relabel j) (parent.relabel j) (parameter.relabel j) hc hm' hf' ha'

theorem rawApplicationValue (d e f a raw parameter : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f a))) :
    Nonempty (Derivation body Gamma (programGraph rawApplicationAt raw ![d,e,f,a,parameter])) := by
  let xs : Fin 5 → OTerm α := ![d,e,f,a,parameter]
  apply compositionValue application ![.projection 0,.projection 1,.projection 2,.projection 3]
    raw xs ![d,e,f,a] hr
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q)))) i

theorem combineValue (data : Data) (d e f a raw out parameter : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f a)))
    (hd : Nonempty (Derivation body Gamma (graph2 (leaf data) out raw parameter))) :
    Nonempty (Derivation body Gamma (programGraph (combine data) out ![d,e,f,a,parameter])) := by
  let xs : Fin 5 → OTerm α := ![d,e,f,a,parameter]
  exact binaryValue (leaf data) rawApplicationAt (.projection 4) out raw parameter xs hd
    (rawApplicationValue d e f a raw parameter hr) (projectionValue 4 xs)

theorem combineRecover (data : Data) (d e f a raw out parameter : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f a)))
    (hc : Nonempty (Derivation body Gamma (programGraph (combine data) out ![d,e,f,a,parameter]))) :
    Nonempty (Derivation body Gamma (graph2 (leaf data) out raw parameter)) := by
  let xs : Fin 5 → OTerm α := ![d,e,f,a,parameter]
  exact binaryRecover (leaf data) rawApplicationAt (.projection 4) out raw parameter xs hc
    (rawApplicationValue d e f a raw parameter hr) (projectionValue 4 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
