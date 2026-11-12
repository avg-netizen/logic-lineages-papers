module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalPackedProof
open OriginalLambdaTraversalInternalSubstitutionProof OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open InternalApplicationStepPeelSupportProof (andLeft)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal graph substitution relates the packed application node to the
original raw constructor without assigning either child's discarded type. -/
theorem rawApplicationNode (d e fp ap raw : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph3 applicationConstructor raw d fp ap))) :
    Nonempty (Derivation body Delta
      (programGraph (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
        raw (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))))) := by
  let gs : Fin 3 → Program 4 := ![.projection 0,.projection 2,.projection 3]
  have sub : Substitutes gs applicationConstructor
      (pairOf (constant 4 2) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3)))) :=
    pairSubstitution (constantSubstitution gs 2)
      (pairSubstitution (Substitutes.projection 0)
        (pairSubstitution (Substitutes.projection 1) (Substitutes.projection 2)))
  apply (substitutionGraph sub (Fin.cons d (Fin.cons fp (Fin.cons ap Fin.elim0)))
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) raw ?_).mp hr
  intro i
  let ys : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  exact Fin.cases (projectionValue (0 : Fin 4) ys) (Fin.cases (projectionValue (2 : Fin 4) ys)
    (Fin.cases (projectionValue (3 : Fin 4) ys) (fun q => Fin.elim0 q))) i

theorem packedAtRaw (parent d e fp ap raw : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph3 applicationConstructor raw d fp ap)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent e raw))) :
    Nonempty (Derivation body Delta (graph4 packedApplication parent d e fp ap)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  exact binaryValue InternalPairing.pairing (.projection 1)
    (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
    parent e raw xs hp (projectionValue 1 xs) (rawApplicationNode d e fp ap raw hr)

theorem rawAtPacked (parent d e fp ap raw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 packedApplication parent d e fp ap)))
    (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw parent))) :
    Nonempty (Derivation body Delta (graph3 applicationConstructor raw d fp ap)) := by
  apply programCases applicationConstructor (Fin.cons d (Fin.cons fp (Fin.cons ap Fin.elim0))) _
  intro beta j Theta actual hj ha
  rw [graph3Rename]
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hraw j Theta hj
  rw [graph4Rename] at hp'
  rw [graph1Rename] at hr'
  simp only [consTermRename,emptyRename] at ha
  let xs : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have pair := binaryRecover InternalPairing.pairing (.projection 1)
    (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
    (parent.relabel j) (e.relabel j) actual xs hp' (projectionValue 1 xs)
    (rawApplicationNode (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) actual ha)
  have he := valueUnique InternalUnpair.right actual (raw.relabel j)
    (Fin.cons (parent.relabel j) Fin.elim0) (pairRight (parent.relabel j) (e.relabel j) actual pair) hr'
  exact outputTransport applicationConstructor actual (raw.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0))) he ha

/-- Supplied actual type graph is copied; no type is inferred from an app. -/
theorem eraseTypeCopy (packed out typ erasedType cutoff : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ packed)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw out erasedType cutoff packed))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ out)) := by
  let raw : Program 3 := rightOf (.projection 2)
  let transformed : Program 3 := .composition eraseRaw ![.projection 0,.projection 1,raw]
  let qs : Fin 2 → Program 3 := ![raw,transformed]
  let xs : Fin 3 → OTerm alpha := Fin.cons erasedType (Fin.cons cutoff (Fin.cons packed Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have ht' := renameInto ht j Theta hj
  have he' := renameInto he j Theta hj
  rw [graph1Rename] at ht'
  rw [graph3Rename] at he'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 3 → OTerm beta := Fin.cons (erasedType.relabel j) (Fin.cons (cutoff.relabel j) (Fin.cons (packed.relabel j) Fin.elim0))
  have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (packed.relabel j) xx (hq 0) (projectionValue 2 xx)
  have htrans : Nonempty (Derivation body Theta (graph3 eraseRaw (ys 1) (erasedType.relabel j) (cutoff.relabel j) (ys 0))) := by
    apply compositionRecover eraseRaw ![.projection 0,.projection 1,raw] (ys 1) xx
      (Fin.cons (erasedType.relabel j) (Fin.cons (cutoff.relabel j) (Fin.cons (ys 0) Fin.elim0))) (hq 1)
    intro i
    exact Fin.cases (projectionValue 0 xx) (Fin.cases (projectionValue 1 xx)
      (Fin.cases (hq 0) (fun q => Fin.elim0 q))) i
  have hp := reconstructPair (packed.relabel j) (typ.relabel j) (ys 0) ht' hr
  exact pairLeft (out.relabel j) (typ.relabel j) (ys 1)
    (erasePackedForward (packed.relabel j) (out.relabel j) (typ.relabel j) (ys 0) (ys 1)
      (erasedType.relabel j) (cutoff.relabel j) hp htrans he')

/-- Original application geometry commutes with literal packed erasure.
Only child payloads are used; discarded child types are never invented. -/
theorem applicationErasure (parent d e fn arg parentE fnE argE erasedType cutoff : OTerm alpha)
    (hApp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg)))
    (hParentErase : Nonempty (Derivation body Delta (graph3 erasePackedRaw parentE erasedType cutoff parent)))
    (hFnErase : Nonempty (Derivation body Delta (graph3 erasePackedRaw fnE erasedType cutoff fn)))
    (hArgErase : Nonempty (Derivation body Delta (graph3 erasePackedRaw argE erasedType cutoff arg))) :
    Nonempty (Derivation body Delta (graph4 application parentE d e fnE argE)) := by
  let pr : Program 5 := rightOf (.projection 0)
  let ft : Program 5 := leftOf (.projection 1)
  let fr : Program 5 := rightOf (.projection 1)
  let argType : Program 5 := leftOf (.projection 2)
  let ar : Program 5 := rightOf (.projection 2)
  let pe : Program 5 := .composition eraseRaw ![.projection 3,.projection 4,pr]
  let fe : Program 5 := .composition eraseRaw ![.projection 3,.projection 4,fr]
  let ae : Program 5 := .composition eraseRaw ![.projection 3,.projection 4,ar]
  let qs : Fin 8 → Program 5 := ![pr,ft,fr,argType,ar,pe,fe,ae]
  let xs : Fin 5 → OTerm alpha := Fin.cons parent (Fin.cons fn (Fin.cons arg
    (Fin.cons erasedType (Fin.cons cutoff Fin.elim0))))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph4Rename]
  have happ := renameInto hApp j Theta hj
  have hpe := renameInto hParentErase j Theta hj
  have hfe := renameInto hFnErase j Theta hj
  have hae := renameInto hArgErase j Theta hj
  rw [graph4Rename] at happ
  rw [graph3Rename] at hpe hfe hae
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 5 → OTerm beta := Fin.cons (parent.relabel j) (Fin.cons (fn.relabel j)
    (Fin.cons (arg.relabel j) (Fin.cons (erasedType.relabel j) (Fin.cons (cutoff.relabel j) Fin.elim0))))
  have hpr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (parent.relabel j) xx (hq 0) (projectionValue 0 xx)
  have hft := unaryRecover InternalUnpair.left (.projection 1) (ys 1) (fn.relabel j) xx (hq 1) (projectionValue 1 xx)
  have hfr := unaryRecover InternalUnpair.right (.projection 1) (ys 2) (fn.relabel j) xx (hq 2) (projectionValue 1 xx)
  have hat := unaryRecover InternalUnpair.left (.projection 2) (ys 3) (arg.relabel j) xx (hq 3) (projectionValue 2 xx)
  have har := unaryRecover InternalUnpair.right (.projection 2) (ys 4) (arg.relabel j) xx (hq 4) (projectionValue 2 xx)
  have hper := ternaryRecover eraseRaw (.projection 3) (.projection 4) pr (ys 5)
    (erasedType.relabel j) (cutoff.relabel j) (ys 0) xx (hq 5) (projectionValue 3 xx) (projectionValue 4 xx) (hq 0)
  have hfer := ternaryRecover eraseRaw (.projection 3) (.projection 4) fr (ys 6)
    (erasedType.relabel j) (cutoff.relabel j) (ys 2) xx (hq 6) (projectionValue 3 xx) (projectionValue 4 xx) (hq 2)
  have haer := ternaryRecover eraseRaw (.projection 3) (.projection 4) ar (ys 7)
    (erasedType.relabel j) (cutoff.relabel j) (ys 4) xx (hq 7) (projectionValue 3 xx) (projectionValue 4 xx) (hq 4)
  have hpacked := InternalApplicationCertificateConstructorsSupportProof.applicationForward
    (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j) (ys 2) (ys 4) (parent.relabel j) hfr har happ
  have hfields := OriginalApplicationComponentCoherenceFieldsProof.packedFields
    (d.relabel j) (e.relabel j) (ys 2) (ys 4) (parent.relabel j) hpacked
  have hpt : Nonempty (Derivation body Theta (graph1 InternalUnpair.left (e.relabel j) (parent.relabel j))) := by
    have h := andLeft hfields
    exact unaryRecover InternalUnpair.left (.projection 0) (e.relabel j) (parent.relabel j)
      (Fin.cons (parent.relabel j) Fin.elim0) h
      (projectionValue (0 : Fin 1) (Fin.cons (parent.relabel j) Fin.elim0))
  have hp := reconstructPair (parent.relabel j) (e.relabel j) (ys 0) hpt hpr
  have hf := reconstructPair (fn.relabel j) (ys 1) (ys 2) hft hfr
  have ha := reconstructPair (arg.relabel j) (ys 3) (ys 4) hat har
  have hpo := erasePackedForward (parent.relabel j) (parentE.relabel j) (e.relabel j) (ys 0) (ys 5)
    (erasedType.relabel j) (cutoff.relabel j) hp hper hpe
  have hfo := erasePackedForward (fn.relabel j) (fnE.relabel j) (ys 1) (ys 2) (ys 6)
    (erasedType.relabel j) (cutoff.relabel j) hf hfer hfe
  have hao := erasePackedForward (arg.relabel j) (argE.relabel j) (ys 3) (ys 4) (ys 7)
    (erasedType.relabel j) (cutoff.relabel j) ha haer hae
  have hraw := rawAtPacked (parent.relabel j) (d.relabel j) (e.relabel j) (ys 2) (ys 4) (ys 0) hpacked hpr
  have hrawOut := OriginalRawSyntaxTransportInternalFoldApplicationProof.applicationForward .erase
    (ys 0) (ys 5) (erasedType.relabel j) (cutoff.relabel j) (d.relabel j)
    (ys 2) (ys 4) (ys 6) (ys 7) hraw hfer haer hper
  exact InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    (d.relabel j) (e.relabel j) (fnE.relabel j) (argE.relabel j) (ys 6) (ys 7) (parentE.relabel j)
    (pairRight (fnE.relabel j) (ys 1) (ys 6) hfo) (pairRight (argE.relabel j) (ys 3) (ys 7) hao)
    (packedAtRaw (parentE.relabel j) (d.relabel j) (e.relabel j) (ys 6) (ys 7) (ys 5) hrawOut hpo)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
