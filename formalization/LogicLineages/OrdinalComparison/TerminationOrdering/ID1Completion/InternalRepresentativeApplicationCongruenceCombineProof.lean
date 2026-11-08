module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruencePayloadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceCombineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalRepresentativeFoldCalibration
open InternalRepresentativeTagSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem combineTag (old : InternalQuotientEdgeChecker.Data) (d e x arg out : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph4 (combine old) out d e x arg))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e out)) :=
  pairTagForward (.projection 1)
    (rightOf (.composition old.targetRepresentative (fun _ : Fin 1 => application))) out e
    (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons arg Fin.elim0)))) h
    (projectionValue 1 (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons arg Fin.elim0)))))

theorem packedApplicationTag (d e fp ap parent : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e parent)) :=
  pairTagForward (.projection 1)
    (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
    parent e (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) h
    (projectionValue 1 (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))))

/-- Preserve the concrete combine output when the two application graphs share
an output. The old representative and its right field are evaluated internally. -/
theorem combineAtApplication (old : InternalQuotientEdgeChecker.Data)
    (d e x y arg app out : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph4 application app d e x arg)))
    (hy : Nonempty (Derivation body Gamma (graph4 application app d e y arg)))
    (hc : Nonempty (Derivation body Gamma (graph4 (combine old) out d e x arg))) :
    Nonempty (Derivation body Gamma (graph4 (combine old) out d e y arg)) := by
  apply programCases old.targetRepresentative (Fin.cons app Fin.elim0) _
  intro β j Delta rep hj hrep
  simp only [consTermRename,emptyRename] at hrep
  rw [graph4Rename]
  have hx' := renameInto hx j Delta hj
  have hy' := renameInto hy j Delta hj
  have hc' := renameInto hc j Delta hj
  simp only [graph4Rename] at hx' hy' hc'
  have hrep' : Nonempty (Derivation body Delta
      (graph1 old.targetRepresentative rep (app.relabel j))) := hrep
  apply programCases InternalUnpair.right (Fin.cons rep Fin.elim0) _
  intro γ k Theta payload hk hright
  simp only [consTermRename,emptyRename] at hright
  rw [graph4Rename]
  have hx'' := renameInto hx' k Theta hk
  have hy'' := renameInto hy' k Theta hk
  have hc'' := renameInto hc' k Theta hk
  have hrep'' := renameInto hrep' k Theta hk
  simp only [graph4Rename,graph1Rename] at hx'' hy'' hc'' hrep''
  let xs : Fin 4 → OTerm γ := Fin.cons ((d.relabel j).relabel k)
    (Fin.cons ((e.relabel j).relabel k) (Fin.cons ((x.relabel j).relabel k)
      (Fin.cons ((arg.relabel j).relabel k) Fin.elim0)))
  let ys : Fin 4 → OTerm γ := Fin.cons ((d.relabel j).relabel k)
    (Fin.cons ((e.relabel j).relabel k) (Fin.cons ((y.relabel j).relabel k)
      (Fin.cons ((arg.relabel j).relabel k) Fin.elim0)))
  let p : Program 4 := .composition old.targetRepresentative (fun _ : Fin 1 => application)
  have hpx : Nonempty (Derivation body Theta (programGraph p (rep.relabel k) xs)) :=
    unaryValue old.targetRepresentative application (rep.relabel k)
      ((app.relabel j).relabel k) xs hrep'' hx''
  have hpy : Nonempty (Derivation body Theta (programGraph p (rep.relabel k) ys)) :=
    unaryValue old.targetRepresentative application (rep.relabel k)
      ((app.relabel j).relabel k) ys hrep'' hy''
  have hqx : Nonempty (Derivation body Theta (programGraph (rightOf p) payload xs)) :=
    unaryValue InternalUnpair.right p payload (rep.relabel k) xs hright hpx
  have hqy : Nonempty (Derivation body Theta (programGraph (rightOf p) payload ys)) :=
    unaryValue InternalUnpair.right p payload (rep.relabel k) ys hright hpy
  have hpair := binaryRecover InternalPairing.pairing (.projection 1) (rightOf p)
    ((out.relabel j).relabel k) ((e.relabel j).relabel k) payload xs hc''
    (projectionValue 1 xs) hqx
  exact binaryValue InternalPairing.pairing (.projection 1) (rightOf p)
    ((out.relabel j).relabel k) ((e.relabel j).relabel k) payload ys hpair
    (projectionValue 1 ys) hqy

/-- The original combine uses the function child only through its right payload. -/
theorem combinePayloadExtensionality (old : InternalQuotientEdgeChecker.Data)
    (d e x y arg xp ap out : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right xp x)))
    (hy : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right xp y)))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap arg)))
    (hc : Nonempty (Derivation body Gamma (graph4 (combine old) out d e x arg))) :
    Nonempty (Derivation body Gamma (graph4 (combine old) out d e y arg)) := by
  apply programCases application
    (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons arg Fin.elim0)))) _
  intro β j Delta app hj happ
  simp only [consTermRename,emptyRename] at happ
  rw [graph4Rename]
  have hx' := renameInto hx j Delta hj
  have hy' := renameInto hy j Delta hj
  have ha' := renameInto ha j Delta hj
  have hc' := renameInto hc j Delta hj
  simp only [graph1Rename,graph4Rename] at hx' hy' ha' hc'
  have happ' : Nonempty (Derivation body Delta
      (graph4 application app (d.relabel j) (e.relabel j) (x.relabel j) (arg.relabel j))) := happ
  have hpacked := applicationForward (d.relabel j) (e.relabel j) (x.relabel j)
    (arg.relabel j) (xp.relabel j) (ap.relabel j) app hx' ha' happ'
  have happy := applicationBackward (d.relabel j) (e.relabel j) (y.relabel j)
    (arg.relabel j) (xp.relabel j) (ap.relabel j) app hy' ha' hpacked
  exact combineAtApplication old (d.relabel j) (e.relabel j) (x.relabel j)
    (y.relabel j) (arg.relabel j) app (out.relabel j) happ' happy hc'

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceCombineProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceCombineProof
