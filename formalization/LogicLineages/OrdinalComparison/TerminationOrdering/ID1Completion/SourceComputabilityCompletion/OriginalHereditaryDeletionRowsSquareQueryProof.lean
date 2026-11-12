module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem coordinateCases (gamma i j upper lower c : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
 (a b u l ul lu xl xr pl pr : OTerm beta),
 (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup a (i.relabel rho) (gamma.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup b (suc (j.relabel rho)) (gamma.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 deleteAt u (suc (j.relabel rho)) (gamma.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 deleteAt l (i.relabel rho) (gamma.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 deleteAt ul (i.relabel rho) u)) →
 Nonempty (Derivation body Theta (graph2 deleteAt lu (j.relabel rho) l)) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw xl a (i.relabel rho) (upper.relabel rho))) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw xr b (j.relabel rho) (lower.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing pl (c.relabel rho) ul)) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing pr (c.relabel rho) lu)) →
 Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let k : Program 6 := .composition .succ (fun _ : Fin 1 => .projection 2)
 let a : Program 6 := .composition InternalRawListRecursion.lookup ![.projection 1,.projection 0]
 let b : Program 6 := .composition InternalRawListRecursion.lookup ![k,.projection 0]
 let u : Program 6 := .composition deleteAt ![k,.projection 0]
 let l : Program 6 := .composition deleteAt ![.projection 1,.projection 0]
 let ul : Program 6 := .composition deleteAt ![.projection 1,u]
 let lu : Program 6 := .composition deleteAt ![.projection 2,l]
 let xl : Program 6 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![a,.projection 1,.projection 3]
 let xr : Program 6 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![b,.projection 2,.projection 4]
 let pl : Program 6 := .composition InternalPairing.pairing ![.projection 5,ul]
 let pr : Program 6 := .composition InternalPairing.pairing ![.projection 5,lu]
 let qs : Fin 10 → Program 6 := ![a,b,u,l,ul,lu,xl,xr,pl,pr]
 let xs : Fin 6 → OTerm alpha := ![gamma,i,j,upper,lower,c]
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 6 → OTerm beta := ![gamma.relabel rho,i.relabel rho,j.relabel rho,upper.relabel rho,lower.relabel rho,c.relabel rho]
 have he : (fun t => (xs t).relabel rho) = xx := by
  funext t
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun z => Fin.elim0 z)))))) t
 rw [he] at hq
 have hk : Nonempty (Derivation body Theta (programGraph k (suc (j.relabel rho)) xx)) := by
  apply unaryValue .succ (.projection 2) (suc (j.relabel rho)) (j.relabel rho) xx
  · exact InternalControlGraphSupportProof.successorValue (Fin.cons (j.relabel rho) Fin.elim0)
  · exact projectionValue 2 xx
 have ha := binaryRecover InternalRawListRecursion.lookup (.projection 1) (.projection 0) (ys 0) (i.relabel rho) (gamma.relabel rho) xx (hq 0) (projectionValue 1 xx) (projectionValue 0 xx)
 have hb := binaryRecover InternalRawListRecursion.lookup k (.projection 0) (ys 1) (suc (j.relabel rho)) (gamma.relabel rho) xx (hq 1) hk (projectionValue 0 xx)
 have hu := binaryRecover deleteAt k (.projection 0) (ys 2) (suc (j.relabel rho)) (gamma.relabel rho) xx (hq 2) hk (projectionValue 0 xx)
 have hl := binaryRecover deleteAt (.projection 1) (.projection 0) (ys 3) (i.relabel rho) (gamma.relabel rho) xx (hq 3) (projectionValue 1 xx) (projectionValue 0 xx)
 have hul := binaryRecover deleteAt (.projection 1) u (ys 4) (i.relabel rho) (ys 2) xx (hq 4) (projectionValue 1 xx) (hq 2)
 have hlu := binaryRecover deleteAt (.projection 2) l (ys 5) (j.relabel rho) (ys 3) xx (hq 5) (projectionValue 2 xx) (hq 3)
 have hxl := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw a (.projection 1) (.projection 3) (ys 6) (ys 0) (i.relabel rho) (upper.relabel rho) xx (hq 6) (hq 0) (projectionValue 1 xx) (projectionValue 3 xx)
 have hxr := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw b (.projection 2) (.projection 4) (ys 7) (ys 1) (j.relabel rho) (lower.relabel rho) xx (hq 7) (hq 1) (projectionValue 2 xx) (projectionValue 4 xx)
 have hpl := binaryRecover InternalPairing.pairing (.projection 5) ul (ys 8) (c.relabel rho) (ys 4) xx (hq 8) (projectionValue 5 xx) (hq 4)
 have hpr := binaryRecover InternalPairing.pairing (.projection 5) lu (ys 9) (c.relabel rho) (ys 5) xx (hq 9) (projectionValue 5 xx) (hq 5)
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) hrho ha hb hu hl hul hlu hxl hxr hpl hpr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareQueryProof
