module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalListCodecSupportProof OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanDefinitions
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph scan decorate
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (graph5Rename)

theorem scanCases (count role typ raw jobs : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (previous value singleton : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph5 scan previous (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j))) →
      Nonempty (Derivation body Theta
        (graph5 cell value (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j))) →
      Nonempty (Derivation body Theta (consGraph singleton value z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let single : Program 5 := .composition InternalListCodec.consCode
    ![cell,InternalAcceptance.constantZero 5]
  let qs : Fin 3 → Program 5 := ![scan,cell,single]
  let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  let xx : Fin 5 → OTerm beta := Fin.cons (count.relabel j)
    (Fin.cons (role.relabel j) (Fin.cons (typ.relabel j) (Fin.cons (raw.relabel j) (Fin.cons (jobs.relabel j) Fin.elim0))))
  have he : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
  rw [he] at hq
  have hz := InternalRawListRecursionSupportProof.constantZero (body := body) (Gamma := Theta) xx
  have hc := binaryRecover InternalListCodec.consCode cell (InternalAcceptance.constantZero 5)
    (ys 2) (ys 1) z xx (hq 2) (hq 1) hz
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj (hq 0) (hq 1) hc

theorem scanAppendRecover (count previous role typ raw jobs mark singleton output : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 scan previous count role typ raw jobs)))
 (hs : Nonempty (Derivation body Delta (graph5 scan output (suc count) role typ raw jobs)))
 (hm : Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)))
 (hc : Nonempty (Derivation body Delta (consGraph singleton mark z))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output previous singleton)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons count (Fin.cons jobs Fin.elim0)
 apply programCases InternalRawListRecursion.lookup xs _
 intro beta rho Theta rawChild hrho hlookup
 simp only [graph2Rename]
 let xx : Fin 2 → OTerm beta := Fin.cons (count.relabel rho) (Fin.cons (jobs.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hlookup
 have hp' := renameInto hp rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 simp only [graph5Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hp' hs' hm'
 rw [InternalListCodecSupportProof.consGraphRename] at hc'
 simp only [InternalTagArithmeticSyntaxProof.zRelabel] at hc'
 exact SixSol20261113.Context.NarrowScanAppendProof.scanAppendAtLookup (count.relabel rho) (previous.relabel rho) (role.relabel rho)
   (typ.relabel rho) (raw.relabel rho) (jobs.relabel rho) (mark.relabel rho)
   (singleton.relabel rho) (output.relabel rho) rawChild hp' hs' hm' hc' hlookup

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanQueries
