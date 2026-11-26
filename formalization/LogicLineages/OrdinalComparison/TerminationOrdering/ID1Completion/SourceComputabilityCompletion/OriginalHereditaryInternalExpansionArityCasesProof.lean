module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorArityProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalHereditaryInternalExpansionArityQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem oneFromTags (raw : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw ⊔ graph1 rawTag (numeral 4) raw))) :
 Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 apply orCases ht
 · intro Theta inc h
   exact arityTag1 (.projection 0) xs
     (unaryValue InternalUnpair.left (.projection 0) (numeral 1) raw xs h (projectionValue 0 xs))
 · intro Theta inc h
   exact arityTag4 (.projection 0) xs
     (unaryValue InternalUnpair.left (.projection 0) (numeral 4) raw xs h (projectionValue 0 xs))

theorem twoFromTags (raw : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw ⊔
   (graph1 rawTag (numeral 5) raw ⊔ graph1 rawTag (numeral 7) raw)))) :
 Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 apply orCases ht
 · intro Theta inc h
   exact arityTag2 (.projection 0) xs
     (unaryValue InternalUnpair.left (.projection 0) (numeral 2) raw xs h (projectionValue 0 xs))
 · intro Theta inc h
   apply orCases h
   · intro Xi inc2 h2
     exact arityTag5 (.projection 0) xs
       (unaryValue InternalUnpair.left (.projection 0) (numeral 5) raw xs h2 (projectionValue 0 xs))
   · intro Xi inc2 h2
     exact arityTag7 (.projection 0) xs
       (unaryValue InternalUnpair.left (.projection 0) (numeral 7) raw xs h2 (projectionValue 0 xs))

theorem childArityCases (input parameter : OTerm alpha) (psi : Formula alpha)
 (zero : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (arityOf (.projection 0)) (numeral 0) (input.relabel rho) (parameter.relabel rho))) →
   Nonempty (Derivation body Theta (psi.relabel rho)))
 (one : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (arityOf (.projection 0)) (numeral 1) (input.relabel rho) (parameter.relabel rho))) →
   Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 1) (input.relabel rho))) →
   Nonempty (Derivation body Theta (psi.relabel rho)))
 (two : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (arityOf (.projection 0)) (numeral 2) (input.relabel rho) (parameter.relabel rho))) →
   Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 2) (input.relabel rho))) →
   Nonempty (Derivation body Theta (psi.relabel rho)))
 : Nonempty (Derivation body Delta psi) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 apply programCases (arityOf (.projection 0)) xs psi
 intro beta rho Theta value hrho ha
 let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at ha
 have hv := arityViewQuery (.projection 0) (input.relabel rho) value xx (projectionValue 0 xx) ha
 apply orCases hv
 · intro Xi inc he
   apply zero beta rho Xi (fun f hf => inc _ (hrho f hf))
   exact outputTransport (arityOf (.projection 0)) value (numeral 0) xx
     (by simpa only [equalEqn] using he) (weakenProof ha inc)
 · intro Xi inc hn
   apply orCases hn
   · intro Omega inc2 hone
     have hinc : ∀ f ∈ Theta, f ∈ Omega := fun f hf => inc2 f (inc f hf)
     apply one beta rho Omega (fun f hf => hinc _ (hrho f hf))
     · exact outputTransport (arityOf (.projection 0)) value (numeral 1) xx
         (by simpa only [equalEqn] using andLeft hone) (weakenProof ha hinc)
     · exact oneFromTags (input.relabel rho) (andRight hone)
   · intro Omega inc2 htwo
     have hinc : ∀ f ∈ Theta, f ∈ Omega := fun f hf => inc2 f (inc f hf)
     apply two beta rho Omega (fun f hf => hinc _ (hrho f hf))
     · exact outputTransport (arityOf (.projection 0)) value (numeral 2) xx
         (by simpa only [equalEqn] using andLeft htwo) (weakenProof ha hinc)
     · exact twoFromTags (input.relabel rho) (andRight htwo)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
