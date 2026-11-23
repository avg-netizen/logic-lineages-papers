module
public import LogicLineages.PersistentMarking.NumberedWindowOriginalSelectRootFieldsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelChecks
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSelectClosedRootUseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot)
open NumberedWindowInternalConstructorLowerLabelTargets (lowerLabel)
open NumberedWindowInternalConstructorLowerLabelChecks
  (exact_OriginalNumericLowerLabel exact_OriginalOpenLowerLabel)
open NumberedWindowOriginalSelectRootFieldsProof (exact_OriginalSelectRootFields)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode unpack)
open NumberedWindowRootDispatchAlgorithm (flagView)
open NumberedWindowAddressAlgorithm (contextView)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowOwnerAlgorithm (plan applyCopies)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem actualPredecessor (n : Nat) :
    Nonempty (Derivation B Γ
      (eqn (numeral (n+1)) (suc (numeral n)) ⊓ ltF (numeral n) (numeral (n+1)))) := by
  let v := (n+1) ::ᵥ n ::ᵥ List.Vector.nil
  have eval : evaluate lowerLabel v = 1 := by
    change evaluate lowerLabel ((n+1) ::ᵥ n ::ᵥ List.Vector.nil) = 1
    rw [exact_OriginalNumericLowerLabel] <;> simp
  have accepted := exact_NumeralGraph 2 lowerLabel v B α Γ
  have obs : (inputs v : Fin 2 → OTerm α) = ![numeral (n+1),numeral n] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
  rw [eval,obs] at accepted
  exact exact_OriginalOpenLowerLabel B α Γ (numeral (n+1)) (numeral n) accepted

/-- Original Select dispatch at held literal numeral inputs. Even for
arbitrary open Γ, expose the real physical selected fields and actual
object-level order via CPS; do not reflect arbitrary acceptance into a
meta-level fact. On the rejected case, original functionality supplies
an object contradiction instead. -/
theorem exact_OriginalClosedSelectRootUse (xs : Entries) (s : Settings) (p : Program 3)
    (fit : ActualRoot (root xs s) p)
    (src cert dst flag index domainCode : Nat) (goal : Formula α)
    (witness : unpackNode cert = some (2,[flag,index,domainCode]))
    (accepted : Nonempty (Derivation B Γ (programGraph p (suc z) ![numeral src,numeral cert,numeral dst])))
    (next : ∀ extra domains head result label base extras tape child,
      flagView flag = some extra → contextView domainCode = some domains →
      (syntaxBits src).1 = true → (syntaxBits dst).1 = true →
      unpackNode src = some (5,[head,result,label+1,base,extras]) →
      unpack (if extra then extras else base) = some tape → tape[index]? = some child →
      (annotations child).1 = (plan result domains).1 →
      dst = applyCopies head label base extras child (plan result domains).2 →
      Nonempty (Derivation B Γ
        (eqn (numeral (label+1)) (suc (numeral label)) ⊓ ltF (numeral label) (numeral (label+1)))) →
      Nonempty (Derivation B Γ goal)) :
    Nonempty (Derivation B Γ goal) := by
  cases good : root xs s src cert dst with
  | false =>
    let v := src ::ᵥ cert ::ᵥ dst ::ᵥ List.Vector.nil
    have zero : evaluate p v = 0 := by
      change evaluate p (src ::ᵥ cert ::ᵥ dst ::ᵥ List.Vector.nil) = 0
      rw [fit,good] <;> rfl
    have known := exact_NumeralGraph 3 p v B α Γ
    have obs : (inputs v : Fin 3 → OTerm α) = ![numeral src,numeral cert,numeral dst] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
    rw [zero,obs] at known
    obtain ⟨bad⟩ := valueUnique p (suc z) z
      (![numeral src,numeral cert,numeral dst] : Fin 3 → OTerm α) accepted known
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  | true =>
    obtain ⟨extra,domains,head,result,label,base,extras,tape,child,flagEq,domainEq,sx,sy,
      sourceEq,tapeEq,indexEq,typed,fold⟩ :=
      exact_OriginalSelectRootFields xs s src cert dst flag index domainCode witness good
    exact next extra domains head result label base extras tape child flagEq domainEq sx sy sourceEq
      tapeEq indexEq typed fold (actualPredecessor label)

#print axioms exact_OriginalClosedSelectRootUse
end LogicLineages.PersistentMarking.NumberedWindowInternalSelectClosedRootUseProof
