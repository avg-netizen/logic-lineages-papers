module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (graph)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z sucSubst zSubst)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoordinateTargets NumberedWindowInternalPresentationTargets (data)
open NumberedWindowCheckerCoordinates (domain suppliedCertificate)
open SourceComputabilityFormulaSupportProof NumberedWindowComputabilityFormulaTargets (accepts)

private theorem domainProjection {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (p : Program 1) (c x : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (domain p) (suc z) ![c,x])) ↔
    Nonempty (Derivation body Γ (RawDomain p x)) := by
  let xs : Fin 2 → OTerm α := ![c,x]
  have project (j : Fin 1) : Nonempty (Derivation body Γ (programGraph (.projection 1) (![x] j) xs)) := by
    obtain rfl := Fin.eq_zero j
    exact projectionValue 1 xs
  exact ⟨fun h => compositionRecover p _ _ xs ![x] h project,
    fun h => compositionValue p _ _ xs ![x] h project⟩

private theorem carrierGraph {α : Type} (d : ID1Completion.SourcePresentation.Data) (odd : Bool)
    (c : Nat) (x : OTerm α) :
    carrier d odd c x = programGraph (carrierProgram d odd) (suc z) ![numeral c,x] := by
  unfold carrier ID1Completion.SourcePresentation.checkerFormula
  rw [ID1Completion.InternalGraphCompositionSyntaxProof.applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext j
    exact Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a)) j

theorem exact_DomainRules : DomainRules := by
  intro i j r d odd c body α Γ x
  rw [carrierGraph]
  cases odd
  · exact domainProjection i (numeral c) x
  · exact domainProjection j (numeral c) x

private theorem certProjection {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (p : Program 3) (c x y w : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (suppliedCertificate p) (suc z) ![c,x,y,w])) ↔
    Nonempty (Derivation body Γ (accepts p x w y)) := by
  let xs : Fin 4 → OTerm α := ![c,x,y,w]
  let slots : Fin 3 → Program 4 := Fin.cases (.projection 1) (Fin.cases (.projection 3) (fun _ => .projection 2))
  have project (j : Fin 3) : Nonempty (Derivation body Γ (programGraph (slots j) (![x,w,y] j) xs)) := by
    refine Fin.cases (projectionValue 1 xs) (fun k => ?_) j
    refine Fin.cases (projectionValue 3 xs) (fun l => ?_) k
    obtain rfl := Fin.eq_zero l
    exact projectionValue 2 xs
  exact ⟨fun h => compositionRecover p slots _ xs ![x,w,y] h project,
    fun h => compositionValue p slots _ xs ![x,w,y] h project⟩

theorem exact_CertificateRules : CertificateRules := by
  intro i j r d odd c body α Γ x y w
  cases odd
  · exact certProjection r (numeral c) x y w
  · exact certProjection d (numeral c) x y w

#print axioms exact_DomainRules
#print axioms exact_CertificateRules
end LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
