module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretation
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions TypedExtraDownsets

def Confined {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : Prop :=
  typesAllowed (fun υ => υ ∈ types I) q ∧ headsAllowed (fun f => f ∈ headList I) q

def ArgumentsConfined {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) {Γ ts : List Ty}
    (args : Arguments Symbol arity Γ ts) : Prop :=
  argumentTypesAllowed (fun υ => υ ∈ types I) args ∧ argumentsAllowed (fun f => f ∈ headList I) args

abbrev ConfinedTerm {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) :=
  {q : MarkedTerm Symbol arity Γ τ // Confined I q}

/-- Literal type-list membership extracted from existing occurrence confinement. -/
theorem argumentTypeList {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {Γ ts : List Ty}
    (args : Arguments Symbol arity Γ ts) (h : ArgumentsConfined I args) : ∀ τ ∈ ts,τ ∈ types I := by
  induction ts with
  | nil => simp
  | cons σ ts ih =>
    cases args with
    | cons q rest =>
      intro τ ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact FiniteQueryPrimitivesSupportProof.rootType q h.1.1
      · exact ih rest ⟨h.1.2,h.2.2⟩ τ ht

mutual
def buildTerm {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) :
    {Γ : List Ty} → {τ : Ty} → (q : MarkedTerm Symbol arity Γ τ) → Confined I q → PairedAction I Γ τ
  | _, _, .var v, _ => OriginalSpineActionsProof.variableAction v
  | _, _, .lam body, h => LambdaSpineActionsProof.lambdaAction body (buildTerm I body ⟨h.1.2.2,h.2⟩)
  | _, _, .ordinary f base, h => FunctionalSpineActionsProof.ordinaryAction ⟨f,h.2.1⟩
      (buildArguments I base ⟨h.1.2,h.2.2⟩)
  | _, _, .marked f τ base ts extras, h => FunctionalSpineActionsProof.markedAction ⟨f,h.2.1⟩ ⟨τ,h.1.1⟩
      (buildArguments I base ⟨h.1.2.1,h.2.2.1⟩) ts (argumentTypeList extras ⟨h.1.2.2,h.2.2.2⟩)
      (buildArguments I extras ⟨h.1.2.2,h.2.2.2⟩)
def buildArguments {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) :
    {Γ ts : List Ty} → (args : Arguments Symbol arity Γ ts) → ArgumentsConfined I args → ArgumentActions I Γ ts
  | _, _, .nil, _ => fun i => Fin.elim0 i
  | _, _, .cons q rest, h => fun i => Fin.cases (buildTerm I q ⟨h.1.1,h.2.1⟩)
      (buildArguments I rest ⟨h.1.2,h.2.2⟩) i
end

def action {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {τ : Ty}
    (q : ConfinedTerm I Γ τ) : PairedAction I Γ τ := buildTerm I q.val q.property

def interpret {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {τ : Ty}
    (q : ConfinedTerm I Γ τ) : Evaluate I Γ τ := (action q).evaluate

def scan {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {τ : Ty}
    (q : ConfinedTerm I Γ τ) : Scan I Γ τ := (action q).scan

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretation
