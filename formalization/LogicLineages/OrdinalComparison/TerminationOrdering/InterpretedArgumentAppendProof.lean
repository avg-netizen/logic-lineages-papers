module
public import LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation TypedExtraDownsets TypedExtraAppend InterpretedArgumentAppend

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem confinedAppend {Γ xs ys : List Ty} (a : Arguments Symbol arity Γ xs) (b : Arguments Symbol arity Γ ys)
    (ha : ArgumentsConfined I a) (hb : ArgumentsConfined I b) : ArgumentsConfined I (appendArguments a b) := by
  induction xs with
  | nil => cases a; exact hb
  | cons τ xs ih =>
    cases a with
    | cons q rest =>
      have hr := ih rest ⟨ha.1.2,ha.2.2⟩
      exact ⟨⟨ha.1.1,hr.1⟩,⟨ha.2.1,hr.2⟩⟩

theorem packedCons {Γ types : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ)
    (rest : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I (.cons q rest))
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    packedValues (.cons q rest) ha M P ρ=
      ⟨⟨τ,FiniteQueryPrimitivesSupportProof.rootType q ha.1.1⟩,(buildTerm I q ⟨ha.1.1,ha.2.1⟩).evaluate M P ρ⟩ ::
      packedValues rest ⟨ha.1.2,ha.2.2⟩ M P ρ := by
  simp only [packedValues,packArguments,List.ofFn_succ]
  rfl

theorem appendConfinement : InterpretedArgumentAppendTargets.AppendConfinement := by
  intro Symbol inst arity I Γ xs ys a b ha hb
  exact confinedAppend a b ha hb

theorem orderedPackedAppend : InterpretedArgumentAppendTargets.OrderedPackedAppend := by
  intro Symbol inst arity I Γ xs ys a b ha hb hab M P ρ
  induction xs with
  | nil =>
    cases a
    rfl
  | cons τ xs ih =>
    cases a with
    | cons q rest =>
      simp only [appendArguments] at hab ⊢
      exact (packedCons q (appendArguments rest b) hab M P ρ).trans
        ((congrArg (List.cons _) (ih rest ⟨ha.1.2,ha.2.2⟩ ⟨hab.1.2,hab.2.2⟩)).trans
          (congrArg (fun l => l ++ packedValues b hb M P ρ) (packedCons q rest ha M P ρ).symm))

theorem downclosureAppend : InterpretedArgumentAppendTargets.DownclosureAppend := by
  intro Symbol inst arity I P E xs ys
  funext τ
  apply Subtype.ext
  apply Finset.ext
  intro a
  change a ∈ appendRaw (TypedExtraAppendProof.appendExtras E xs) ys τ ↔ a ∈ appendRaw E (xs++ys) τ
  rw [TypedExtraAppendProof.membershipCalibration Symbol inst arity I P (TypedExtraAppendProof.appendExtras E xs) ys ⟨τ,a⟩,
    TypedExtraAppendProof.membershipCalibration Symbol inst arity I P E (xs++ys) ⟨τ,a⟩]
  change (a ∈ appendRaw E xs τ ∨ ∃ p ∈ ys,PackedLE ⟨τ,a⟩ p) ↔ _
  rw [TypedExtraAppendProof.membershipCalibration Symbol inst arity I P E xs ⟨τ,a⟩]
  simp only [List.mem_append,or_and_right,exists_or,or_assoc]

end LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendProof
