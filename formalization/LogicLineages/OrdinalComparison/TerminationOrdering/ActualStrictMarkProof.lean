module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkLambdaProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation RecursiveComparison TypedObservationAccess SourceConstructorIteration ActualStrictMark FunctionalSpineActions OriginalSpineActions OrdinaryFunctionalValue LambdaObservationMatching LambdaSpineActions ActualStrictMarkSupportProof ActualStrictMarkLambdaProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem successfulBits (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (hq : Confined I q) (r : MarkedTerm Symbol arity Γ τ) (hr : Confined I r),strictMark q=some r →
    ∀ P (ρ : Environment I Γ P) o,readBit true (interpret ⟨q,hq⟩ (limit I above) P ρ) o=
      readBit false (interpret ⟨r,hr⟩ (limit I above) P ρ) o := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro hq r hr he; simp [strictMark] at he
  | lam body ih =>
    intro hq r hr he P ρ o
    cases hb : strictMark body with
    | none => simp [strictMark,hb] at he
    | some b =>
      simp only [strictMark,hb,Option.map_some] at he
      cases Option.some.inj he
      exact lambdaReads body b (buildTerm I body ⟨hq.1.2.2,hq.2⟩) (buildTerm I b ⟨hr.1.2.2,hr.2⟩) (limit I above)
        (ih ⟨hq.1.2.2,hq.2⟩ b ⟨hr.1.2.2,hr.2⟩ hb) P ρ o
  | ordinary f base ih =>
    intro hq r hr he P ρ o
    cases Option.some.inj he
    change readBit true (ordinaryValue (limit I above) ⟨f,hq.2.1⟩
      (evaluateArguments (buildArguments I base ⟨hq.1.2,hq.2.2⟩) (limit I above) P ρ)) o=
      readBit false ((limit I above).val ⟨f,hq.2.1⟩ ⟨headResult f,hq.1.1⟩ P
        ⟨evaluateArguments (buildArguments I base ⟨hq.1.2,hq.2.2⟩) (limit I above) P ρ,
          TypedExtraAppendProof.appendExtras (emptyExtras I P) []⟩) o
    rw [emptyAppend]
    exact ordinaryReads (limit I above) ⟨f,hq.2.1⟩ P _ hq.1.1 o
  | marked f output base ts extras ihb ihe => intro hq r hr he; simp [strictMark] at he
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem failedBits (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (hq : Confined I q),strictMark q=none → ∀ P (ρ : Environment I Γ P),VariablesStrictEmpty ρ →
    ∀ o,readBit true (interpret ⟨q,hq⟩ (limit I above) P ρ) o=false := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro hq he P ρ hρ o
    exact readFalse (ρ v) (hρ v) o
  | lam body ih =>
    intro hq he P ρ hρ o
    cases hb : strictMark body with
    | none =>
      exact readFalse _ (lambdaEmpty body (buildTerm I body ⟨hq.1.2.2,hq.2⟩) (limit I above)
        (ih ⟨hq.1.2.2,hq.2⟩ hb) P ρ hρ) o
    | some b => simp [strictMark,hb] at he
  | ordinary f base ih => intro hq he; simp [strictMark] at he
  | marked f output base ts extras ihb ihe =>
    intro hq he P ρ hρ o
    exact readFalse _ (markedEmpty above ⟨f,hq.2.1⟩ ⟨output,hq.1.1⟩ P
      (markedState ⟨f,hq.2.1⟩ (buildArguments I base ⟨hq.1.2.1,hq.2.2.1⟩) ts
        (argumentTypeList extras ⟨hq.1.2.2,hq.2.2.2⟩) (buildArguments I extras ⟨hq.1.2.2,hq.2.2.2⟩) (limit I above) P ρ)) o
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem markConfinement : ActualStrictMarkTargets.MarkConfinement := by
  intro Symbol inst arity I Γ τ q r he
  exact markConfined q.val q.property r he

theorem markBitEquality : ActualStrictMarkTargets.MarkBitEquality := by
  intro Symbol inst arity I above dec Γ τ q r hr he P ρ o
  exact successfulBits above q.val q.property r hr he P ρ o

theorem undefinedMarkFalse : ActualStrictMarkTargets.UndefinedMarkFalse := by
  intro Symbol inst arity I above dec Γ τ q he P ρ o hρ
  exact failedBits above q.val q.property he P ρ hρ o

theorem identityUndefinedMarkFalse : ActualStrictMarkTargets.IdentityUndefinedMarkFalse := by
  intro Symbol inst arity I above dec P τ q he o
  exact failedBits above q.val q.property he P (identity I P) (fun {_} v => variableEmpty v) o

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkProof
