module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationResultStack
open InternalParameterizedApplicationResultStackSyntaxProof InternalParameterizedApplicationResultStackTargets
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem liftValue (P : Program 1) (out value parameter : OTerm α)
    (hg : Nonempty (Derivation body Gamma (graph1 P out value))) :
    Nonempty (Derivation body Gamma (graph2 (liftP P) out value parameter)) := by
  apply compositionValue P (fun _ : Fin 1 => .projection (0 : Fin 2)) out
    (Fin.cons value (Fin.cons parameter Fin.elim0)) (Fin.cons value Fin.elim0) hg
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (n := 2) 0 (Fin.cons value (Fin.cons parameter Fin.elim0))

theorem liftRecover (P : Program 1) (out value parameter : OTerm α)
    (hg : Nonempty (Derivation body Gamma (graph2 (liftP P) out value parameter))) :
    Nonempty (Derivation body Gamma (graph1 P out value)) := by
  apply compositionRecover P (fun _ : Fin 1 => .projection (0 : Fin 2)) out
    (Fin.cons value (Fin.cons parameter Fin.elim0)) (Fin.cons value Fin.elim0) hg
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (n := 2) 0 (Fin.cons value (Fin.cons parameter Fin.elim0))

/-- Every component of the literal appended argument vector has its actual graph. -/
theorem wireArguments {n : Nat} (selectors : Fin n → Program 1)
    (state parameter : OTerm α) (values : Fin n → OTerm α)
    (hs : ∀ i, Nonempty (Derivation body Gamma (graph1 (selectors i) (values i) state))) :
    ∀ i, Nonempty (Derivation body Gamma
      (programGraph (appendParameter (fun k => liftP (selectors k)) (.projection (1 : Fin 2)) i)
        (appendParameter values parameter i) (Fin.cons state (Fin.cons parameter Fin.elim0)))) := by
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [appendParameterLast]
    exact projectionValue (n := 2) 1 (Fin.cons state (Fin.cons parameter Fin.elim0))
  · simp only [appendParameterCastSucc]
    exact liftValue (selectors k) (values k) state parameter (hs k)

theorem wireValue {n : Nat} (P : Program (n+1)) (selectors : Fin n → Program 1)
    (out state parameter : OTerm α) (values : Fin n → OTerm α)
    (hg : Nonempty (Derivation body Gamma (programGraph P out (appendParameter values parameter))))
    (hs : ∀ i, Nonempty (Derivation body Gamma (graph1 (selectors i) (values i) state))) :
    Nonempty (Derivation body Gamma (graph2 (wireP P selectors) out state parameter)) :=
  compositionValue P _ out (Fin.cons state (Fin.cons parameter Fin.elim0))
    (appendParameter values parameter) hg (wireArguments selectors state parameter values hs)

theorem wireRecover {n : Nat} (P : Program (n+1)) (selectors : Fin n → Program 1)
    (out state parameter : OTerm α) (values : Fin n → OTerm α)
    (hg : Nonempty (Derivation body Gamma (graph2 (wireP P selectors) out state parameter)))
    (hs : ∀ i, Nonempty (Derivation body Gamma (graph1 (selectors i) (values i) state))) :
    Nonempty (Derivation body Gamma (programGraph P out (appendParameter values parameter))) :=
  compositionRecover P _ out (Fin.cons state (Fin.cons parameter Fin.elim0))
    (appendParameter values parameter) hg (wireArguments selectors state parameter values hs)

theorem actualOriginalParameterizedApplicationResultStackLift :
    ActualOriginalParameterizedApplicationResultStackLift := by
  intro body P α Gamma out value parameter
  obtain ⟨hf⟩ := liftRecover (body := body)
    (Gamma := graph2 (liftP P) out value parameter :: Gamma) P out value parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := liftValue (body := body)
    (Gamma := graph1 P out value :: Gamma) P out value parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalParameterizedApplicationResultStackWiring :
    ActualOriginalParameterizedApplicationResultStackWiring := by
  intro body n P selectors α Gamma out state parameter values hs
  have hs' (phi : Formula α) (i : Fin n) :
      Nonempty (Derivation body (phi :: Gamma) (graph1 (selectors i) (values i) state)) := by
    obtain ⟨h⟩ := hs i
    exact ⟨Derivation.weakening (fun q hq => List.mem_cons_of_mem phi hq) h⟩
  obtain ⟨hf⟩ := wireRecover (body := body)
    (Gamma := graph2 (wireP P selectors) out state parameter :: Gamma)
    P selectors out state parameter values ⟨Derivation.hypothesis List.mem_cons_self⟩ (hs' _)
  obtain ⟨hb⟩ := wireValue (body := body)
    (Gamma := programGraph P out (appendParameter values parameter) :: Gamma)
    P selectors out state parameter values ⟨Derivation.hypothesis List.mem_cons_self⟩ (hs' _)
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
