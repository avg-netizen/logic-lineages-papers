module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallArgsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope
  (hopGood hopTarget hopSource hopWitness hopRawTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (hopCertified z suc)
open NumberedWindowInternalSparsePathAdvance
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev At4 (body : Positive (Fin 1)) (Γ : List (Formula α)) (xs : Fin 4 → OTerm α)
    (p : Program 4) (out : OTerm α) := Nonempty (Derivation body Γ (programGraph p out xs))

def LiftedReports (body : Positive (Fin 1)) (Γ : List (Formula α))
    (xs : Fin 4 → OTerm α) (t q w r : OTerm α) : Prop :=
  At4 body Γ xs (atHop hopGood) (suc z) ∧
    (At4 body Γ xs (atHop hopTarget) t ∧
      (At4 body Γ xs (atHop hopSource) q ∧
        (At4 body Γ xs (atHop hopWitness) w ∧ At4 body Γ xs (atHop hopRawTarget) r)))

theorem liftReports (c ty s h t q w r : OTerm α)
    (reports : Nonempty (Derivation body Γ (hopCertified h t q w r))) :
    LiftedReports body Γ (coords c ty s h) t q w r := by
  obtain ⟨reports⟩ := reports
  have tqr := Derivation.conjunctionRight reports
  have qwr := Derivation.conjunctionRight tqr
  have wr := Derivation.conjunctionRight qwr
  exact ⟨atHopIntro hopGood (suc z) c ty s h ⟨Derivation.conjunctionLeft reports⟩,
     atHopIntro hopTarget t c ty s h ⟨Derivation.conjunctionLeft tqr⟩,
     atHopIntro hopSource q c ty s h ⟨Derivation.conjunctionLeft qwr⟩,
     atHopIntro hopWitness w c ty s h ⟨Derivation.conjunctionLeft wr⟩,
     atHopIntro hopRawTarget r c ty s h ⟨Derivation.conjunctionRight wr⟩⟩

private theorem rawArgs (c ty s h q w r : OTerm α)
    (hq : At4 body Γ (coords c ty s h) (atHop hopSource) q)
    (hw : At4 body Γ (coords c ty s h) (atHop hopWitness) w)
    (hr : At4 body Γ (coords c ty s h) (atHop hopRawTarget) r) :
    ∀ i : Fin 5, At4 body Γ (coords c ty s h)
      ((![.projection 0,.projection 1,atHop hopSource,atHop hopWitness,atHop hopRawTarget] :
        Fin 5 → Program 4) i) ((![c,ty,q,w,r] : Fin 5 → OTerm α) i) := by
  let xs := coords c ty s h
  intro i
  exact Fin.cases (projectionValue (0 : Fin 4) xs)
    (Fin.cases (projectionValue (1 : Fin 4) xs)
      (Fin.cases hq (Fin.cases hw (Fin.cases hr (fun u => Fin.elim0 u))))) i

theorem rawIntro (raw : Program 5) (c ty s h t q w r : OTerm α)
    (reports : LiftedReports body Γ (coords c ty s h) t q w r)
    (check : Nonempty (Derivation body Γ (programGraph raw (suc z) ![c,ty,q,w,r]))) :
    At4 body Γ (coords c ty s h) (rawCall raw) (suc z) :=
  compositionValue raw ![.projection 0,.projection 1,atHop hopSource,atHop hopWitness,atHop hopRawTarget]
    (suc z) (coords c ty s h) ![c,ty,q,w,r] check
    (rawArgs c ty s h q w r reports.2.2.1 reports.2.2.2.1 reports.2.2.2.2)

theorem rawRead (raw : Program 5) (c ty s h t q w r : OTerm α)
    (reports : LiftedReports body Γ (coords c ty s h) t q w r)
    (check : At4 body Γ (coords c ty s h) (rawCall raw) (suc z)) :
    Nonempty (Derivation body Γ (programGraph raw (suc z) ![c,ty,q,w,r])) :=
  compositionRecover raw ![.projection 0,.projection 1,atHop hopSource,atHop hopWitness,atHop hopRawTarget]
    (suc z) (coords c ty s h) ![c,ty,q,w,r] check
    (rawArgs c ty s h q w r reports.2.2.1 reports.2.2.2.1 reports.2.2.2.2)

private theorem leastArgs (p : Program 1) (c ty s h q : OTerm α)
    (hq : At4 body Γ (coords c ty s h) (atHop p) q) :
    ∀ i : Fin 3, At4 body Γ (coords c ty s h)
      ((![.projection 0,.projection 1,atHop p] : Fin 3 → Program 4) i) ((![c,ty,q] : Fin 3 → OTerm α) i) := by
  let xs := coords c ty s h
  intro i
  exact Fin.cases (projectionValue (0 : Fin 4) xs)
    (Fin.cases (projectionValue (1 : Fin 4) xs) (Fin.cases hq (fun u => Fin.elim0 u))) i

theorem leastIntro (least : Program 3) (p : Program 1) (c ty s h q value : OTerm α)
    (hq : At4 body Γ (coords c ty s h) (atHop p) q)
    (check : Nonempty (Derivation body Γ (programGraph least value ![c,ty,q]))) :
    At4 body Γ (coords c ty s h) (leastCall least p) value :=
  compositionValue least ![.projection 0,.projection 1,atHop p] value
    (coords c ty s h) ![c,ty,q] check (leastArgs p c ty s h q hq)

theorem leastRead (least : Program 3) (p : Program 1) (c ty s h q value : OTerm α)
    (hq : At4 body Γ (coords c ty s h) (atHop p) q)
    (check : At4 body Γ (coords c ty s h) (leastCall least p) value) :
    Nonempty (Derivation body Γ (programGraph least value ![c,ty,q])) :=
  compositionRecover least ![.projection 0,.projection 1,atHop p] value
    (coords c ty s h) ![c,ty,q] check (leastArgs p c ty s h q hq)

theorem matchIntro (p q : Program 4) (xs : Fin 4 → OTerm α) (v : OTerm α)
    (hp : At4 body Γ xs p v) (hq : At4 body Γ xs q v) :
    At4 body Γ xs (.composition equalityTest ![p,q]) (suc z) := by
  apply compositionValue equalityTest ![p,q] (suc z) xs ![v,v] (equalitySelf v)
  intro i
  exact Fin.cases hp (Fin.cases hq (fun k => Fin.elim0 k)) i

theorem matchRead (p q : Program 4) (c ty s h v : OTerm α)
    (good : At4 body Γ (coords c ty s h) (.composition equalityTest ![p,q]) (suc z))
    (expected : At4 body Γ (coords c ty s h) q v) :
    At4 body Γ (coords c ty s h) p v := by
  apply programCases p (coords c ty s h) _
  intro β j Δ actual hJ found
  rw [quadRename]
  rw [coordsRename] at found
  let xs := coords (c.relabel j) (ty.relabel j) (s.relabel j) (h.relabel j)
  let value := v.relabel j
  have good' := moveQuad j Δ hJ (.composition equalityTest ![p,q]) (suc z) c ty s h good
  simp only [sucRelabel,zRelabel] at good'
  have expected' := moveQuad j Δ hJ q v c ty s h expected
  have all := compositionRecover equalityTest ![p,q] (suc z) xs ![actual,value] good'
    (fun i => Fin.cases found (Fin.cases expected' (fun k => Fin.elim0 k)) i)
  exact outputTransport p actual value xs (equalityOfAcceptance actual value all) found

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallArgsProof
