module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem certificateFieldValue (p : Program 1) (value d e a certificate : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 p value certificate))) :
    Nonempty (Derivation body Gamma (graph4 (certificateField p) value d e a certificate)) :=
  unaryValue p (.projection 3) value certificate
    (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))) h
    (projectionValue 3 (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))))

theorem applicationAtFieldValue (p : Program 1) (field out d e a certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 p field certificate)))
    (ha : Nonempty (Derivation body Gamma (graph4 application out d e field a))) :
    Nonempty (Derivation body Gamma (graph4
      (.composition application ![.projection 0,.projection 1,certificateField p,.projection 2])
      out d e a certificate)) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))
  apply compositionValue application ![.projection 0,.projection 1,certificateField p,.projection 2]
    out xs (Fin.cons d (Fin.cons e (Fin.cons field (Fin.cons a Fin.elim0)))) ha
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (certificateFieldValue p field d e a certificate hp)
      (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q)))) i

theorem liftedStepValue (k' k d e a certificate : OTerm α)
    (hk : Nonempty (Derivation body Gamma (graph1 step k certificate)))
    (hs : Nonempty (Derivation body Gamma (graph1 stepLift k' k))) :
    Nonempty (Derivation body Gamma (graph4 liftedStep k' d e a certificate)) :=
  unaryValue stepLift (certificateField step) k' k
    (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))) hs
    (certificateFieldValue step k d e a certificate hk)

theorem edgeLiftComponents (d e a certificate s t k s' t' k' : OTerm α)
    (hp : Nonempty (Derivation body Gamma (liftPremises d e a certificate s t k s' t' k'))) :
    ∀ i : Fin 3, Nonempty (Derivation body Gamma
      (programGraph (![sourceApplication,targetApplication,liftedStep] i)
        (![s',t',k'] i)
        (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))))) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hd⟩ := edgeSelectors certificate s t k ⟨Derivation.conjunctionLeft hp⟩
  intro i
  exact Fin.cases
    (applicationAtFieldValue source s s' d e a certificate
      ⟨Derivation.conjunctionLeft hd⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hp)⟩)
    (Fin.cases
      (applicationAtFieldValue target t t' d e a certificate
        ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hd)⟩
        ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hp))⟩)
      (Fin.cases
        (liftedStepValue k' k d e a certificate
          ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hd)⟩
          ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hp))⟩)
        (fun q => Fin.elim0 q))) i

/-- Recover the exact transformed edge fields through the original composition
graph. Its existential intermediate codes are not replaced by semantic values. -/
theorem edgeLiftForward (d e a certificate s t k s' t' k' out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (liftPremises d e a certificate s t k s' t' k')))
    (hl : Nonempty (Derivation body Gamma (graph4 edgeLift out d e a certificate))) :
    Nonempty (Derivation body Gamma (graph3 edgeCode out s' t' k')) :=
  compositionRecover edgeCode ![sourceApplication,targetApplication,liftedStep] out
    (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0))))
    (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0))) hl
    (edgeLiftComponents d e a certificate s t k s' t' k' hp)

theorem edgeLiftBackward (d e a certificate s t k s' t' k' out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (liftPremises d e a certificate s t k s' t' k')))
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode out s' t' k'))) :
    Nonempty (Derivation body Gamma (graph4 edgeLift out d e a certificate)) :=
  compositionValue edgeCode ![sourceApplication,targetApplication,liftedStep] out
    (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0))))
    (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0))) he
    (edgeLiftComponents d e a certificate s t k s' t' k' hp)

theorem liftedEdgeSelectors (d e a certificate s t k s' t' k' out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (liftPremises d e a certificate s t k s' t' k')))
    (hl : Nonempty (Derivation body Gamma (graph4 edgeLift out d e a certificate))) :
    Nonempty (Derivation body Gamma (selectors out s' t' k')) :=
  edgeSelectors out s' t' k' (edgeLiftForward d e a certificate s t k s' t' k' out hp hl)

theorem guardedIff {A p q : Formula α}
    (hf : Nonempty (Derivation body [p,A] q))
    (hb : Nonempty (Derivation body [q,A] p)) :
    Nonempty (Derivation body [] (A.imp (p.iff q))) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalEdgeSelectors :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalEdgeSelectors := by
  intro body α certificate s t k
  obtain ⟨h⟩ := edgeSelectors (body := body) (Gamma := [graph3 edgeCode certificate s t k])
    certificate s t k ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalEdgeReconstruction :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalEdgeReconstruction := by
  intro body α certificate s t k
  obtain ⟨h⟩ := edgeReconstruction (body := body) (Gamma := [selectors certificate s t k])
    certificate s t k ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalApplicationPayloadEquation :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalApplicationPayloadEquation := by
  intro body α d e f a fp ap out
  apply guardedIff
  · exact applicationForward d e f a fp ap out
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact applicationBackward d e f a fp ap out
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalPackedApplicationEquation :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalPackedApplicationEquation := by
  intro body α d e f a ftype atype fp ap out
  apply guardedIff
  · exact applicationForward d e f a fp ap out
      (pairRight f ftype fp
        ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩)
      (pairRight a atype ap
        ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact applicationBackward d e f a fp ap out
      (pairRight f ftype fp
        ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩)
      (pairRight a atype ap
        ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalStepPrefixEquation :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalStepPrefixEquation := by
  intro body α certificate path payload prefixed out
  apply guardedIff
  · exact stepForward certificate path payload prefixed out
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact stepBackward certificate path payload prefixed out
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalStepPayloadPreserved :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalStepPayloadPreserved := by
  intro body α certificate path payload out
  let A := graph2 InternalPairing.pairing certificate path payload ⊓ graph1 stepLift out certificate
  obtain ⟨h⟩ := stepPayloadPreserved (body := body) (Gamma := [A]) certificate path payload out
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalStepDestruction :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalStepDestruction := by
  intro body α certificate path payload out prefixed
  let A := graph2 InternalPairing.pairing certificate path payload ⊓
    (graph1 stepLift out certificate ⊓ graph1 InternalUnpair.left prefixed out)
  obtain ⟨h⟩ := stepDestruction (body := body) (Gamma := [A]) certificate path payload out prefixed
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalEdgeLiftEquation :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalEdgeLiftEquation := by
  intro body α d e a certificate s t k s' t' k' out
  apply guardedIff
  · exact edgeLiftForward d e a certificate s t k s' t' k' out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact edgeLiftBackward d e a certificate s t k s' t' k' out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalLiftedEdgeSelectors :
    InternalApplicationCertificateConstructorsTargets.ActualOriginalLiftedEdgeSelectors := by
  intro body α d e a certificate s t k s' t' k' out
  let A := liftPremises d e a certificate s t k s' t' k' ⊓ graph4 edgeLift out d e a certificate
  obtain ⟨h⟩ := liftedEdgeSelectors (body := body) (Gamma := [A]) d e a certificate s t k s' t' k' out
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
