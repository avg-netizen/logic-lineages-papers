module

public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchDefinitions

/-! Exact partial-search targets for paper 03 `prop:certificate`.
A finite exhaustive check is independent of Carter. The search halts exactly
on JEP failure for valid finite codes, not on positive instances. No bound on
the first bad pair and no effectiveness of arbitrary mathematical bundles is
presupposed. The final equivalence requires transport via finite order isomorphisms. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.Targets
open FiniteCode CertificateSearch

def CertificateCodecFaithful : Prop :=
  (∀ U : Input, Encodable.decode (Encodable.encode U) = some U) ∧
  (∀ t : Certificate, Encodable.decode (Encodable.encode t) = some t)

def CertificateFamilyValidation : Prop :=
  ∀ U : Input, familyValidTest U = true ↔ FamilyValid U

def CertificateVerification : Prop :=
  ∀ (U : Input) (t : Certificate), verify U t = true ↔
    ∃ hU : FamilyValid U, ∃ hc : valid t.1 = true, ∃ hd : valid t.2.1 = true,
      t.2.2 = hostCodes (t.1.1 + t.2.1.1) ∧
      AvoidsForbidden (toFamily U hU) (toForest t.1 hc).Carrier ∧
      AvoidsForbidden (toFamily U hU) (toForest t.2.1 hd).Carrier ∧
      ¬ ∃ H : FiniteOrderForest, AvoidsForbidden (toFamily U hU) H.Carrier ∧
        Nonempty ((toForest t.1 hc).Carrier ↪o H.Carrier) ∧
        Nonempty ((toForest t.2.1 hd).Carrier ↪o H.Carrier)

def CertificateSearchOutputSound : Prop :=
  ∀ (U : Input) (t : Certificate), t ∈ search U → verify U t = true

def CertificateExistence : Prop :=
  ∀ (U : Input) (hU : FamilyValid U),
    (∃ t : Certificate, verify U t = true) ↔ ¬ HasJEP (toFamily U hU)

def CertificateSearchDomain : Prop :=
  ∀ (U : Input) (hU : FamilyValid U),
    (search U).Dom ↔ ¬ HasJEP (toFamily U hU)

def CertificateInvalidInputRejected : Prop :=
  ∀ U : Input, ¬ FamilyValid U → search U = Part.none

def CertificateFiniteOperationsPrimitiveRecursive : Prop :=
  Primrec familyValidTest ∧ Primrec₂ makeCertificate ∧
  Primrec₂ verify ∧ Primrec₂ atIndex

def CertificateSearchPartialRecursive : Prop := Partrec search

end LogicLineages.ModelsAlgebra.Forests.Targets
