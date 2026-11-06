# Frozen internal arithmetic supplier

These targets are auxiliary PA-calculus derivations for the positive signed-linear-combination proof of Bezout existence. They assert right distributivity, right-factor-preserving congruence, and the explicit coefficient identity

x*a+y*b=d+(z*a+w*b), a=q*d+r implies
(1+q*z)*a+(q*w)*b=r+((q*x)*a+(q*y)*b).

Quantification is over arbitrary object-language terms and arbitrary positive inductive body. No standard-model evaluation, semantic reflection, or Bezout premise is used. This is an arithmetic supplier, not whole Bezout existence or a numbered source promotion. The target hash records the pre-proof freeze. Targets must compile before proof authoring.
