# Paper 16: two literal finite-type tower extractors

- Printed source: `16-persistent-marking-termination-ordering/sections/ordinals.tex:529–550`, with the wrapper `B₁ B₀ Next` at :563–568. `B₀` is `λ h. ordinalFix (λ α. (((It₀ α) h) Z))`. `B₁` is `λ h h₁. ordinalFix (λ α. ((((It₁ α) h) h₁) Z))`; in particular `Z` is an actual last application, not omitted or replaced by a different ordinal witness. `nativeNB` is left-associated `((B₁ B₀) ordinalNext)`.
- The typing leaf uses only original literal typed iterators and the existing native typing of `ordinalZero`, `ordinalFix`, and `ordinalNext`. It proves actual closed, ordinary, native, and well-typed codes for both extractors and their named composition.
- Separate beta leaf proves one literal native beta step and its genuine native strict edge for the printed application of `B₀` to an arbitrary closed (h). It neither executes nor assumes a collapse calibration.
- No mixed realization, Simmons helpfulness, `Γ₀` value, Veblen-hull `ψ_B`, cofinality, or numbered theorem is asserted.
