# Weingarten calculus in Lean 4

**The general unitary Weingarten integration formula is proved**, for arbitrary
matrix dimension and moment order, including the singular Gram matrix regime
`d < k`. The previously missing permutation-tensor spanning theorem is now
unconditional. All unequal-degree mixed moments are also proved to vanish.

The project uses Lean **4.28.0** and Mathlib **v4.28.0**, with exact dependency
revisions recorded in `lake-manifest.json`. No `sorry`, `admit`, or additional
axioms are used.

## Build and use

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
scripts/check.sh
```

`lean-toolchain` selects the compiler. A fresh checkout fetches the pinned
dependencies. The verification script additionally requires Python 3.
The local development cache is not required by the committed configuration.

Import the public API with `import Weingarten`.
[`Weingarten/Examples.lean`](Weingarten/Examples.lean) contains compiled applications
in arbitrary positive dimension and order, an explicit `d = 2, k = 3`
singular-regime application, unequal-degree vanishing, and low-order results.
No spanning assumption is needed in any of these examples.
The [independent audit](AUDIT.md) checks the statement semantics, the Schur–Weyl
argument, normalization, logical dependencies, and explicit low-order values.

## Main theorem and conventions

Let `α` be a finite matrix-index type and let words be functions `Fin k → α`.
Define the permutation tensors and their Gram matrix by

\[
\Delta_\sigma(i,i')=[i'=i\circ\sigma],\qquad
A_{(i,i'),\sigma}=\Delta_\sigma(i,i'),\qquad G=A^*A.
\]

These are `pairing`, `diagramMatrix`, and `gramMatrix`. The coefficients
`W = weingartenMatrix (Fin k) α` are defined as the spectral Moore–Penrose inverse
of `G`: invert each nonzero eigenvalue and retain zero on the kernel. All four
Moore–Penrose equations are proved. In the stable range `k ≤ card α`,
`weingartenMatrix_eq_inv` identifies this with the ordinary inverse.

The main theorem **`Weingarten.integral_unitary_weingarten`** states

\[
\int_{U(\alpha)}\prod_{a=1}^{k}U_{i_a j_a}
       \overline{\prod_{a=1}^{k}U_{i'_a j'_a}}\,dU
 = \sum_{\sigma,\tau\in S_k}
   \Delta_\sigma(i,i')\,W_{\sigma,\tau}\,\Delta_\tau(j,j').
\]

This is an actual Bochner integral against normalized Haar measure on Mathlib's
complex unitary matrix group. Every integrand is proved continuous and
integrable. **There is no spanning, representation-theory, or dimension/order
hypothesis in the theorem.** It applies to every positive dimension `d` by
setting `α = Fin d`, for every `k`, including `d < k`. The definitions and theorem
also cover empty index types and order zero.

The result is also available as `mixedMoment_eq_weingarten` using the moment
abbreviation, and as `momentMatrix_eq_weingarten` in matrix form, `P = A W Aᴴ`.
For unequal degrees, `mixedMoment_eq_zero_of_ne` proves

\[
\int\prod_{a=1}^{p}U_{i_a j_a}
       \overline{\prod_{b=1}^{q}U_{i'_b j'_b}}\,dU=0
\qquad(p\ne q).
\]

The coefficient API uses two permutations and the Gram pseudoinverse. A central
function API in one relative permutation, cycle-count notation, and character
expansions are optional extensions, not assumptions needed for the proved formula.

## How the spanning gap is closed

1. **Haar projection.** `range_momentMatrix` identifies the range of the actual
   moment matrix with `invariantTensors`. Vectorization identifies invariance
   with commuting with all unitary tensor powers.
2. **Polynomial identity principle.** `polynomial_eq_zero_of_unitary` proves that
   complex polynomials in matrix entries vanishing on every unitary matrix
   vanish on every matrix. The proof uses the spectral theorem and polynomial
   uniqueness on products of circles for Hermitian matrices, then complexifies
   using two Hermitian matrices.
3. **Permutation commutant.** Equal multiplicities characterize words related by
   a permutation. Polynomial coefficient extraction and linear duality show
   that permutation-invariant matrices lie in the span of arbitrary matrix
   tensor powers. Repeated letters are allowed, with no stable-range assumption.
4. **Double commutant.** Maschke's theorem and Mathlib's Jacobson density theorem
   give the double-commutant theorem for any finite-group representation,
   including nonfaithful ones. Combining these results proves
   `unitary_tensor_commutant`, the dimension-free Schur–Weyl commutant theorem.
5. **Spanning and integration.** `invariantTensors_le_range_diagramMatrix` proves
   spanning. Consequently `momentMatrix_factorization` proves the exact
   formerly open statement:

   ```lean
   ∃ B, momentMatrix α k = diagramMatrix * B
   ```

   The existing generalized-inverse reconstruction theorem gives the full
   integral formula. Only `G W G = G` is required, so singular Gram matrices
   cause no loss of generality.

All steps are formal Lean proofs. The older conditional reconstruction lemmas
remain as reusable APIs, but the main theorems discharge their hypotheses internally.

## Organization

| Module | Content |
| --- | --- |
| `Haar` | Compact unitary group, normalized Haar measure, invariances |
| `Symmetries` | Permutation and diagonal-sign unitary matrices |
| `Moments` | Mixed integrals, integrability, odd moments, `U(1)` |
| `FirstMoment` | Order-one formula in arbitrary dimension |
| `Permutation` | Diagram tensors, Gram counting, stable-range independence |
| `Projection` | Reconstruction using a possibly singular Gram matrix |
| `GeneralizedInverse` | Spectral Moore–Penrose inverse and Weingarten matrix |
| `TensorPower` | General contractions and Hermitian moment matrix |
| `HaarProjection` | Representation action and exact range of Haar averaging |
| `DoubleCommutant` | Finite-group double commutant via Maschke and density |
| `UnitaryPolynomial` | Polynomial identity principle for unitary matrices |
| `WordWeight`, `PolynomialSpan` | Multiplicities and monomial-evaluation spans |
| `TensorMatrix` | Tensor matrices and position-permutation representation |
| `SchurWeyl` | Dimension-free unitary commutant theorem |
| `InvariantSpanning` | Unconditional spanning and Haar factorization |
| `Integration` | Full balanced Weingarten formula |
| `UnbalancedMoments` | Vanishing for every pair of unequal degrees |
| `LowOrder` | Explicit coefficients at orders zero, one, and two; singular `d = 1, k = 2` |
| `Examples`, `AxiomAudit` | Checked applications and logical dependency reports |

At order two, `integral_unitary_two` gives the explicit four-term formula for
`d ≥ 2`. In dimension one, `weingartenMatrix_one_two` proves every pseudoinverse
entry is `1/4`, and `integral_one_two` obtains integral one from the general
formula. `spectralInverse_eq_of_penrose` proves uniqueness from the four
Moore–Penrose equations.

## Verification

`scripts/check.sh` builds the library and examples, checks sources for proof
placeholders, and inspects transitive axiom reports for the principal results,
including Schur–Weyl duality, spanning, and the general integration theorem.
Only Lean's standard foundations `propext`, `Classical.choice`, and `Quot.sound`
are allowed; no `sorryAx` or additional axiom is permitted.
