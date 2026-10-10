# Mathematical and formalization audit

Audit date: 2026-10-09. The starting revision was `6a78741`.

Subsequent extension, 2026-10-10: `PermutationLength`, `GramCycles`,
`MatrixDecay`, and `Asymptotics` add the cycle-count Gram formula and the uniform
bound `|Wg_d(σ)| ≤ C_r / d^(r+|σ|)` for all positive dimensions. See the
[current coefficient-bound API](README.md#bounds-on-weingarten-coefficients).
The build counts and scope assessments below record the original audit.

**Verdict:** the library proves the standard unitary Haar integration formula
in coordinates, in arbitrary dimension and order, including singular Gram
matrices. No mathematical gap, hidden spanning assumption, circular definition,
or weakening of the main integration statement was found. This conclusion rests
on inspecting the definitions and mathematical arguments as well as checking
Lean proofs. It does not assert a formalization of the irreducible decomposition
version of Schur–Weyl duality, character formulas, or other classical groups.

## Exact objects and statements

For a finite type `α`, `UnitaryGroup α` abbreviates Mathlib's complex unitary
matrix group. Words of length `k` are functions `Fin k → α`. The only typeclass
parameters of the main spanning and integration theorems are `Fintype α` and
`DecidableEq α`. Neither requires positive dimension, a dimension bound,
faithfulness, linear independence, or a representation-theory instance supplied
by the caller.

`invariantTensors α k` is defined by the actual fixed-vector condition

```lean
∀ U : UnitaryGroup α, mixedAction k U *ᵥ v = v
```

Here `mixedAction` has entries
`(∏ a, U (i a) (j a)) * star (∏ a, U (i' a) (j' a))`.
It is not defined as the span of diagrams. The theorem
`invariantTensors_le_range_diagramMatrix` states precisely

```lean
invariantTensors α k ≤
  LinearMap.range (diagramMatrix (ι := Fin k) (α := α)).mulVecLin
```

The reverse inclusion follows from `diagramMatrix_col_mem_invariantTensors`
and linearity. Thus these diagrams really span the fixed vectors.

Writing `Δσ(i,i') = [i' = i ∘ σ]`, the exact mathematical content of
`integral_unitary_weingarten` is

\[
\int_{U(\alpha)}\left(\prod_a U_{i_a j_a}\right)
 \overline{\left(\prod_a U_{i'_a j'_a}\right)}\,dU
=\sum_{\sigma,\tau\in S_k}
 \Delta_\sigma(i,i')W_{\sigma,\tau}\Delta_\tau(j,j').
\]

Both sides use separately defined objects: the left side is a Bochner integral;
the right side uses a spectral inverse of a combinatorial Gram matrix.
`mixedMoment` is an abbreviation for that integral, not for the proposed answer.
The earlier conditional reconstruction theorems retain explicit hypotheses,
but the final theorem discharges all of them internally.

`mixedMoment_eq_zero_of_ne` also proves vanishing for every unequal pair of
degrees. Its phase-invariance argument is stronger than the older odd-degree
result: a nonzero moment would force `z^p = z^q` for every scalar unitary phase.
The polynomial identity principle in dimension one extends that identity to
`z = 2`, contradicting `p ≠ q`. This supplies the remaining mixed monomials,
including unequal degrees with even total degree.

The coordinate convention agrees with the standard formula, up to choosing a
permutation or its inverse as the label of a diagram. The classical reference is
Collins and Śniady, [Integration with respect to the Haar measure on unitary,
orthogonal and symplectic group](https://arxiv.org/pdf/math-ph/0402073), Section 2.
The comparison here concerns its unitary integration formula, not its character
expansions or asymptotics.

## Haar normalization and analytic content

`haar α = Measure.haarMeasure ⊤` normalizes Haar measure on the whole compact
group. Its `IsProbabilityMeasure` instance proves mass one using
`Measure.haarMeasure_self`. Compactness is proved from closedness of the unitary
group and the entrywise bound `‖U i j‖ ≤ 1`. The measurable space is the Borel
space of the usual matrix topology. Left invariance comes from Haar measure;
right and inversion invariance are derived using uniqueness of invariant
probability measure.

Every mixed monomial is continuous and integrable. The formulas therefore do
not exploit Lean's default value for a nonintegrable Bochner integral.
`range_momentMatrix` identifies the range of actual Haar averaging with the
fixed vectors. Inversion invariance proves the moment matrix Hermitian, and
unitary contraction proves it fixes the diagram columns. These results precede
the spanning argument and do not assume the integration formula.

Dimension zero is handled consistently. At positive order there are no words
into an empty index type, so an entrywise assertion has no indices to which it
can be applied; the corresponding tensor space is zero. At order zero there is
one empty word, its product is one, and its integral is one, even for `U(0)`.
This natural degeneracy does not make the positive-dimensional theorem vacuous.

## Gram matrix and Moore–Penrose inverse

`pairing σ i j` is exactly the complex-valued indicator of `j = i ∘ σ`.
`diagramMatrix` has these vectors as columns, and `gramMatrix` is literally
`diagramMatrixᴴ * diagramMatrix`. The proved entry formula counts words with
`i ∘ σ = i ∘ τ`. Such words are constant on the cycles of `σ ∘ τ⁻¹`, so this
is the standard Gram matrix

\[
G_{\sigma,\tau}=d^{\#\mathrm{cycles}(\sigma\tau^{-1})}.
\]

There is no factorial or dimension normalization in the Gram definition.
The word-count statement is formalized; the conversion to cycle-count notation
in this paragraph is a mathematical identification, not a named library theorem.

`spectralInverse` conjugates the diagonal matrix of reciprocal real eigenvalues
by a unitary eigenvector matrix. Scalar inversion sends zero to zero. The
library proves all four equations

\[
GWG=G,\qquad WGW=W,\qquad (GW)^*=GW,\qquad (WG)^*=WG.
\]

These characterize the Moore–Penrose inverse, including in the singular case.
The audit adds `spectralInverse_eq_of_penrose`, a formal uniqueness theorem,
to make identification with independently calculated candidates explicit.
Eigenbasis choices consequently cannot change the matrix. In the stable range,
`weingartenMatrix_eq_inv` identifies it with the ordinary inverse. The integration
reconstruction needs only `GWG=G`; this is sufficient because the moment matrix
is Hermitian, fixes the diagrams, and has range in their span.

## Scrutiny of the Schur–Weyl argument

The central theorem `unitary_tensor_commutant` says that an arbitrary complex
matrix commuting with every `U` tensor power is a linear combination of
position-permutation matrices. Its proof has the following independently
checked steps.

1. **Polynomial identity principle.** For a Hermitian matrix, diagonalize it
   unitarily and substitute independent variables for its eigenvalues. When
   those variables lie on unit circles, the resulting matrix is unitary.
   Polynomial uniqueness on a product of infinite sets gives the identity for
   all eigenvalues. For an arbitrary matrix `M`, use the Hermitian matrices
   `H = M + M*` and `K = i(M - M*)`. The polynomial in two scalar variables
   vanishes for all real pairs, hence all complex pairs. Substitution of
   `(1/2, -i/2)` recovers `M`. This is valid for complex polynomials in entries;
   it does not incorrectly claim density for polynomials involving conjugates.
2. **The permutation commutant.** Commutation with position permutations makes
   matrix entries constant on simultaneous reindexing orbits of pairs of words.
   Equal multiplicities of paired letters characterize those orbits. The proof
   constructs bijections of letter fibers, so repeated letters are explicitly
   allowed. It never chooses an injective word in the singular regime.
3. **Spanning by arbitrary tensor powers.** Entries of `M` tensor powers are
   monomials in its matrix entries. Linear functionals annihilating all their
   evaluation vectors give a zero polynomial. Extracting each monomial
   coefficient shows that each multiplicity-fiber indicator lies in their span.
   Linear duality then recovers every matrix constant on these fibers. In
   particular, repeated exponents are not incorrectly treated as independent
   coordinates.
4. **Double commutant.** The generic helper `exists_smul_of_commutes` explicitly
   assumes semisimplicity. In the finite-group application that assumption is
   proved by Mathlib's Maschke instance for `ℂ[G]`, using `|G| ≠ 0` in `ℂ`.
   Jacobson density supplies an element agreeing on a finite complex basis;
   complex linearity extends equality to every vector. Neither the helper's
   application nor Maschke requires the group representation to be faithful.
5. **Return to invariant tensors.** Vectorization is proved to identify the
   mixed action with `X ↦ U^{⊗k} X (U^{⊗k})*`. Unitarity turns fixedness into
   commutation. The double-commutant result then supplies the diagram
   coefficients. Haar factorization and generalized-inverse reconstruction
   finish the integration proof.

The dependency order is acyclic. In particular, polynomial density and the
finite-group double commutant do not appeal to the desired integration formula.
The result is the commutant form of Schur–Weyl duality needed for integration;
it does not construct partitions, Schur functors, or irreducible summands.

## Explicit low-order calculations

The added `LowOrder` module proves the coefficients at orders zero and one,
the order-two Gram matrix, its stable-range inverse, its singular inverse for
dimension one, and the resulting order-two integrals. The examples import the
public entry point and derive the following formulas through the general theorem.

At `k = 0`, `G = W = [1]` and the integral is one. At `k = 1`, `G = [d]`,
`W = [1/d]` for `d > 0`, giving

\[
\int U_{ij}\overline{U_{i'j'}}\,dU
=\frac{[i=i'][j=j']}{d}.
\]

At `k = 2`, in permutation order `(e,s)` where `s = (12)`,

\[
G=\begin{pmatrix}d^2&d\\d&d^2\end{pmatrix},\qquad
W=\frac1{d^2-1}\begin{pmatrix}1&-1/d\\-1/d&1\end{pmatrix}
\quad(d\ge2).
\]

Put `Rσ = Δσ(i,i')` and `Cσ = Δσ(j,j')`. Substitution in the general theorem gives

\[
\int U_{i_1j_1}U_{i_2j_2}
 \overline{U_{i'_1j'_1}U_{i'_2j'_2}}\,dU
=\frac{R_eC_e+R_sC_s}{d^2-1}
 -\frac{R_eC_s+R_sC_e}{d(d^2-1)}.
\]

This identity is `integral_unitary_two`. In particular, setting all indices
equal gives `2/[d(d+1)]` for the fourth absolute moment. Setting both row words
to `(0,1)`, the column word to `(0,1)`, and its conjugate word to `(1,0)` gives
`-1/[d(d²-1)]`. The examples formally check the respective values `1/3` and
`-1/6` in `U(2)`; the displayed general scalar simplifications are ordinary
algebraic consequences of the formal four-term formula.

At **`d = 1, k = 2`**, the eigenvalues of `G` are `2,0`, so

\[
G=\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
G^+=\frac14\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]

`weingartenMatrix_one_two` proves each entry is `1/4` by checking the four
Penrose equations and invoking uniqueness. All deltas are one, so the general
integration theorem gives four terms of `1/4`, hence integral one
(`integral_one_two`). This agrees independently with the existing pointwise
`U(1)` argument. Substituting `d = 1` in the stable-range rational expression
would be invalid; the singular proof does not do that.

## Formal verification and reproducibility

The baseline `scripts/check.sh` passed. Lean reports only `propext`,
`Classical.choice`, and `Quot.sound` for the principal results, including
polynomial density, the double commutant, spanning, and the general integral.
Source inspection found no additional axioms, proof placeholders, unsafe proof
shortcuts, or disabled kernel checking. The audit extends the axiom reports to
the new uniqueness and low-order results.

Final verification passed `scripts/check.sh` after moving the previous project
build directory aside: all **22 project modules** compiled afresh, including
examples and the audit module, with no warnings or errors. All **31 axiom
reports** passed the standard-foundations allowlist. Dependency build artifacts
were reused from the checked cache; Mathlib itself was not rebuilt from source.
`git diff --check` also passed.

A separate consumer file outside the repository compiled using only
`import Weingarten`. Printing the fully explicit types of spanning, integration,
the unitary commutant, and the finite-group double commutant confirmed the
parameters described above. Probability-measure instance synthesis and the
singular `1/4` coefficient example also succeeded in that consumer.
A separate temporary Lake project then declared a local path dependency on
this package and built a module containing that public-import example
successfully. It used the same pinned toolchain and shared dependency cache.

The pinned compiler is Lean 4.28.0. All nine dependency checkouts match their
manifest revisions and have no tracked modifications; Mathlib is at
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The toolchain and manifest are unchanged.
The local `.lake/packages` is a pre-existing cache symlink and is not committed.
The toolchain launcher stalled in this environment; prepending the pinned
toolchain's `bin` directory to `PATH` allowed the build and checks to run.

## Reuse and Mathlib assessment

The library is suitable for downstream projects using the pinned toolchain:
it has an Apache 2.0 license, a Lake library target, a single public import,
focused modules, and unconditional theorem statements. Coefficients are
noncomputable spectral objects; the newly explicit low-order API helps with
small calculations, but this is not an executable general coefficient engine.

For eventual Mathlib contribution, the strongest separable additions are the
finite-group double commutant, polynomial identity principle, monomial span
lemma, and spectral generalized-inverse lemmas. They should be integrated into
the appropriate Mathlib namespaces and generalized where useful, followed by
the unitary commutant and integration application. The coordinate tensor model
is mathematically faithful, but an equivalence with Mathlib's abstract tensor
power representations would improve interoperability. The central-function,
cycle-count, and character APIs remain extensions rather than missing premises.

This repository is not yet a submission-ready Mathlib patch. Upstream work needs
the target revision's conventions, declaration documentation and file headers,
import/linter review, instance integration, and human mathematical and Lean
review. Mathlib's [contribution guidance](https://leanprover-community.github.io/contribute/index.html)
also requires contributors to understand and disclose AI-assisted work; its
[style guide](https://leanprover-community.github.io/contribute/style.html)
governs the final presentation. No upstream submission was made.

## Changes resulting from the audit

No central proof needed repair. Changes add an explicit uniqueness theorem,
low-order coefficient and integral checks, public API examples, and axiom reports.
Stale comments describing the spanning problem as still open were corrected.
These address verification coverage and documentation, without altering the
general theorem or imposing any new restriction on it.
